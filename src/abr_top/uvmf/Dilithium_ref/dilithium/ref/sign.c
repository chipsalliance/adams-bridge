#include <stdint.h>
#include "params.h"
#include "sign.h"
#include "packing.h"
#include "polyvec.h"
#include "poly.h"
#include "randombytes.h"
#include "symmetric.h"
#include "fips202.h"
#include "reduce.h"

/*************************************************
* Name:        crypto_sign_keypair_with_external_seed
*
* Description: Generates public and private key using an external seed.
*
* Arguments:   - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*              - const uint8_t *external_seed: pointer to an array of 
*                                              SEEDBYTES number of uint8_t values
*
* Returns 0 (success)
**************************************************/

// Function to print an array of bytes in hex format
void print_hex(const char *label, const uint8_t *data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len; ++i) {
        printf("%02X", data[len-1-i]);
    }
    printf("\n");
}


void print_polyk_from_hex(const char *label, uint8_t *data, size_t len) {
  size_t cnt = len;
  printf("%s: ", label);
  for (size_t i = 0; i < K; ++i) {
      printf("vec[%zu]: ", i);
      for (size_t j = 0; j < N; ++j) {
          cnt--;
          printf("%02X ", data[cnt]);
      }
      printf("\n");
  }
}

// Function to print a polyvecl structure in hex format
void print_polyvecl(const char *label, const polyvecl *v) {
    printf("%s:\n", label);
    for (size_t i = 0; i < L; ++i) {
        printf("vec[%zu]: ", i);
        for (size_t j = 0; j < N; ++j) {
            // printf("%08X ", v->vec[i].coeffs[j]);
            printf("%08X ", caddq(v->vec[i].coeffs[j]));
        }
        printf("\n");
    }
}

// Function to print a polyvecl structure in hex format
void print_polyveck(const char *label, const polyveck *v) {
    printf("%s:\n", label);
    for (size_t i = 0; i < K; ++i) {
        printf("vec[%zu]: ", i);
        for (size_t j = 0; j < N; ++j) {
            // printf("%08X ", v->vec[i].coeffs[j]);
            printf("%08X ", caddq(v->vec[i].coeffs[j]));
        }
        printf("\n");
    }
}

// Function to print a polyvecl structure in hex format
void print_poly(const char *label, const poly *v) {
    printf("%s:\n", label);
    printf("vec[0]: ");
    for (size_t j = 0; j < N; ++j) {
      // printf("%08X ", v->vec[i].coeffs[j]);
      printf("%08X ", caddq(v->coeffs[j]));
    }
    printf("\n");
}

int crypto_sign_keypair_with_external_seed(uint8_t *pk, uint8_t *sk, const uint8_t *external_seed) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];
  // UPDATED because tr is 512-bit
  uint8_t tr[SEEDBYTES*2];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl mat[K];
  polyvecl s1, s1hat;
  polyveck s2, t1, t0;

  /* Copy external seed into seedbuf */
  memcpy(seedbuf, external_seed, SEEDBYTES);
  //===============================================================
  // ********************** FIPS Update ***************************
  // shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES);
  const uint8_t byte_K = K;  // K = 8
  const uint8_t byte_L = L;  // L = 7
  seedbuf[SEEDBYTES] = byte_K;
  seedbuf[SEEDBYTES + 1] = byte_L;
  shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES+2);
  //===============================================================
  rho = seedbuf;
  rhoprime = rho + SEEDBYTES;
  key = rhoprime + CRHBYTES;

  /* Expand matrix */
  polyvec_matrix_expand(mat, rho);

  /* Sample short vectors s1 and s2 */
  polyvecl_uniform_eta(&s1, rhoprime, 0);
  polyveck_uniform_eta(&s2, rhoprime, L);

  /* Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(&s1hat);
#if DEBUG == 1
    print_polyvecl("s1", &s1);
    print_polyvecl("s1hat", &s1hat);
#endif


  polyvec_matrix_pointwise_montgomery(&t1, mat, &s1hat);
  polyveck_reduce(&t1);
  polyveck_invntt_tomont(&t1);

  /* Add error vector s2 */
  polyveck_add(&t1, &t1, &s2);
#if DEBUG == 1
    print_polyveck("t", &t1);
#endif

  /* Extract t1 and write public key */
  polyveck_caddq(&t1);
  polyveck_power2round(&t1, &t0, &t1);
  pack_pk(pk, rho, &t1);

  /* Compute H(rho, t1) and write secret key */
  // UPDATED because tr is 512-bit
  // shake256(tr, SEEDBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  shake256(tr, 2*SEEDBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  pack_sk(sk, rho, tr, key, &t0, &s1, &s2);

#if DEBUG == 1
    print_polyveck("s2", &s2);
    print_polyveck("t0", &t0);
    print_polyveck("t1", &t1);
    print_hex("seedbuf", seedbuf, sizeof(seedbuf));
    print_hex("tr", tr, SEEDBYTES*2);
    print_hex("rho", rho, SEEDBYTES);
    print_hex("rhoprime", rhoprime, CRHBYTES);
    print_hex("key", key, SEEDBYTES);
#endif

  return 0;
}


/*************************************************
* Name:        crypto_sign_keypair
*
* Description: Generates public and private key.
*
* Arguments:   - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/
int crypto_sign_keypair(uint8_t *pk, uint8_t *sk) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];
  uint8_t tr[SEEDBYTES];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl mat[K];
  polyvecl s1, s1hat;
  polyveck s2, t1, t0;

  /* Get randomness for rho, rhoprime and key */
  randombytes(seedbuf, SEEDBYTES);
  shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES);
  rho = seedbuf;
  rhoprime = rho + SEEDBYTES;
  key = rhoprime + CRHBYTES;

  /* Expand matrix */
  polyvec_matrix_expand(mat, rho);

  /* Sample short vectors s1 and s2 */
  polyvecl_uniform_eta(&s1, rhoprime, 0);
  polyveck_uniform_eta(&s2, rhoprime, L);

  /* Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(&s1hat);
  polyvec_matrix_pointwise_montgomery(&t1, mat, &s1hat);
  polyveck_reduce(&t1);
  polyveck_invntt_tomont(&t1);

  /* Add error vector s2 */
  polyveck_add(&t1, &t1, &s2);

  /* Extract t1 and write public key */
  polyveck_caddq(&t1);
  polyveck_power2round(&t1, &t0, &t1);
  pack_pk(pk, rho, &t1);

  /* Compute H(rho, t1) and write secret key */
  shake256(tr, SEEDBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  pack_sk(sk, rho, tr, key, &t0, &s1, &s2);

  return 0;
}

/*************************************************
* Name:        crypto_sign_signature
*
* Description: Computes signature.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success)
**************************************************/
/*
* I need to add rnd input as an argument, which is signature randomness.
* This rnd is 256-bit, meaning that it should be const uint8_t *rnd.
* As a result, seedbuf requires should be extended 256 bit more.
* Since the result is written to the memory following rhoprime pointer,
* it should not be problem.
* shake256(rhoprime, CRHBYTES, key, SEEDBYTES + CRHBYTES) requires update
* because lenght changed and the initial pointer cannot cover rnd. It covers
* key and mu.
*/
int crypto_sign_signature(uint8_t *sig,
                          size_t *siglen,
                          const uint8_t *m,
                          const uint8_t *rnd,
                          size_t mlen,
                          const uint8_t *sk)
{
#if DEBUG == 1
  printf("\n======================================\n");
  printf("\n========Signature Generation==========\n");
  printf("\n======================================\n");
  int i;
#endif
  unsigned int n;
  // I need to update this part because tr is 512 bit not, 256-bit
  // uint8_t seedbuf[3*SEEDBYTES + 2*CRHBYTES];
  uint8_t seedbuf[3*SEEDBYTES + 2*CRHBYTES + SEEDBYTES*2];
  uint8_t *rho, *tr, *key, *mu, *rhoprime;
  uint16_t nonce = 0;
  polyvecl mat[K], s1, y, z;
  polyveck t0, s2, w1, w0, h;
  poly cp;
  keccak_state state;

  rho = seedbuf;
  tr = rho + SEEDBYTES;
  key = tr + SEEDBYTES*2;
  mu = key + SEEDBYTES;
  rhoprime = mu + CRHBYTES;
  unpack_sk(rho, tr, key, &t0, &s1, &s2, sk);
#if DEBUG == 1
  printf("\n========Unpacked secret key elements==========\n");
  print_hex("rho", rho, SEEDBYTES);
  print_hex("tr", tr, SEEDBYTES*2);
  print_hex("K", key, SEEDBYTES);
  print_hex("M_prime", m, ((unsigned int)mlen));
  print_polyvecl("s1", &s1);
  print_polyveck("s2", &s2);
  print_polyveck("t0", &t0);
#endif  

  /* Compute CRH(tr, msg) */
  shake256_init(&state);
  shake256_absorb(&state, tr, SEEDBYTES*2);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);
  

#ifdef DILITHIUM_RANDOMIZED_SIGNING
  randombytes(rhoprime, CRHBYTES);
#else
  // shake256(rhoprime, CRHBYTES, key, SEEDBYTES + CRHBYTES);
  // I updated this part because NIST hashes rnd with key and mu
  /* Hash key || rnd || mu to generate rhoprime */
  shake256_init(&state);
  shake256_absorb(&state, key, SEEDBYTES);           // Absorb key (32 bytes)
  shake256_absorb(&state, rnd, SEEDBYTES);           // Absorb rnd (32 bytes)
  shake256_absorb(&state, mu, CRHBYTES);             // Absorb mu (64 bytes)
  shake256_finalize(&state);
  shake256_squeeze(rhoprime, CRHBYTES, &state);      // Generate rhoprime
#endif

#if DEBUG == 1
  print_hex("mu", mu, SEEDBYTES*2);
  print_hex("rhoprime", rhoprime, 2*SEEDBYTES);
#endif

  /* Expand matrix and transform vectors */
  // TODO: I am not sure about this part, NIST spec and Dilithum spec uses
  //      rhoprime
  polyvec_matrix_expand(mat, rho);
#if DEBUG == 1
  for(i = 0; i < K; ++i){
    printf("            A[%d]            \n",i);
    print_polyvecl("A", &mat[i]);
  }
#endif

  polyvecl_ntt(&s1);
  polyveck_ntt(&s2);
  polyveck_ntt(&t0);

rej:
  /* Sample intermediate vector y */
  polyvecl_uniform_gamma1(&y, rhoprime, nonce++);
#if DEBUG == 1
  print_polyvecl("y", &y);
#endif

  /* Matrix-vector multiplication */
  z = y;
  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);
#if DEBUG == 1
  print_polyveck("Ay", &w1);
#endif

  /* Decompose w and call the random oracle */
  polyveck_caddq(&w1);
  polyveck_decompose(&w1, &w0, &w1);
#if DEBUG == 1
  print_polyveck("w0", &w0);
  print_polyveck("Decomposed w1", &w1);
#endif
  polyveck_pack_w1(sig, &w1);
#if DEBUG == 1
  print_polyk_from_hex("w1Encode", sig, K*POLYW1_PACKEDBYTES);
#endif

  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, sig, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  // shake256_squeeze(sig, SEEDBYTES, &state);
  // Updated because we use 512-bit output
  shake256_squeeze(sig, CRHBYTES, &state);
#if DEBUG == 1
  print_hex("~c1", sig, SEEDBYTES);
  print_hex("~c2", sig+SEEDBYTES, SEEDBYTES);
#endif
  poly_challenge(&cp, sig);
#if DEBUG == 1
  print_poly("c", &cp);
#endif
  poly_ntt(&cp);
#if DEBUG == 1
  print_poly("c_hat", &cp);
#endif

  /* Compute z, reject if it reveals secret */
  polyvecl_pointwise_poly_montgomery(&z, &cp, &s1);
  polyvecl_invntt_tomont(&z);
  polyvecl_add(&z, &z, &y);
  polyvecl_reduce(&z);
#if DEBUG == 1
  print_polyvecl("z", &z);
#endif
  if(polyvecl_chknorm(&z, GAMMA1 - BETA)){
#if DEBUG == 1
    printf("\n-----------------------------------\n");
    printf("Signature was Rejected due to z");
    printf("\n-----------------------------------\n");
#endif
    goto rej;
  }

  /* Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  polyveck_pointwise_poly_montgomery(&h, &cp, &s2);
  polyveck_invntt_tomont(&h);
  polyveck_sub(&w0, &w0, &h);
  polyveck_reduce(&w0);
#if DEBUG == 1
  print_polyveck("r0", &w0);
#endif
  if(polyveck_chknorm(&w0, GAMMA2 - BETA)){
#if DEBUG == 1
    printf("\n-----------------------------------\n");
    printf("Signature was Rejected due to r0");
    printf("\n-----------------------------------\n");
#endif
    goto rej;
  }

  /* Compute hints for w1 */
  polyveck_pointwise_poly_montgomery(&h, &cp, &t0);
  polyveck_invntt_tomont(&h);
  polyveck_reduce(&h);
#if DEBUG == 1
  print_polyveck("<<ct0>>", &h);
#endif
  if(polyveck_chknorm(&h, GAMMA2))
    goto rej;

  polyveck_add(&w0, &w0, &h);
  n = polyveck_make_hint(&h, &w0, &w1);
#if DEBUG == 1
  print_polyveck("after makehint h", &h);
#endif
  if(n > OMEGA)
    goto rej;

  /* Write signature */
  pack_sig(sig, sig, &z, &h);
  *siglen = CRYPTO_BYTES+SEEDBYTES;
  return 0;
}

/*************************************************
* Name:        crypto_sign
*
* Description: Compute signed message.
*
* Arguments:   - uint8_t *sm: pointer to output signed message (allocated
*                             array with CRYPTO_BYTES + mlen bytes),
*                             can be equal to m
*              - size_t *smlen: pointer to output length of signed
*                               message
*              - const uint8_t *m: pointer to message to be signed
*              - size_t mlen: length of message
*              - const uint8_t *sk: pointer to bit-packed secret key
*
* Returns 0 (success)
**************************************************/
int crypto_sign(uint8_t *sm,
                size_t *smlen,
                const uint8_t *m,
                const uint8_t *rnd,
                size_t mlen,
                const uint8_t *sk)
{
  size_t i;

  for(i = 0; i < mlen; ++i)
    sm[CRYPTO_BYTES +SEEDBYTES + mlen - 1 - i] = m[mlen - 1 - i];
  crypto_sign_signature(sm, smlen, sm + CRYPTO_BYTES+SEEDBYTES, rnd, mlen, sk);
  *smlen += mlen;
  return 0;
}

/*************************************************
* Name:        crypto_sign_verify
*
* Description: Verifies signature.
*
* Arguments:   - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_verify(const uint8_t *sig,
                       size_t siglen,
                       const uint8_t *m,
                       size_t mlen,
                       const uint8_t *pk)
{
  unsigned int i;
  uint8_t buf[K*POLYW1_PACKEDBYTES];
  uint8_t rho[SEEDBYTES];
  uint8_t mu[CRHBYTES];
  // uint8_t c[SEEDBYTES];
  // uint8_t c2[SEEDBYTES];
  uint8_t c[SEEDBYTES*2];
  uint8_t c2[SEEDBYTES*2];
  poly cp;
  polyvecl mat[K], z;
  polyveck t1, w1, h;
  keccak_state state;

  if(siglen != (CRYPTO_BYTES+SEEDBYTES))
    return -1;

  unpack_pk(rho, &t1, pk);
  if(unpack_sig(c, &z, &h, sig))
    return -1;
  if(polyvecl_chknorm(&z, GAMMA1 - BETA))
    return -1;

  /* Compute CRH(H(rho, t1), msg) */
  // shake256(mu, SEEDBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  // This one is tr
  shake256(mu, SEEDBYTES*2, pk, CRYPTO_PUBLICKEYBYTES);
#if DEBUG == 1
  print_hex("tr", mu, SEEDBYTES*2);
  print_hex("rho", rho, SEEDBYTES);
  print_hex("M_prime", m, ((unsigned int)mlen));
#endif
  // This for mu
  shake256_init(&state);
  // shake256_absorb(&state, mu, SEEDBYTES);
  shake256_absorb(&state, mu, SEEDBYTES*2); //tr
  // printf("the message lenght is %d\n",mlen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);
#if DEBUG == 1
  print_hex("mu", mu, SEEDBYTES*2);
  print_polyveck("h", &h);
  print_polyveck("t1", &t1);
  print_polyvecl("z", &z);
#endif


  /* Matrix-vector multiplication; compute Az - c2^dt1 */
  poly_challenge(&cp, c);
  polyvec_matrix_expand(mat, rho);

#if DEBUG == 1
  for(i = 0; i < K; ++i){
    printf("            A[%d]            \n",i);
    print_polyvecl("A", &mat[i]);
  }
#endif

  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);

  poly_ntt(&cp);
  polyveck_shiftl(&t1);
  polyveck_ntt(&t1);
  polyveck_pointwise_poly_montgomery(&t1, &cp, &t1);

  polyveck_sub(&w1, &w1, &t1);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Reconstruct w1 */
  polyveck_caddq(&w1);
#if DEBUG == 1
  print_polyveck("w1", &w1);
#endif
  polyveck_use_hint(&w1, &w1, &h);
  polyveck_pack_w1(buf, &w1);

#if DEBUG == 1
  print_hex("Decomposed w1", buf, K*POLYW1_PACKEDBYTES);
#endif

  /* Call random oracle and verify challenge */
  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, buf, K*POLYW1_PACKEDBYTES);
  shake256_finalize(&state);
  // shake256_squeeze(c2, SEEDBYTES, &state);
  shake256_squeeze(c2, SEEDBYTES*2, &state);
  for(i = 0; i < SEEDBYTES*2; ++i)
    if(c[i] != c2[i])
    {
      printf("Mismatch c[%d] = %d, while c[%d] = %d\n", i,c[i], i, c2[i]);
      return -1;
    }

  return 0;
}

/*************************************************
* Name:        crypto_sign_open
*
* Description: Verify signed message.
*
* Arguments:   - uint8_t *m: pointer to output message (allocated
*                            array with smlen bytes), can be equal to sm
*              - size_t *mlen: pointer to output length of message
*              - const uint8_t *sm: pointer to signed message
*              - size_t smlen: length of signed message
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signed message could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_open(uint8_t *m,
                     size_t *mlen,
                     const uint8_t *sm,
                     size_t smlen,
                     const uint8_t *pk)
{
  size_t i;

  if(smlen < CRYPTO_BYTES+SEEDBYTES)
    goto badsig;

  *mlen = smlen - (CRYPTO_BYTES+SEEDBYTES);
  // printf("the message lenght is %d and smlen (%d) - CRYPTO_BYTES+SEEDBYTES(%d) \n",*mlen, smlen, (CRYPTO_BYTES+SEEDBYTES));
  // int crypto_sign_verify(const uint8_t *sig,
  //                      size_t siglen,
  //                      const uint8_t *m,
  //                      size_t mlen,
  //                      const uint8_t *pk)
  if(crypto_sign_verify(sm, CRYPTO_BYTES+SEEDBYTES, sm + SEEDBYTES +CRYPTO_BYTES, *mlen, pk))
    goto badsig;
  else {
    /* All good, copy msg, return 0 */
    for(i = 0; i < *mlen; ++i)
      m[i] = sm[CRYPTO_BYTES+SEEDBYTES + i];
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = -1;
  for(i = 0; i < smlen; ++i)
    m[i] = 0;

  return -1;
}
