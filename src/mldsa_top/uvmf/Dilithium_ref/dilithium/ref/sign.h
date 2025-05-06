#ifndef SIGN_H
#define SIGN_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"
#include "polyvec.h"
#include "poly.h"
#include <stdio.h>
#include <string.h>

// #define DEBUG 1

#define challenge DILITHIUM_NAMESPACE(challenge)
void challenge(poly *c, const uint8_t seed[SEEDBYTES]);

#define crypto_sign_keypair DILITHIUM_NAMESPACE(keypair)
int crypto_sign_keypair(uint8_t *pk, uint8_t *sk);

#define crypto_sign_signature DILITHIUM_NAMESPACE(signature)
int crypto_sign_signature(uint8_t *sig,
                          size_t *siglen,
                          const uint8_t *m,
                          const uint8_t *rnd,
                          size_t mlen,
                          const uint8_t *sk);

#define crypto_sign DILITHIUM_NAMESPACETOP
int crypto_sign(uint8_t *sm,
                size_t *smlen,
                const uint8_t *m,
                const uint8_t *rnd,
                size_t mlen,
                const uint8_t *sk);

#define crypto_sign_verify DILITHIUM_NAMESPACE(verify)
int crypto_sign_verify(const uint8_t *sig, size_t siglen,
                       const uint8_t *m, size_t mlen,
                       const uint8_t *pk);

#define crypto_sign_open DILITHIUM_NAMESPACE(open)
int crypto_sign_open(uint8_t *m, size_t *mlen,
                     const uint8_t *sm, size_t smlen,
                     const uint8_t *pk);

// Function to print an array of bytes in hex format
void print_hex(const char *label, const uint8_t *data, size_t len);


void print_polyk_from_hex(const char *label, uint8_t *data, size_t len);

// Function to print a polyvecl structure in hex format
void print_polyvecl(const char *label, const polyvecl *v);

// Function to print a polyvecl structure in hex format
void print_polyveck(const char *label, const polyveck *v) ;

// Function to print a polyvecl structure in hex format
void print_poly(const char *label, const poly *v);

int crypto_sign_keypair_with_external_seed(uint8_t *pk, uint8_t *sk, const uint8_t *external_seed);


#endif