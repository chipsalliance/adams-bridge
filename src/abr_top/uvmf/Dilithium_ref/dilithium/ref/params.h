#ifndef PARAMS_H
#define PARAMS_H

#include "config.h"

/*
 * WARNING - THIS TREE IS NOT A VALID FIPS 204 VECTOR SOURCE FOR ML-DSA-44/65.
 *
 * This copy of the Dilithium reference has been locally modified for the
 * Adams-Bridge category-5 bring-up: tr and c~ are hardcoded to SEEDBYTES*2
 * (64 bytes) in sign.c for every value of DILITHIUM_MODE. FIPS 204 requires
 * lambda/4 bytes of c~, i.e. 32 bytes for ML-DSA-44, 48 bytes for ML-DSA-65
 * and 64 bytes for ML-DSA-87, and a 64-byte tr only for ML-DSA-87.
 *
 * Consequently DILITHIUM_MODE 2 and 3 built from this tree produce signatures
 * that are self-consistent but do NOT match FIPS 204, and must never be used
 * to generate or check known-answer vectors for ML-DSA-44 or ML-DSA-65.
 *
 * Use tools/mldsa_ref.py in the security-levels workspace instead - it tracks
 * lambda per parameter set. Fixing this tree means plumbing a CTILDEBYTES
 * parameter through sign.c, packing.c and the test harness.
 */
#if DILITHIUM_MODE == 2 || DILITHIUM_MODE == 3
#warning "Dilithium_ref is hardcoded to category-5 c~/tr sizing: MODE 2/3 output is NOT FIPS 204 compliant. See the warning block in params.h."
#endif

#define SEEDBYTES 32
#define CRHBYTES 64
#define N 256
#define Q 8380417
#define D 13
#define ROOT_OF_UNITY 1753

#if DILITHIUM_MODE == 2
#define K 4
#define L 4
#define ETA 2
#define TAU 39
#define BETA 78
#define GAMMA1 (1 << 17)
#define GAMMA2 ((Q-1)/88)
#define OMEGA 80

#elif DILITHIUM_MODE == 3
#define K 6
#define L 5
#define ETA 4
#define TAU 49
#define BETA 196
#define GAMMA1 (1 << 19)
#define GAMMA2 ((Q-1)/32)
#define OMEGA 55

#elif DILITHIUM_MODE == 5
#define K 8
#define L 7
#define ETA 2
#define TAU 60
#define BETA 120
#define GAMMA1 (1 << 19)
#define GAMMA2 ((Q-1)/32)
#define OMEGA 75

#endif

#define POLYT1_PACKEDBYTES  320
#define POLYT0_PACKEDBYTES  416
#define POLYVECH_PACKEDBYTES (OMEGA + K)

#if GAMMA1 == (1 << 17)
#define POLYZ_PACKEDBYTES   576
#elif GAMMA1 == (1 << 19)
#define POLYZ_PACKEDBYTES   640
#endif

#if GAMMA2 == (Q-1)/88
#define POLYW1_PACKEDBYTES  192
#elif GAMMA2 == (Q-1)/32
#define POLYW1_PACKEDBYTES  128
#endif

#if ETA == 2
#define POLYETA_PACKEDBYTES  96
#elif ETA == 4
#define POLYETA_PACKEDBYTES 128
#endif

#define CRYPTO_PUBLICKEYBYTES (SEEDBYTES + K*POLYT1_PACKEDBYTES)
// It is updated 3 became 4 in order to add one more SEEDBYTES for tr
#define CRYPTO_SECRETKEYBYTES (4*SEEDBYTES \
                               + L*POLYETA_PACKEDBYTES \
                               + K*POLYETA_PACKEDBYTES \
                               + K*POLYT0_PACKEDBYTES)
#define CRYPTO_BYTES (SEEDBYTES + L*POLYZ_PACKEDBYTES + POLYVECH_PACKEDBYTES)

#endif
