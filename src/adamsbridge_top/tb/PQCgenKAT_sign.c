//
//  PQCgenKAT_sign.c
//
//  Created by Bassham, Lawrence E (Fed) on 8/29/17.
//  Copyright © 2017 Bassham, Lawrence E (Fed). All rights reserved.
//

//======================================================================
//
// PQCgenKAT_sign.c
// --------
// this file has dependencies to pq-crystals dilithium libraries, and needs to be placed 
// in dilithium/ref directory of dilithium to be run.
// Note: if generating the .exe in unix, add -std=c99 to the end of CFLAGS and
// NISTFLAGS variable assignment at the top of the Makefile
//======================================================================

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include "rng.h"
#include "sign.h"
#include "fips202.h"

#define	MAX_MARKER_LEN      50

#define KAT_SUCCESS          0
#define KAT_FILE_OPEN_ERROR -1
#define KAT_DATA_ERROR      -3
#define KAT_CRYPTO_FAILURE  -4

int	FindMarker(FILE *infile, const char *marker);
int	ReadHex(FILE *infile, unsigned char *a, int Length, char *str);
void	fprintBstr(FILE *fp, char *s, unsigned char *a, unsigned long long l);

int
main()
{
    char                fn_req[32], fn_rsp[32], fn_hex[32];
    FILE                *fp_req, *fp_rsp, *fp_hex;
    uint8_t             seed[32], hash[64], IV[64]; // randlen[1];
    uint8_t             msg[3300];
    uint8_t             entropy_input[48];
    uint8_t             *m, *sm, *m1;
    size_t              mlen, smlen, mlen1, hlen;
    int                 count;
    int                 done;
    uint8_t             pk[CRYPTO_PUBLICKEYBYTES], sk[CRYPTO_SECRETKEYBYTES];
    int                 ret_val;
    time_t              now;

    now = time(0);
    unsigned char * timestr = ctime(&now);
    uint64_t * timeint = (uint64_t *) timestr;
    //printf("Time now = %s\nTime now in int = %u\n", timestr,timeint);
    //printf("crypto: pk bytes = %d, sk bytes = %d", CRYPTO_PUBLICKEYBYTES, CRYPTO_SECRETKEYBYTES);

    // Create the REQUEST file
    sprintf(fn_req, "PQCsignKAT_%.16s.req", CRYPTO_ALGNAME);
    if ( (fp_req = fopen(fn_req, "w")) == NULL ) {
        printf("Couldn't open <%s> for write\n", fn_req);
        return KAT_FILE_OPEN_ERROR;
    }
    sprintf(fn_rsp, "PQCsignKAT_%.16s.rsp", CRYPTO_ALGNAME);
    if ( (fp_rsp = fopen(fn_rsp, "w")) == NULL ) {
        printf("Couldn't open <%s> for write\n", fn_rsp);
        return KAT_FILE_OPEN_ERROR;
    }
    sprintf(fn_hex, "PQCsignKAT_mldsa87.hex");
    if ( (fp_hex = fopen(fn_hex, "w")) == NULL ) {
        printf("Couldn't open <%s> for write\n", fn_hex);
        return KAT_FILE_OPEN_ERROR;
    }

    for (int i=0; i<48; i++)
        entropy_input[i] = i;

    // randombytes_init(entropy_input, NULL, 256);
    randombytes_init(timestr, NULL, 256);
    for (int i=0; i<1; i++) {
        fprintf(fp_req, "count = %d\n", i);
        randombytes(seed, 32);
        fprintBstr(fp_req, "seed = ", seed, 32);
        fprintBstr(fp_hex, "seed = ", seed, 32);
        mlen = 3300; //33*(i+1);
        // randombytes(randlen, 1);
        // printf("randlen = %u\n", randlen);
        // fprintBstr(fp_req, "randlen = ", randlen, 1);
        // mlen = (size_t) randlen;
        fprintf(fp_req, "mlen = %lu\n", mlen);
        randombytes(msg, mlen);
        fprintBstr(fp_req, "msg = ", msg, mlen);
        sha3_512(hash, msg, mlen);
        hlen = 64;
        fprintf(fp_req, "hlen = %lu\n", hlen);
        fprintBstr(fp_req, "hash = ", hash, hlen);
        fprintBstr(fp_hex, "hash = ", hash, hlen);
        fprintf(fp_req, "pk =\n");
        fprintf(fp_req, "sk =\n");
        fprintf(fp_req, "smlen =\n");
        fprintf(fp_req, "sm =\n\n");
        randombytes(IV, 64);
        fprintBstr(fp_req, "IV = ", IV, 64);
        fprintBstr(fp_hex, "IV = ", IV, 64);
    }
    fclose(fp_req);

    //Create the RESPONSE file based on what's in the REQUEST file
    if ( (fp_req = fopen(fn_req, "r")) == NULL ) {
        printf("Couldn't open <%s> for read\n", fn_req);
        return KAT_FILE_OPEN_ERROR;
    }

    fprintf(fp_rsp, "# %s\n\n", CRYPTO_ALGNAME);
    done = 0;
    do {
        if ( FindMarker(fp_req, "count = ") )
            fscanf(fp_req, "%d", &count);
        else {
            done = 1;
            break;
        }
        fprintf(fp_rsp, "count = %d\n", count);

        if ( !ReadHex(fp_req, seed, 32, "seed = ") ) {
            printf("ERROR: unable to read 'seed' from <%s>\n", fn_req);
            return KAT_DATA_ERROR;
        }
        fprintBstr(fp_rsp, "seed = ", seed, 32);

        randombytes_init(seed, NULL, 256);

        // if ( FindMarker(fp_req, "mlen = ") )
        //     fscanf(fp_req, "%lu", &mlen);
        // else {
        //     printf("ERROR: unable to read 'mlen' from <%s>\n", fn_req);
        //     return KAT_DATA_ERROR;
        // }
        // fprintf(fp_rsp, "mlen = %lu\n", mlen);

        if ( FindMarker(fp_req, "hlen = ") )
            fscanf(fp_req, "%lu", &hlen);
        else {
            printf("ERROR: unable to read 'hlen' from <%s>\n", fn_req);
            return KAT_DATA_ERROR;
        }
        fprintf(fp_rsp, "hlen = %lu\n", hlen);

        // m = (uint8_t *)calloc(mlen, sizeof(uint8_t));
        // m1 = (uint8_t *)calloc(mlen+CRYPTO_BYTES, sizeof(uint8_t));
        // sm = (uint8_t *)calloc(mlen+CRYPTO_BYTES, sizeof(uint8_t));

        m = (uint8_t *)calloc(hlen, sizeof(uint8_t));
        m1 = (uint8_t *)calloc(hlen+CRYPTO_BYTES, sizeof(uint8_t));
        sm = (uint8_t *)calloc(hlen+CRYPTO_BYTES, sizeof(uint8_t));

        // if ( !ReadHex(fp_req, m, (int)mlen, "msg = ") ) {
        //     printf("ERROR: unable to read 'msg' from <%s>\n", fn_req);
        //     return KAT_DATA_ERROR;
        // }
        // fprintBstr(fp_rsp, "msg = ", m, mlen);

        if ( !ReadHex(fp_req, m, (int)hlen, "hash = ") ) {
            printf("ERROR: unable to read 'hash' from <%s>\n", fn_req);
            return KAT_DATA_ERROR;
        }
        fprintBstr(fp_rsp, "hash = ", hash, hlen);

        // Generate the public/private keypair
        if ( (ret_val = crypto_sign_keypair(pk, sk)) != 0) {
            printf("crypto_sign_keypair returned <%d>\n", ret_val);
            return KAT_CRYPTO_FAILURE;
        }
        fprintBstr(fp_rsp, "pk = ", pk, CRYPTO_PUBLICKEYBYTES);
        fprintBstr(fp_hex, "pk = ", pk, CRYPTO_PUBLICKEYBYTES);
        fprintBstr(fp_rsp, "sk = ", sk, CRYPTO_SECRETKEYBYTES);
        fprintBstr(fp_hex, "sk = ", sk, CRYPTO_SECRETKEYBYTES);

        // if ( (ret_val = crypto_sign(sm, &smlen, m, mlen, sk)) != 0) {
        if ( (ret_val = crypto_sign(sm, &smlen, m, hlen, sk)) != 0) {
            printf("crypto_sign returned <%d>\n", ret_val);
            return KAT_CRYPTO_FAILURE;
        }
        fprintf(fp_rsp, "smlen = %lu\n", smlen);
        fprintBstr(fp_rsp, "sm = ", sm, smlen);
        fprintBstr(fp_hex, "sm = ", sm, smlen);
        fprintBstr(fp_rsp, "IV = ", IV, 64);
        fprintf(fp_rsp, "\n");

        if ( (ret_val = crypto_sign_open(m1, &mlen1, sm, smlen, pk)) != 0) {
            printf("crypto_sign_open returned <%d>\n", ret_val);
            return KAT_CRYPTO_FAILURE;
        }

        // if ( mlen != mlen1 ) {
        //     printf("crypto_sign_open returned bad 'mlen': Got <%lu>, expected <%lu>\n", mlen1, mlen);
        //     return KAT_CRYPTO_FAILURE;
        // }

        // if ( memcmp(m, m1, mlen) ) {
        //     printf("crypto_sign_open returned bad 'm' value\n");
        //     return KAT_CRYPTO_FAILURE;
        // }

        if ( hlen != mlen1 ) {
            printf("crypto_sign_open returned bad 'hlen': Got <%lu>, expected <%lu>\n", mlen1, hlen);
            return KAT_CRYPTO_FAILURE;
        }

        if ( memcmp(m, m1, hlen) ) {
            printf("crypto_sign_open returned bad 'm' value\n");
            return KAT_CRYPTO_FAILURE;
        }

        free(m);
        free(m1);
        free(sm);

    } while ( !done );

    fclose(fp_req);
    fclose(fp_rsp);

    return KAT_SUCCESS;
}

//
// ALLOW TO READ HEXADECIMAL ENTRY (KEYS, DATA, TEXT, etc.)
//
int
FindMarker(FILE *infile, const char *marker)
{
	char	line[MAX_MARKER_LEN];
	int	i, len;
	int	curr_line;

	len = (int)strlen(marker);
	if ( len > MAX_MARKER_LEN-1 )
	    len = MAX_MARKER_LEN-1;

	for ( i=0; i<len; i++ )
	  {
	    curr_line = fgetc(infile);
	    line[i] = curr_line;
	    if (curr_line == EOF )
	      return 0;
	  }
	line[len] = '\0';

	while ( 1 ) {
		if ( !strncmp(line, marker, len) )
			return 1;

		for ( i=0; i<len-1; i++ )
			line[i] = line[i+1];
		curr_line = fgetc(infile);
		line[len-1] = curr_line;
		if (curr_line == EOF )
			return 0;
		line[len] = '\0';
	}

	// shouldn't get here
	return 0;
}

//
// ALLOW TO READ HEXADECIMAL ENTRY (KEYS, DATA, TEXT, etc.)
//
int
ReadHex(FILE *infile, unsigned char *a, int Length, char *str)
{
	int		i, ch, started;
	unsigned char	ich;

	if ( Length == 0 ) {
		a[0] = 0x00;
		return 1;
	}
	memset(a, 0x00, Length);
	started = 0;
	if ( FindMarker(infile, str) )
		while ( (ch = fgetc(infile)) != EOF ) {
			if ( !isxdigit(ch) ) {
				if ( !started ) {
					if ( ch == '\n' )
						break;
					else
						continue;
				}
				else
					break;
			}
			started = 1;
			if ( (ch >= '0') && (ch <= '9') )
				ich = ch - '0';
			else if ( (ch >= 'A') && (ch <= 'F') )
				ich = ch - 'A' + 10;
			else if ( (ch >= 'a') && (ch <= 'f') )
				ich = ch - 'a' + 10;
			else // shouldn't ever get here
				ich = 0;

			for ( i=0; i<Length-1; i++ )
				a[i] = (a[i] << 4) | (a[i+1] >> 4);
			a[Length-1] = (a[Length-1] << 4) | ich;
		}
	else
		return 0;

	return 1;
}

void
fprintBstr(FILE *fp, char *s, unsigned char *a, unsigned long long l)
{
	unsigned long long  i;

	fprintf(fp, "%s", s);

	for ( i=0; i<l; i++ )
		fprintf(fp, "%02X", a[i]);

	if ( l == 0 )
		fprintf(fp, "00");

	fprintf(fp, "\n");
}


