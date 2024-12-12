#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "../randombytes.h"
#include "../sign.h"

// #define MLEN 64
#define MLEN 65536
#define M_PRIME 1

#ifndef PREHASH
    #define PREHASH 0
#endif

#define PHM_SIZE 64 // 512 bits = 64 bytes

#if PREHASH == 1
    #define OID_SIZE 11 // Size of OID (in bytes)
    #define M_SIZE (2 + OID_SIZE + PHM_SIZE) // Size of final message M'
#else
    #define M_SIZE (2 + PHM_SIZE) // Size of final message M'
#endif

// Function prototypes
uint8_t hexCharToInt(char c);
uint8_t hexStringToByte(const char* str);
void writeFile(FILE* filename, uint8_t* data, size_t len);
void readFile(FILE* filename, uint8_t* data, size_t len);
void byteArrayToHexString(uint8_t* bytes, size_t len, char* str) ;
void byteToHexString(uint8_t byte, char* str);
void sizeTToByteArray(size_t value, uint8_t* array);
size_t byteArrayToSizeT(uint8_t* array);
void create_message_prime(uint8_t *PHM, uint8_t *M_prime);


const uint8_t rnd[32] = {0};

void create_message_prime(uint8_t *PHM, uint8_t *M_prime) {
    #if PREHASH == 1
        // pre-hash MLDSA
        // Step 1: Initialize M_prime with required sizes
        M_prime[0] = 0x01;
        M_prime[1] = 0x00;
        
        // Step 2: Add OID (0x0609608648016503040203)
        uint8_t OID[OID_SIZE] = {0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03};
        memcpy(M_prime + 2, OID, OID_SIZE);
        
        // Step 3: Add 512-bit (64-byte) PHM
        memcpy(M_prime + 2 + OID_SIZE, PHM, PHM_SIZE);

    #else
        // pure MLDSA
        // Step 1: Initialize M_prime with required sizes
        M_prime[0] = 0x00;
        M_prime[1] = 0x00;
            
        // Step 2: Add 512-bit (64-byte) PHM
        memcpy(M_prime + 2, PHM, PHM_SIZE);
    #endif
}


// Function to convert a hex character to its integer value
uint8_t hexCharToInt(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 0; // Invalid character
}

// Function to convert a hex string to uint8_t
uint8_t hexStringToByte(const char* str) {
    return (hexCharToInt(str[0]) << 4) | hexCharToInt(str[1]);
}
// Function to convert a byte array to a hex string
void byteArrayToHexString(uint8_t* bytes, size_t len, char* str) {
    static const char hexDigits[] = "0123456789ABCDEF";
    for (size_t i = 0; i < len; i++) {
        str[i * 2] = hexDigits[bytes[i] >> 4];
        str[i * 2 + 1] = hexDigits[bytes[i] & 0x0F];
    }
    str[len * 2] = '\0'; // Null-terminate the string
}

// Function to convert a byte to a two-character hex string
void byteToHexString(uint8_t byte, char* str) {
    static const char hexDigits[] = "0123456789ABCDEF";
    str[0] = hexDigits[byte >> 4];
    str[1] = hexDigits[byte & 0x0F];
    str[2] = '\0'; // Null-terminate the string
}

void writeFile(FILE *file, uint8_t* data, size_t len) {

    if (file == NULL) {
        perror("Failed to open file for writing");
        exit(EXIT_FAILURE);
    }
    for (size_t i = 0; i < len; i++) {
        fprintf(file, "%02X", data[i]);
    }
    fprintf(file, "\n");
}

// 0xABCD_10EF  value[31:0]
// {AB, CD, 10, EF}
void readFile(FILE *file , uint8_t* data, size_t len) {

    if (file == NULL) {
        perror("Failed to open file for reading");
        exit(EXIT_FAILURE);
    }

    char *line = NULL;
    size_t line_len = 0;
    size_t i = 0;

    while (i < len && getline(&line, &line_len, file) != -1) {
        size_t line_len_hex = strlen(line) / 2;
        for (size_t j = 0; j < line_len_hex && i < len; j++) {
            char buffer[3];
            buffer[0] = line[j * 2];
            buffer[1] = line[j * 2 + 1];
            buffer[2] = '\0';
            data[i++] = hexStringToByte(buffer);
        }
    }

    free(line);
}

// Function to convert size_t to a byte array (Little Endian)
void sizeTToByteArray(size_t value, uint8_t* array) {
    for (int i = 0; i < 4; i++) {
        array[3-i] = (value >> (i * 8)) & 0xFF;
    }
}

// Function to convert a byte array to size_t (Little Endian)
size_t byteArrayToSizeT(uint8_t* array) {
    size_t value = 0;
    for (int i = 0; i < 4; i++) {
        value = value<<8;
        value |= (size_t)array[i];
    }
    return value;
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <input_file.hex> <output_file.hex>\n", argv[0]);
        return -1;
    }

    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    uint8_t external_seed[SEEDBYTES];
    uint8_t m[MLEN + CRYPTO_BYTES] = {0};
    uint8_t m2[MLEN + CRYPTO_BYTES];
    uint8_t sm[MLEN + CRYPTO_BYTES+SEEDBYTES];
    size_t mlen;
    size_t smlen;
    int ret;

    FILE *input_file;
    FILE *output_file;

    input_file = fopen(argv[1], "r");
    if (!input_file) {
        perror("Error opening input file");
        return -1;
    }

    output_file = fopen(argv[2], "w");
    if (!output_file) {
        perror("Error opening output file");
        fclose(input_file);
        return -1;
    }

    uint8_t cmd;
    readFile(input_file, &cmd, 1);

    switch (cmd) {
        case 0: // keygen
            {
                readFile(input_file, external_seed, SEEDBYTES);
                char seed_hex[2 * SEEDBYTES + 1];
                byteArrayToHexString(external_seed, SEEDBYTES, seed_hex);
                printf("seed_hex is %s\n", seed_hex);

                crypto_sign_keypair_with_external_seed(pk, sk, external_seed);
                writeFile(output_file, &cmd, 1);
                writeFile(output_file, pk, CRYPTO_PUBLICKEYBYTES);
                writeFile(output_file, sk, CRYPTO_SECRETKEYBYTES);

                char command_hex[2+1];
                byteToHexString(cmd, command_hex);
                printf("comand is %s\n", command_hex);
                char pk_hex[2 * CRYPTO_PUBLICKEYBYTES + 1];
                byteArrayToHexString(pk, CRYPTO_PUBLICKEYBYTES, pk_hex);
                printf("public key is %s\n", pk_hex);
                char sk_hex[2 * (CRYPTO_SECRETKEYBYTES) + 1];
                byteArrayToHexString(sk, CRYPTO_SECRETKEYBYTES, sk_hex);
                printf("secret key is %s\n", sk_hex);
            }
            break;

        case 1: // signing
            {
#if M_PRIME == 1
                uint8_t PHM[PHM_SIZE]; // This should contain the SHA-512 hash of the message
                readFile(input_file, PHM, PHM_SIZE);
                create_message_prime(PHM, m);
                mlen = M_SIZE;
                printf("message lenght is %04X\n", (unsigned int)mlen);
#else
                uint8_t mlen_array[4];
                readFile(input_file, mlen_array, 4);
                mlen = byteArrayToSizeT(mlen_array);
                printf("message lenght is %04X\n", (unsigned int)mlen);
                readFile(input_file, m, mlen);
#endif
                readFile(input_file, sk, CRYPTO_SECRETKEYBYTES);

                crypto_sign(sm, &smlen, m, rnd, mlen, sk);

                writeFile(output_file, &cmd, 1);
                fprintf(output_file, "%08X\n", (unsigned int)smlen);
                writeFile(output_file, sm, (smlen-mlen));

                char command_hex[2+1];
                byteToHexString(cmd, command_hex);
                printf("comand is %s\n", command_hex);
                printf("signature lenght is %X\n", (unsigned int)smlen);
                char sm_hex[2*(CRYPTO_BYTES+SEEDBYTES)];
                byteArrayToHexString(sm, (smlen-mlen), sm_hex);
                printf("signature is %s\n", sm_hex);
            }
            break;

        case 2: // verification
            {
#if M_PRIME == 1
                smlen = SEEDBYTES + CRYPTO_BYTES + M_SIZE;
                printf("signature lenght is %04X\n", (unsigned int)smlen);

                
                readFile(input_file, sm, SEEDBYTES +CRYPTO_BYTES+PHM_SIZE);
                readFile(input_file, pk, CRYPTO_PUBLICKEYBYTES);

                uint8_t PHM[PHM_SIZE]; // This should contain the SHA-512 hash of the message
                memcpy(PHM, sm + SEEDBYTES +CRYPTO_BYTES, PHM_SIZE);
                create_message_prime(PHM, sm + SEEDBYTES +CRYPTO_BYTES);
                mlen = M_SIZE;
                printf("message lenght is %04X\n", (unsigned int)mlen);
#else
                uint8_t smlen_array[4];
                readFile(input_file, smlen_array, 4);
                smlen = byteArrayToSizeT(smlen_array);
                printf("signature lenght is %04X\n", (unsigned int)smlen);

                
                readFile(input_file, sm, smlen);
                readFile(input_file, pk, CRYPTO_PUBLICKEYBYTES);
#endif

                ret = crypto_sign_open(m2, &mlen, sm, smlen, pk);

                writeFile(output_file, &cmd, 1);
                fprintf(output_file, "%d\n", ret);
                if (!ret)
                    writeFile(output_file, sm, SEEDBYTES*2);
                else
                    fprintf(output_file, "0\n");

                char command_hex[2+1];
                byteToHexString(cmd, command_hex);
                printf("comand is %s\n", command_hex);
                printf("message lenght is %X\n", (unsigned int)mlen);
                printf("result is %d\n", ret);

            }
            break;

        default:
            fprintf(stderr, "Invalid command\n");
            fclose(input_file);
            fclose(output_file);
            return -1;
    }

    fclose(input_file);
    fclose(output_file);

    

    return 0;
}

