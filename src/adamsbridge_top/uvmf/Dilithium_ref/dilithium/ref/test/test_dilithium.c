#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "../randombytes.h"
#include "../sign.h"

#define MLEN 64
// Function prototypes
uint8_t hexCharToInt(char c);
uint8_t hexStringToByte(const char* str);
void writeFile(FILE* filename, uint8_t* data, size_t len);
void readFile(FILE* filename, uint8_t* data, size_t len);
void byteArrayToHexString(uint8_t* bytes, size_t len, char* str) ;
void byteToHexString(uint8_t byte, char* str);
void sizeTToByteArray(size_t value, uint8_t* array);
size_t byteArrayToSizeT(uint8_t* array);


const uint8_t rnd[32] = {0};


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
    uint8_t sk[CRYPTO_SECRETKEYBYTES+SEEDBYTES];
    uint8_t external_seed[SEEDBYTES];
    uint8_t m[MLEN + CRYPTO_BYTES] = {0};
    uint8_t m2[MLEN + CRYPTO_BYTES];
    uint8_t sm[MLEN + CRYPTO_BYTES+SEEDBYTES];
    size_t mlen = MLEN;
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
                writeFile(output_file, sk, CRYPTO_SECRETKEYBYTES+SEEDBYTES);

                char command_hex[2+1];
                byteToHexString(cmd, command_hex);
                printf("comand is %s\n", command_hex);
                char pk_hex[2 * CRYPTO_PUBLICKEYBYTES + 1];
                byteArrayToHexString(pk, CRYPTO_PUBLICKEYBYTES, pk_hex);
                printf("public key is %s\n", pk_hex);
                char sk_hex[2 * (CRYPTO_SECRETKEYBYTES+SEEDBYTES) + 1];
                byteArrayToHexString(sk, CRYPTO_SECRETKEYBYTES+SEEDBYTES, sk_hex);
                printf("secret key is %s\n", sk_hex);
            }
            break;

        case 1: // signing
            {
                readFile(input_file, m, MLEN);
                readFile(input_file, sk, CRYPTO_SECRETKEYBYTES+SEEDBYTES);

                crypto_sign(sm, &smlen, m, rnd, MLEN, sk);

                writeFile(output_file, &cmd, 1);
                fprintf(output_file, "%08X\n", (unsigned int)smlen);
                writeFile(output_file, sm, smlen);

                char command_hex[2+1];
                byteToHexString(cmd, command_hex);
                printf("comand is %s\n", command_hex);
                printf("signature lenght is %X\n", (unsigned int)smlen);
                char sm_hex[2*(MLEN + CRYPTO_BYTES+SEEDBYTES)];
                byteArrayToHexString(sm, smlen, sm_hex);
                printf("signature is %s\n", sm_hex);
            }
            break;

        case 2: // verification
            {
                uint8_t smlen_array[4];
                readFile(input_file, smlen_array, 4);
                smlen = byteArrayToSizeT(smlen_array);
                printf("signature lenght is %04X\n", (unsigned int)smlen);

                
                readFile(input_file, sm, smlen);
                readFile(input_file, pk, CRYPTO_PUBLICKEYBYTES);

                ret = crypto_sign_open(m2, &mlen, sm, smlen, pk);

                writeFile(output_file, &cmd, 1);
                fprintf(output_file, "%d\n", ret);
                if (!ret)
                    writeFile(output_file, m2, mlen);
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



// #include <stddef.h>
// #include <stdint.h>
// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>
// #include "../randombytes.h"
// #include "../sign.h"

// #define MLEN 59

// void hex_to_bytes(const char* hex, uint8_t* bytes, size_t len);
// void bytes_to_hex(const uint8_t* bytes, char* hex, size_t len);
// void read_exactly(FILE* file, char* buffer, size_t len);

// void hex_to_bytes(const char* hex, uint8_t* bytes, size_t len) {
//     for (size_t i = 0; i < len; i++) {
//         sscanf(hex + 2 * i, "%2hhx", &bytes[i]);
//     }
// }

// void bytes_to_hex(const uint8_t* bytes, char* hex, size_t len) {
//     for (size_t i = 0; i < len; i++) {
//         sprintf(hex + 2 * i, "%02x", bytes[i]);
//     }
//     hex[2 * len] = '\0';
// }

// void read_exactly(FILE* file, char* buffer, size_t len) {
//     size_t total_read = 0;
//     while (total_read < len) {
//         size_t to_read = len - total_read;
//         size_t n = fread(buffer + total_read, 1, to_read, file);
//         if (n == 0) {
//             break;
//         }
//         total_read += n;
//     }
//     buffer[len] = '\0'; // Null terminate the string
//     int ch;
//     while ((ch = fgetc(file)) != '\n' && ch != EOF); // Discard the rest of the line
// }

// int main(int argc, char *argv[]) {
//     if (argc != 2) {
//         fprintf(stderr, "Usage: %s <seed_file.hex>\n", argv[0]);
//         return -1;
//     }

//     FILE *seed_file = fopen(argv[1], "r");
//     if (!seed_file) {
//         perror("Error opening seed file");
//         return -1;
//     }

//     char seed_hex[2 * SEEDBYTES + 1];
//     read_exactly(seed_file, seed_hex, 2 * SEEDBYTES);
//     fclose(seed_file);

//     uint8_t pk[CRYPTO_PUBLICKEYBYTES];
//     uint8_t sk[CRYPTO_SECRETKEYBYTES];
//     uint8_t external_seed[SEEDBYTES];
//     uint8_t m[MLEN + CRYPTO_BYTES] = {0};
//     uint8_t m2[MLEN + CRYPTO_BYTES];
//     uint8_t sm[MLEN + CRYPTO_BYTES];
//     size_t mlen = MLEN;
//     size_t smlen;
//     int ret;

//     hex_to_bytes(seed_hex, external_seed, SEEDBYTES);

//     // Step 1: Generate keypair
//     crypto_sign_keypair_with_external_seed(pk, sk, external_seed);

//     FILE *pk_file = fopen("public_key.hex", "w");
//     if (!pk_file) {
//         perror("Error opening public key file");
//         return -1;
//     }
//     char pk_hex[2 * CRYPTO_PUBLICKEYBYTES + 1];
//     bytes_to_hex(pk, pk_hex, CRYPTO_PUBLICKEYBYTES);
//     fprintf(pk_file, "%s\n", pk_hex);
//     fclose(pk_file);

//     FILE *sk_file = fopen("secret_key.hex", "w");
//     if (!sk_file) {
//         perror("Error opening secret key file");
//         return -1;
//     }
//     char sk_hex[2 * CRYPTO_SECRETKEYBYTES + 1];
//     bytes_to_hex(sk, sk_hex, CRYPTO_SECRETKEYBYTES);
//     fprintf(sk_file, "%s\n", sk_hex);
//     fclose(sk_file);

//     // Step 2: Sign the message
//     const char *message_hex = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";
//     hex_to_bytes(message_hex, m, MLEN);

//     crypto_sign(sm, &smlen, m, MLEN, sk);

//     FILE *sm_file = fopen("signature.hex", "w");
//     if (!sm_file) {
//         perror("Error opening signature file");
//         return -1;
//     }
//     char *sm_hex = malloc(2 * smlen + 1);
//     bytes_to_hex(sm, sm_hex, smlen);
//     fprintf(sm_file, "%s\n", sm_hex);
//     free(sm_hex);
//     fclose(sm_file);

//     // Step 3: Verify the signature
//     FILE *sm_file_read = fopen("signature.hex", "r");
//     if (!sm_file_read) {
//         perror("Error opening signature file for reading");
//         return -1;
//     }
//     sm_hex = malloc(2 * (MLEN + CRYPTO_BYTES) + 1);
//     read_exactly(sm_file_read, sm_hex, 2 * smlen);
//     fclose(sm_file_read);
//     hex_to_bytes(sm_hex, sm, smlen);
//     free(sm_hex);

//     FILE *pk_file_read = fopen("public_key.hex", "r");
//     if (!pk_file_read) {
//         perror("Error opening public key file for reading");
//         return -1;
//     }
//     read_exactly(pk_file_read, pk_hex, 2 * CRYPTO_PUBLICKEYBYTES);
//     fclose(pk_file_read);
//     hex_to_bytes(pk_hex, pk, CRYPTO_PUBLICKEYBYTES);

//     ret = crypto_sign_open(m2, &mlen, sm, smlen, pk);

//     printf("Verification result: %d\n", ret);
//     if (ret == 0) {
//         char *m2_hex = malloc(2 * mlen + 1);
//         bytes_to_hex(m2, m2_hex, mlen);
//         printf("Verified message: %s\n", m2_hex);
//         free(m2_hex);
//     } else {
//         printf("Verification failed\n");
//     }

//     return 0;
// }

