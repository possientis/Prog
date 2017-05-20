#ifndef INCLUDED_TEST_H
#define INCLUDED_TEST_H

#include <stddef.h>
#include<secp256k1.h>

typedef struct {const char* in; int out;} callback_t;

// testing functions
extern int test_macro();
extern int test_context();
extern int test_callback();
extern int test_ec_pubkey();
extern int test_ecdsa_signature();
extern int test_nonce_function();
extern int test_ec_seckey();


// global test data
extern callback_t callback_data;
extern secp256k1_context *ctx;
extern const unsigned char *pubkey_bytes1;
extern const unsigned char *pubkey_bytes2;
extern const unsigned char *pubkey_bytes3;
extern const unsigned char *pubkey_bytes4;
extern const unsigned char *pubkey_bytes5;
extern const unsigned char *pubkey_bytes6;
extern const unsigned char *sig_bytes1;
extern const unsigned char *sig_bytes2;
extern const unsigned char *hash_bytes1;
extern const unsigned char *hash_bytes2;
extern const unsigned char *priv_bytes1;
extern const unsigned char *nonce_bytes1;
extern const unsigned char *order_bytes;
extern const unsigned char *order_minus_one_bytes;
extern const unsigned char *tweak_bytes;

void default_callback(const char* message, void* data);
int is_all_null(const void *ptr, size_t size);
int test_setup();
int test_cleanup();


#endif
