#ifndef INCLUDED_TEST_H
#define INCLUDED_TEST_H

#include <stddef.h>
#include<secp256k1.h>

typedef struct {const char* in; int out;} callback_t;


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

void default_callback(const char* message, void* data);
int is_all_null(const void *ptr, size_t size);
int test_setup();


#endif
