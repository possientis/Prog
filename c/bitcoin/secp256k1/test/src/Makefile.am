#SUBDIRS = modules/hithere

bin_PROGRAMS = Test_secp256k1
Test_secp256k1_SOURCES = main.c test.c test.h callback.t.c \
												 context.t.c ecdsa_signature.t.c ec_pubkey.t.c \
												 ec_seckey.t.c macro.t.c nonce_function.t.c
Test_sep256k1_CFLAGS = -I/home/john/Prog/c/bitcoin/secp256k1/clone/include
Test_secp256k1_LDADD = -L/home/john/Prog/c/bitcoin/secp256k1/clone/.libs/libsecp256k1.so

