LDFLAGS="-lsecp256k1"


all: main.o test.o \
	macro.t.o \
	context.t.o \
	callback.t.o \
	ec_pubkey.t.o \
	ecdsa_signature.t.o\
	nonce_function.t.o \
	ec_seckey.t.o

	gcc $(LDFLAGS) -o a.out main.o test.o \
		macro.t.o	\
		context.t.o \
		callback.t.o \
		ec_pubkey.t.o \
		ecdsa_signature.t.o \
		nonce_function.t.o \
		ec_seckey.t.o


