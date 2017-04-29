all: main.o test.o \
	macro.t.o \
	context.t.o \
	callback.t.o \
	ec_pubkey.t.o \
	ecdsa_signature.t.o

	gcc -lsecp256k1 -o a.out main.o test.o \
		macro.t.o	\
		context.t.o \
		callback.t.o \
		ec_pubkey.t.o \
		ecdsa_signature.t.o


