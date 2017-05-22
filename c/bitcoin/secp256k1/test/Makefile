LDFLAGS="-lsecp256k1"
#CPPFLAGS="-c -I/home/john/Prog/c/bitcoin/secp256k1/clone/include"
CPPFLAGS="-c"


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

main.o: main.c test.h
	$(CC) $(CPPFLAGS) main.c 
test.o:	test.c test.h
	$(CC) $(CPPFLAGS) test.c 
macro.t.o: macro.t.c 
	$(CC) $(CPPFLAGS) macro.t.c
context.t.o: context.t.c test.h
	$(CC) $(CPPFLAGS) context.t.c
callback.t.o: callback.t.c test.h
	$(CC) $(CPPFLAGS) callback.t.c
ec_pubkey.t.o: ec_pubkey.t.c test.h
	$(CC) $(CPPFLAGS) ec_pubkey.t.c
ecdsa_signature.t.o: ecdsa_signature.t.c test.h
	$(CC) $(CPPFLAGS) ecdsa_signature.t.c
nonce_function.t.o: nonce_function.t.c test.h
	$(CC) $(CPPFLAGS) nonce_function.t.c
ec_seckey.t.o: ec_seckey.t.c test.h
	$(CC) $(CPPFLAGS) ec_seckey.t.c
