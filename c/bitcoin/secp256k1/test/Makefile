all: main.o test.o \
	test_macro.o \
	test_context.o \
	test_callback.o \
	test_pubkey.o

	gcc -lsecp256k1 -o a.out main.o test.o \
		test_macro.o	\
		test_context.o \
		test_callback.o \
		test_pubkey.o


