set -e
if [ -z "$1" ]; then
  echo "usage ./$0 [ main | clone ]"
  exit 1
fi

if [ "$1" == "main" ]; then
  LDFLAGS="-L/home/john/Libs/secp256k1/.libs"
  CPPFLAGS="-I/home/john/Libs/secp256k1/include"
  CLONE=0
  LD_LIBRARY_PATH="/home/john/Libs/secp256k1/.libs"
elif [ "$1" == "clone" ]; then
  LDFLAGS="-L/home/john/Prog/c/bitcoin/secp256k1/clone/.libs"
  CPPFLAGS="-I/home/john/Prog/c/bitcoin/secp256k1/clone/include"
  CLONE=1
  LD_LIBRARY_PATH="/home/john/Prog/c/bitcoin/secp256k1/clone/.libs"
else
  echo "usage ./$0 [ main | clone ]"
  exit 1
fi


gcc -c $CPPFLAGS -DCLONE=$CLONE main.c
gcc -c $CPPFLAGS test.c
gcc -c $CPPFLAGS macro.t.c
gcc -c $CPPFLAGS context.t.c
gcc -c $CPPFLAGS callback.t.c
gcc -c $CPPFLAGS ec_pubkey.t.c
gcc -c $CPPFLAGS ecdsa_signature.t.c
gcc -c $CPPFLAGS nonce_function.t.c
gcc -c $CPPFLAGS ec_seckey.t.c

gcc $LDFLAGS -o a.out -lsecp256k1 \
  main.o \
  test.o \
  macro.t.o \
  context.t.o \
  callback.t.o \
  ec_pubkey.t.o \
  ecdsa_signature.t.o \
  nonce_function.t.o \
  ec_seckey.t.o

export LD_LIBRARY_PATH
./a.out
./clean.sh



