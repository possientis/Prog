// 'static' keyword creates local symbols within translation unit
// This is 'static' as in 'static linkage', not to be confused with
// local variables of functions which have static storage.

int main(){ return 0;}

// lowercase 't' indicates local symbol
// $ gcc static.c; nm a.out | grep foo  # 0000000000000660 t foo
static void foo(){} // symbol is local to translation unit

// uppercase 'T' indicates global symbol
// $ gcc static.c; nm a.out | grep bar  # 0000000000000667 T bar 
void bar(){}        // symbol is global


// lowercase 'd' indicates local symbol
// $ gcc static.c; nm a.out | grep FOO  # 0000000000201028 d FOO
static int FOO = 4;

// uppercase 'D' indicates global symbol
// $ gcc static.c; nm a.out | grep BAR  # 000000000020102c D BAR
int BAR = 5;

