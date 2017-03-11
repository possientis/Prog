#define f(x) ((x)*2)

// arguments in macro calls are expanded first

f(f(1)) // -> f( ((1)*2) )
        // -> ((((1)*2))*2)


#define AFTERX(x)   X_ ## x
#define XAFTERX(x)  AFTERX(x) 
#define TABLESIZE   1024
#define BUFSIZE     TABLESIZE 

TABLESIZE           // -> 1024
BUFSIZE             // -> 1024

AFTERX(BUFSIZE)     // -> X_BUFSIZE (argument not expanded when ## or # used on it)
XAFTERX(BUFSIZE)    // -> XAFTERX(TABLESIZE) (prescan triggered as no # or ##)
                    // -> XAFTERX(1024) (prescan always does full expansion)
                    // -> AFTERX(1024)
                    // -> X_1024


#define foo a,b
#define bar(x) lose(x)
#define lose(x) (1 + (x))

foo                 // -> a,b
//bar(foo)            // -> x = foo in bar(x)
                    // -> x = a,b in bar(x)   (argument expansion complete)
                    // -> x = a,b in lose(x)  
                    // -> lose(a,b)   
                    // -> error as lose requires single argument
// prescan.c:28:8: error: macro "lose" passed 2 arguments, but takes just 1

#define foo2 (a,b)

// or

#define bar2(x) lose((x))

bar(foo2)           // -> x = foo2 in bar(x)
                    // -> x = (a,b) in bar(x)
                    // -> x = (a,b) in lose(x)
                    // -> x = (a,b) in (1 + (x))
                    // -> (1 + ((a,b)))

bar2(foo)           // -> x = foo in bar2(x)
                    // -> x = a,b in bar2(x)
                    // -> x = a,b in lose((x))
                    // -> lose((a,b))
                    // -> x = (a,b) in lose(x)
                    // -> x = (a,b) in (1 + (x))
                    // -> (1 + ((a,b)))
                   


