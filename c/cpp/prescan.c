#define f(x) ((x)*2)

// arguments in macro calls are expanded first

f(f(1)) // -> f( ((1)*2) )
        // -> ((((1)*2))*2)
