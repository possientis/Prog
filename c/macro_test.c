// cpp macro_test.c | grep -v '\#' to check macro expansion

#define f(x) x x
f (1
#undef f
#define f 2
f)

// -> 1 2 1 2


#define twice(x) (2*(x))
#define call_with_1(x) x(1)

call_with_1(twice)
// -> twice(1)
// -> (2*(1))


#define strange(file) fprintf(file, "%s %d", 

strange(stderr) p, 35)
// -> fprintf(stderr, "%s %d", p, 35)


int x = 5;

typeof x y = 6;
