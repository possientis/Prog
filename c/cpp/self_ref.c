#define foo (4 + foo)

foo // (4 + foo)

#define ENUM1 ENUM1

ENUM1 // ENUM1

// if you have an enum, but you want #ifdef to be true for each constant

# define x (4 + y)
# define y (2 * x)

x // (4 + (2 * x))

y // (2 * (4 + y))




