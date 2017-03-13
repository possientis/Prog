#pragma GCC poison printf fprintf sprintf

sprintf(some_string, "hello");


// however
#define strrchr rindex
#pragma GCC poison rindex

strrchr(some_string, 'h');  // no error
