// #line directive alter the value of __LINE__ and __FILE__

#line 45
#warning "issuing this warning, should be line 45"
some code
other code
#warning "another warning in line 48"

#line 178 "/usr/dummy/some-file-ref.c"
#warning "let's see what happens"

// #line directive can be parameterized

#define LINE 90
#line LINE
#warning "this is a warning on line 90" // but filename not changed

#line LINE "line.c"
#warning "this is a warning on line 90"


