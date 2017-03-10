#include <stdio.h>

#define f(x) #x

#define print1(int_macro) printf("value of "#int_macro" is %d\n", int_macro)

#define print2(str_macro) printf("value of "#str_macro" is %s\n", str_macro)

#define PACKED // remove definition to change conditional compilation

#ifdef PACKED
#define CODE_MACRO __attribute__((packed))
#else
#define CODE_MACRO 
#endif

/* Some macros have normal C values such as integers of string constants.
 * Visualizing these macros are easy, with a simple printf statement. The
 * stringification operator # (which works inside body of macro definition)
 * allows us to display the macro name as well as its value.
 *
 * However, some macros simply evaluates to some piece of C code
 * as the 'CODE_MACRO' above. The question is, how do we display 
 * its value? 
 * we need to define a macro 'STR(X)' which given a macro name X evaluates
 * to a string repesenting the code to which X evaluates. For example,
 * we sould like STR(CODE_MACRO) to evaluates to "" or "__attribute__((packed))"
 * (depending on whether PACKED is defined or not). The following does the trick.
 * But why? From GNU cpp manual: "Macro arguments are completely macro-expanded 
 * before they are substituted into a macro body, unless they are stringified 
 * or pasted with other tokens". 
 * STR(CODE_MACRO) -> STR(__attribute__((packed)))
 *                 -> f(__attribute__((packed))) 
 *                 -> #__attribute__((packed))
 *                 -> "__attribute__((packed))"
 *
 * Note that f(CODE_MACRO) does not work:
 *
 * f(CODE_MACRO)   -> #CODE_MACRO   (no prior exapnasion of stringified argument)
 *                 -> "CODE_MACRO"
 */

#define STR(macro) f(macro)

int main()
{
  printf("%s\n", f(hello));

  print1(__STDC__);

  print2(__DATE__);

  printf("CODE_MACRO = \"%s\"\n", STR(CODE_MACRO));

  return 0;
}
