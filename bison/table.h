#define NSYMS 20 /* maximum number of symbols */

struct symtab {
  const char* name;
  double value;
} symtab [NSYMS];

struct symtab *symlook();
