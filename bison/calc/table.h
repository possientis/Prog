#define NSYMS 20 /* maximum number of symbols */

struct symtab {
  const char* name;
  double (*funcptr)(double);
  double value;
} symtab [NSYMS];

struct symtab *symlook();

double sqrt(), exp(), log();

void addfunc(const char *, double (*)(double));
