#include <string.h>
#include <stdlib.h>

#include "table.h"

extern int yyerror(const char*);

struct symtab *symlook(const char* s)
{
  const char *p;
  struct symtab *sp;

  for(sp = symtab; sp < &symtab[NSYMS]; ++sp) {

    /* is it already there ? */
    if(sp->name && !strcmp(sp->name,s))
      return sp;

    /* is it free */
    if(!sp->name) {
      sp->name =strdup(s);
      return sp;
    }

    /* otherwise continue to next*/
  }

  yyerror("Too many symbols");
  exit(1);
}

void addfunc(const char *name, double (*func)(double)){
  struct symtab *sp = symlook(name);
  sp->funcptr = func; 
}
  

