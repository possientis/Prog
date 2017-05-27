#include <stdlib.h>
#include <stdio.h>

#include "MGL6.tab.h"

extern void yyset_in(FILE*);
const char *progname = "mgl";
int lineno  = 1;

#define DEFAULT_OUTFILE "screen.out"

const char *usage = "%s: usage [infile] [outfile]\n";

int main(int argc, char* argv[])
{

  printf("MGL is running...\n");
  
  const char *outfile;
  const char *infile;

  extern FILE *yyin, *yyout;

  progname = argv[0];

  if(argc > 3)
  {
    fprintf(stderr, usage, progname);
    exit(1);
  }

  if(argc > 1)
  {
    infile = argv[1];
    yyin = fopen(infile,"r");
    if(yyin == NULL)
    {
      fprintf(stderr, "%s: cannot open %s\n", progname, infile);
      exit(1);
    }
  }

  if(argc > 2)
  {
    outfile = argv[2];
  }
  else
  {
    outfile = DEFAULT_OUTFILE;
  }

  yyout = fopen(outfile,"w");
  if(yyout == NULL)
  {
    fprintf(stderr,"%s:cannot open %s\n", progname, outfile);
    exit(1);
  }

  yyset_in(yyin);

  yyparse();

  printf("parsing was successful...\n");

  return 0;
}

int yyerror(const char *s)
{
  fprintf(stderr, "%s\n", s);
  return 1;
}

int warning(const char *s, const char* t)
{
  fprintf(stderr, "%s: %s\n", progname, s);
  if(t) {
    fprintf(stderr, "% s\n", t);
    fprintf(stderr, " line %d\n",lineno);
  }
  return 0;
}

