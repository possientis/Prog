%{
#undef input
#undef unput
//int input(void);
void unput(int ch);

unsigned int verbose;
const char *progName;
%}

%%

-h        |
"-?"      |
--help    { 
            printf("usage: %s [--help|-h|-?] [--verbose|-v]"
                   "[(--file|-f) filename]\n", progName);
          }

-v        |
--verbose { 
            printf("verbose mode is on\n"); verbose = 1;
          }

%%

char **targv;   /* remembers arguments */
char **arglim;  /* end of arguments */

int main(int argc, char* argv[])
{
  progName = argv[0];
  targv = argv + 1;
  arglim = argv + argc;
  yylex();
}

static unsigned int offset = 0;

/*
int 
input(void)
{

  char c;
  if(targv >= arglim)
    return 0;   // EOF
  
  // end of argument, move to the next 
  if ((c = targv[0][offset++]) != '\0')
    return c;
  targv++;
  offset = 0;
  return ' ';
}
*/

/* simple unput only backs up, doesn't allow yout to */
/* put back different text */

void 
unput(int ch)
{
  /* AT&T lex sometimes puts back the EOF */
  if(ch == 0)
    return;     /* ignore, can't put back EOF */
  if(offset) {   /* back up in current arg */
    offset--;
    return;
  }
  targv--;
  offset = strlen(*targv);
}
  







