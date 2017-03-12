#include <stdio.h>
#include <ctype.h>
char *progname;

#define NUMBER 400
#define COMMENT 401
#define TEXT 402
#define COMMAND 403

int main(int argc, char *argv[])
{
  int val;

  while(val = lexer()) printf("value is %d\n", val);

  return 0;
}

int lexer()
{
  int c;

  while((c = getchar()) == ' ' || c == '\t')
    ;

  if(c == EOF)
    return 0;

  if(c == '.' || isdigit(c)) { /* number */
    while((c = getchar()) != EOF && isdigit(c));
    
    if(c == '.') while ((c = getchar()) != EOF && isdigit(c));

    unget(c, stdin);
    return NUMBER;
  }
  // TODO
    

