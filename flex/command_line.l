%{
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

int main(int argc, char* argv[])
{
  progName = argv[0];
  yylex();
}
