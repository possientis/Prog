%{

unsigned int charCount = 0, wordCount = 0, lineCount = 0;

#undef yywrap /* sometimes a macro by default */

%}

word [^ \t\n]+
eol \n

%%
{word}          { wordCount++; charCount += yyleng; }
{eol}           { charCount++; lineCount++; }
.                 charCount++; 
%%

char **fileList;
unsigned int currentFile = 0;
unsigned int nFiles;
unsigned long totalCC = 0;
unsigned long totalWC = 0;
unsigned long totalLC = 0;


int main(int argc, char* argv[])
{

  FILE* file;
  fileList = argv + 1;
  nFiles = argc - 1;

  if(argc == 2) {
    currentFile = 1;
    file = fopen(argv[1], "r");
    if(!file) {
      fprintf(stderr, "could not open %s\n", argv[1]);
      exit(1);
    }
    yyin = file;
  }

  if(argc > 2)
    yywrap(); /* open first file */

  yylex();
  if(argc > 2){
    printf("%8lu %8lu %8lu %s\n", lineCount, wordCount, charCount, fileList[currentFile - 1]);
    totalCC += charCount;
    totalWC += wordCount;
    totalLC += lineCount;
    printf("%8lu %8lu %8lu\n", totalLC, totalWC, totalCC);
  } else {
    printf("%8lu %8lu %8lu\n", lineCount, wordCount, charCount);
  }
  
  return 0;
}







