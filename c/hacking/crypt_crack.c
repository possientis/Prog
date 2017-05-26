#define _XOPEN_SOURCE /* get crypt() declaration from <unistd.h */
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* Barf a message and exit. */
void barf(const char *message, const char *extra) {
  printf(message, extra);
  exit(1);
}


/* A dictionary attack example program */
int main(int argc, char *argv[]) {

  FILE *wordlist;
  char *hash, word[30], salt[3];

  if(argc < 3)
    barf("Usage: %s <wordlist file> <password hash>\n", argv[0]);

  strncpy(salt, argv[2], 2);  // First 2 bytes of hash are the salt.
  salt[2] = '\0';             // terminate string
  printf("Salt value is \'%s\'\n", salt);

  if( (wordlist = fopen(argv[1], "r")) == NULL) // Open the wordlist.
    barf("Fatal: couldn't open the file \'%s\'.\n", argv[1]);

  while(fgets(word, 30, wordlist) != NULL) {  // Read each word
    word[strlen(word)-1] = '\0';              // Remove the '\n' byte at the end.
    hash = crypt(word, salt);                 // Hash the word using the salt.
    printf("trying word: %-30s ==> %15s\n", word, hash);
    if(strcmp(hash, argv[2]) == 0) {          // If the hash matches
      printf("The hash \"%s\" is from the ", argv[2]);
      printf("plaintext password \"%s\".\n", word);
      fclose(wordlist);
      exit(0);
    }
  }
  printf("Couldn't find the plaintext password in the supplied wordlist.\n");
  fclose(wordlist);

  return 0;
}
