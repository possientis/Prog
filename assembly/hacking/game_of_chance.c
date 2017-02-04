#include <stdio.h>

struct user {
  int uid;
  int credits;
  int highscore;
  char name[100];
  int (*current_game) ();
};


// global
struct user player;

// This function is used to input the player name, since
// scanf("%s", &whatever) will stop input at the first space.
//
// This function does not prevent a buffer overflow !!
//
//
void input_name() {

  char *name_ptr, input_char='\n';

  while(input_char == '\n')           // Flush any leftover
    scanf("%c", &input_char);         // newline chars.

  name_ptr = (char *) &(player.name); // name_ptr = player name's address
  while(input_char != '\n') {         // Loop until newline.
    *name_ptr = input_char;           // Put the input char into name field.
    scanf("%c", &input_char);         // Get the next char.
    name_ptr++;                       // Increment the name pointer.
  }

  *name_ptr = 0; // Terminate the string.
}


int main() {

  printf("input name:");
  input_name();
  printf("name is --%s--\n", player.name);
}
