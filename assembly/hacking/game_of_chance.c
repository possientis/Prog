#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

//#include <string.h>
//#include <sys/stat.h>
#include "hacking.h"

#define DATAFILE "/var/chance.data" // File to store user data

// Custom user struct to store information about users
struct user {
  int uid;
  int credits;
  int highscore;
  char name[100];
  int (*current_game) ();
};

// Function prototypes
int get_player_data();
void register_new_player();
void update_player_data();
void show_highscore();
void jackpot();
void input_name();
void print_cards(char *, char *, int);
int take_wager(int, int);
void play_the_game();
int pick_a_number();
int dealer_no_match();
int find_the_ace();

// Global variables
struct user player;

int main() {

  int choice, last_game;

  srand(time(0));               // Seed the randomizer with the current time

  if(get_player_data() == -1)   // Try to read player data from file
    register_new_player();      // If there is no data, register a new player

  while(choice != 7) {

    printf("-=[ Game of Chance Menu ]=-\n");
    printf("1 - Play the Pick a Number game\n");
    printf("2 - Play the No Match Dealer game\n");
    printf("3 - Play the Find the Ace game\n");
    printf("4 - View current high score\n");
    printf("5 - Change your user name\n");
    printf("6 - Reset your account at 100 credits\n");
    printf("7 - Quit\n");
    printf("[Name: %s]\n", player.name);
    printf("[You have %u credits] -> ", player.credits);
    scanf("%d", &choice);

    if((choice < 1) || (choice > 7))
      printf("\n[!!] The number %d is an invalid selection.\n\n", choice);
    else if (choice < 4) {      // Otherwise, choice was a game of some sort.
      if(choice != last_game) { // If the function ptr isn't set
        if(choice == 1)         // then point it at the selected game
          player.current_game = pick_a_number;
        else if(choice == 2)
          player.current_game = dealer_no_match;
        else
          player.current_game = find_the_ace;
        last_game = choice;     // and set last_game.
      }
      play_the_game();          // Play the game.
    }
    else if (choice == 4)
      show_highscore();
    else if (choice == 5) {
      printf("\nChange user name\n");
      printf("Enter your new name: ");
      input_name();
      printf("Your name has been changed.\n\n");
    }
    else if (choice == 6) {
      printf("\nYour account has been reset with 100 credits.\n\n");
      player.credits = 100;
    }
  }

  update_player_data();
  printf("\nThanks for playing! Bye.\n");
  return 0;
}


// This function reads the player data for the current uid
// from the file. It returns -1 if it is unable to find player
// data for the current uid.
int get_player_data() {
  int fd, uid, read_bytes;
  struct user entry;

  uid = getuid();

  fd = open(DATAFILE, O_RDONLY);
  if(fd == -1) // Can't open the file, maybe it doesn't exist
    return -1;

  read_bytes = read(fd, &entry, sizeof(struct user));   // Read the first chunk.

  while(entry.uid != uid && read_bytes > 0) { // Loop until proper uid is found.
    read_bytes = read(fd, &entry, sizeof(struct user)); // Keep reading.
  }

  close(fd); // Close the file.
  if(read_bytes < sizeof(struct user)) // the end of file was reached.
    return -1;
  else
    player = entry; // Copy the read entry into the player struct.

  return 1;         // Return a success.
}


// This is the new user registration function.
// It will create a new player account and append it to the file.
void register_new_player() {
  int fd;
  printf("-=-={ New Player Registration }=-=-\n");
  printf("Enter your name: ");
  input_name();

  player.uid = getuid();
  player.highscore = 0;
  player.credits = 100;

  fd = open(DATAFILE, O_WRONLY|O_CREAT|O_APPEND, S_IRUSR|S_IWUSR);
  if(fd == -1)
    fatal("in register_new_player() while opening file");

  write(fd, &player, sizeof(struct user));
  close(fd);
  printf("\nWelcome to the Game of Chance %s.\n", player.name);
  printf("You have been given %u credits.\n", player.credits);
}

// This function writes the current player data to the file.
// It is used primarily for updating the credits after games.
void update_player_data() {
  int fd, i, read_uid;
  char burned_byte;

  fd = open(DATAFILE, O_RDWR);
  if(fd == -1) // If open fails here, something is really wrong.
    fatal("in update_player_data() while opening file");

  read(fd, &read_uid, 4);   // Read the uid from the first struct.

  while(read_uid != player.uid) { // Loop until correct uid is found.
    for(i=0; i < sizeof(struct user) - 4; i++)  // Read through the
      read(fd, &burned_byte, 1);                // rest of that struct.
    read(fd, &read_uid, 4);                     // Read from the next struct.
  }

  write(fd, &(player.credits), 4);              // Update credits.
  write(fd, &(player.highscore), 4);            // Update highscore.
  write(fd, &(player.name), 100);               // Update name.
  close(fd);
}

// TODO


/// This function is used to input the player name, since
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


