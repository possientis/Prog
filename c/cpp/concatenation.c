void quit_command() { /* something */ }
void help_command() { /* something */ }

struct command 
{
  const char* name;
  void (*function) (void);
};


// possible but inconvenient
struct command command1[] =
{
  { "quit", quit_command },
  { "help", help_command }
};

// stringify & concatenate
#define COMMAND(NAME) { #NAME, NAME ## _command } 

// more convenient, check macro expansion with gcc -E
struct command command2[] =
{
  COMMAND(quit),
  COMMAND(help)
};


