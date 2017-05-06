#include <string.h>
#include <unistd.h>

void lowered_privilege_function(unsigned char *ptr) {
  char buffer[50];
  seteuid(5); // Drop privileges to games user.
  strcpy(buffer, ptr);
}

int main(int argc, char *argv[]) {
  if (argc > 0)
    lowered_privilege_function(argv[1]);
}
