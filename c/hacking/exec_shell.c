#include <unistd.h>

int main() {

  const char *filename = "/bin/sh";
  char *const argv[2] = { (char*) filename , NULL};
  char *const envp[1] = { NULL };

  execve(filename, argv, envp);

  return 0;

}
