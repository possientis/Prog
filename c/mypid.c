/* technique to display system data types with printf
 * without creating a system dependency
 * use %ld and explicit cast to long
 *
 * Exception for off_t
 * use %lld and cast to (long long) */

// portable, portability

#include <stdio.h>
#include <sys/types.h>

int main(){
  pid_t mypid;
  mypid = getpid();
  printf("My PID is %ld\n", (long) mypid);

  return 0;
}
