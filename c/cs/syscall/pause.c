#include <unistd.h>

int main() 
{
    int i;
    i = pause(); /* need signal after that */

    return 0;
}
