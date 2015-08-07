typedef unsigned long dev_t;
#include<linux/kdev_t.h>
#include<stdio.h>

int main()
{
  int major = 10;
  int minor = 63;

  dev_t dev = MKDEV(major,minor);

  int a = MAJOR(dev);
  int b = MINOR(dev);

  printf("a = %i, b = %i\n", a, b);

 return 0;
}
