extern void a(char *);

int main(int argc, char* arg[])
{
  static char string[] = "Hello, world!\n";

  a(string);
}
