struct foo {
  int bar;
};

int main()
{
  struct foo a[10];
  struct foo *b;

  b = a;

  return 0;
}
