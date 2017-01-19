

int main()
{
  long a = 3;
  long b = 7;
  long temp;

  if (a < b) {
    temp = a;
    a = b;
    b = temp;
  }

  return 0;
}
