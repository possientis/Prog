
void nop()
{
  // do nothing
}

int main()
{
  int i;
  for(i = 0; i < 1000000; ++i){
    nop();
  }

  return 0;
}
