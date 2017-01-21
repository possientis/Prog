/* gcc -S countbits.c to generate assembly */ 

int main() {

  long data = 0xfedcba9876543210; 
  int sum = 0;
  int i = 0;


  while (i < 64) {
    sum += data & 1;
    data = data >> 1;
    ++i;
  }

  return 0;
}


