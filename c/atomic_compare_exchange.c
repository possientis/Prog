#include <stdio.h>
#include <assert.h>



int main()
{
  int exp;      // expected
  int des;      // desired
  int val;      // value
  int b;        // boolean result
  int weak = 0; // strong variation of compare-exchange (use that if in doubt)
  int suc;      // success memory order
  int fai;      // failure memory order


  // This allows to commit a read-modify-write operation
  // if(val == exp)
  //   { *val = des; return 1; }    // memory affected as per 'suc' memory order
  // else
  //   { *exp = *val ; return 0; }  // memory affected as per 'fai' memory order

  // __atomic_compare_exchange_n
  val = 2; exp = 2; des = 4; fai = suc = __ATOMIC_SEQ_CST;
  b = __atomic_compare_exchange_n(&val, &exp, des, weak, suc, fai);
  assert(b == 1); assert(val == 4); assert(exp == 2); assert(des == 4);
  
  val = 2; exp = 3; des = 4; fai = suc = __ATOMIC_SEQ_CST;
  b = __atomic_compare_exchange_n(&val, &exp, des, weak, suc, fai);
  assert(b == 0); assert(val == 2); assert(exp == 2); assert(des == 4);


  // __atomic_compare_exchange (same, except 'desired' is now a pointer)
  val = 2; exp = 2; des = 4; fai = suc = __ATOMIC_SEQ_CST;
  b = __atomic_compare_exchange(&val, &exp, &des, weak, suc, fai);
  assert(b == 1); assert(val == 4); assert(exp == 2); assert(des == 4);


  val = 2; exp = 3; des = 4; fai = suc = __ATOMIC_SEQ_CST;
  b = __atomic_compare_exchange(&val, &exp, &des, weak, suc, fai);
  assert(b == 0); assert(val == 2); assert(exp == 2); assert(des == 4);

  return 0;
}
