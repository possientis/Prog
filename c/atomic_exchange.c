#include <stdio.h>
#include <assert.h>

int main()
{
  long n1, n2, n3;

  n1 = 1, n2 = 2; n3 = 0;
  n3 = __atomic_exchange_n(&n1, n2, __ATOMIC_RELAXED); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  n3 = __atomic_exchange_n(&n1, n2, __ATOMIC_SEQ_CST); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  n3 = __atomic_exchange_n(&n1, n2, __ATOMIC_ACQUIRE); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  n3 = __atomic_exchange_n(&n1, n2, __ATOMIC_RELEASE); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  n3 = __atomic_exchange_n(&n1, n2, __ATOMIC_ACQ_REL); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  __atomic_exchange(&n1, &n2, &n3, __ATOMIC_RELAXED); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  __atomic_exchange(&n1, &n2, &n3, __ATOMIC_SEQ_CST); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  __atomic_exchange(&n1, &n2, &n3, __ATOMIC_ACQUIRE); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  __atomic_exchange(&n1, &n2, &n3, __ATOMIC_RELEASE); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);

  n1 = 1, n2 = 2; n3 = 0;
  __atomic_exchange(&n1, &n2, &n3, __ATOMIC_ACQ_REL); /* n3 = n1; n1 = n2 */
  assert(n3 == 1); assert(n1 == 2); assert(n2 == 2);


  return 0;
}
