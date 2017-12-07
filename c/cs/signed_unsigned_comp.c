#include <stdio.h>


int main() {

    /* LHS is signed, RHS unsigned -> LHS cast to unsigned */
    /* Hence, the result is 0 not 1.                       */
    
    int x = (-1 < 0U);
    printf("x = %d\n",x);


    int y = 0x7FFFFFFF;

    /* -y -1 is -0x80000000 which is a signed integer, with
     * two's complement binary representation 0x80000000.
     * When compared against 0x80000000U, it is converted
     * to an unsigned integer. Such conversion leaves the
     * binary representation intact. Hence the comparison
     * is between two equal unsigned integers and the result 
     * is 1. */
    int c1 = (-y - 1 == 0x80000000U); 
    printf("c1 = %d\n", c1); /* c1 = 1 */

    int c2 = (-y -1 < y); /* signed comparison */
    printf("c2 = %d\n", c2); /* c2 = 1 */

    /* -y has binary representation 0x80000001. It is involved
     * in a binary operation involving the insigned integer 1U.
     * Hence it is converted to unsigned integer. Such conversion
     * leaves the binary representation intact. Hence -y - 1U 
     * evaluates to 0x80000000U. Now in the comparison, y is
     * converted to 0x7FFFFFFFU. Hence the comparison leads to 0.
     */
    int c3 = (-y - 1U < y);
    printf("c3 = %d\n", c3); /* c3 = 0 */

    int c4 = (-y -1 < -y); /* signed comparison */
    printf("c4 = %d\n", c4); /* c4 = 1 */

    /* -y -1U evaluates to 0x80000000U. -y is converted to 
     * 0x80000001U. Hence the comparison yields 1 
     */
    int c5 = (-y - 1U < -y);
    printf("c5 = %d\n", c5); /* c5 = 1 */

    return 0;
}
