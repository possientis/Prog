int leal1(int x, int y) {
    return x + 6;           /* leal 6(%rdi), %eax           */
}

int leal2(int x, int y) {
    return x + y;           /* leal (%rdi,%rsi), % eax      */
}

int leal3(int x, int y) {
    return x + 4*y;         /* leal (%rdi,%rsi,4), %eax     */
}


int leal4(int x, int y) {
    return 9*x + 7;         /* leal 7(%rdi,%rdi,8), %eax    */ 
}

int leal5(int x, int y) {
   return 4*y + 10;         /* leal 10(,%rsi,4), %eax       */
} 

int leal6(int x, int y) {
    return x + 2*y + 9;     /* leal 9(%rdi,%rsi,2), %eax    */
}
