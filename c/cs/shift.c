int shift_left1 (int x) {
    return x << 10;         /* sall $10, %eax */
} 

int shift_left2 (unsigned x) {
    return x << 10;         /* sall $10, %eax */
} 


int shift_right1 (int x) {
    return x >> 10;         /* sarl $10, %eax */
} 

int shift_right2 (unsigned x) {
    return x >> 10;         /* shrl $10, %eax */
} 

