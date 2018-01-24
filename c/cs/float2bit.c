#include <stdio.h>

unsigned float2bit(float f) {
    union {
        float f;
        unsigned u;
    } temp;

    temp.f = f;

    return temp.u;
}


unsigned copy(unsigned u) {
    return u;
}


/* The function returns the double corresponding to the 
 * bit pattern of u[0] and u[1]. However, IEEE 754 specifies
 * an encoding from unsigned long -> double and the 
 * unsigned long represented by the bytes of u[0],u[1]
 * is different on a little and big endian machine */ 

double bit2double(unsigned w0, unsigned w1) {
    union {
        double d;
        unsigned u[2];
    } temp;

    temp.u[0] = w0;
    temp.u[1] = w1;
    return temp.d;
}

int main() {

    float f1 = 0.0;
    float f2 = 1.0;
    float f3 = -1.0;

    printf("representation of %f is 0x%.8x\n",f1,float2bit(f1));
    printf("representation of %f is 0x%.8x\n",f2,float2bit(f2));
    printf("representation of %f is 0x%.8x\n",f3,float2bit(f3));

    return 0;
}
