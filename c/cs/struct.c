#include <stdio.h>

struct rect {
    int llx;    /* x coordinate of lower left corner */
    int lly;    /* y coordinate of lower left corner */
    int color;  /* code of color */
    int width;  /* width (in pixels) */ 
    int height; /* heigth (in pixels) */
};


struct align {
    int i;
    char c;
    int j;
};


int area(struct rect *rp) {
    return rp->width * rp->height;
}

int main() {
    struct rect r;
    r.llx = r.lly = 0;
    r.color = 0xFF00FF;
    r.width = 10;
    r.height = 20;

    printf("area = %d\n", area(&r));
    
    /* 12, not 9 !!! */
    printf("sizeof (struct align) = %d\n", sizeof(struct align));

    return 0;
}


void rotate_left(struct rect *rp) {
    int t = rp->height;
    rp->height = rp->width;
    rp->width  = t;
    rp->llx   -= t;
}




