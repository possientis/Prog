void decode1 (int *xp, int *yp, int *zp) 
{
    int y = *yp;
    int z = *zp;
    int x = *xp;

    *yp = x;
    *zp = y;
    *xp = z;
}
