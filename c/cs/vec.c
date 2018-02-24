#include <malloc.h>
#include "vec.h"

/* Create vector of specified length */
vec_ptr new_vec(long len)
{
    /* Allocate header structure */
    vec_ptr result = (vec_ptr) malloc(sizeof(vec_rec));
    if(!result)
        return NULL; /* could not allocate storage */
    result->len = len;
    /* Allocate array */
    if(len > 0) {
        data_t *data = (data_t *) calloc(len,sizeof(data_t));
        if(!data) {
            free((void*) result);
            return NULL; /* could not allocate storage */
        }
        result->data = data;
    }
    else
        result->data = NULL;
    return result;
}


/* Retrieve vector element and store at destination.
 * Return 0 (out of bound) or 1 (successful)
 */
int get_vec_element(vec_ptr v, long index, data_t *dest)
{
    if (index < 0 || index >= v->len)
        return 0;
    *dest = v->data[index];
    return 1;
}


/* Return length of vector */
long vec_length(vec_ptr v)
{
    return v->len;
}

/* Implementation with maximum use of data abstraction */
void combine1(vec_ptr v, data_t *dest)
{
    long i;
    data_t acc = IDENT;
    for(i = 0; i < vec_length(v); i++) {
        data_t val;
        get_vec_element(v, i, &val);
        acc = acc OP val;
    }
    *dest = acc;
}

void combine2(vec_ptr v, data_t *dest)
{
    long i;
    long length = vec_length(v);

    *dest = IDENT;
    for(i = 0; i < length; i++) {
        data_t val;
        get_vec_element(v, i, &val);
        *dest = *dest OP val;
    }
}

int main() 
{
    data_t r;

    long size = 10000L;

    vec_ptr v = new_vec(size);    

    long i;
    for(i = 0; i < 20000L; ++i) {
        combine1(v,&r);
    }
    
    return 0;
}

