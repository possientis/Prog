/**********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                             *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef _SECP256K1_NUM_
#define _SECP256K1_NUM_

#ifndef USE_NUM_NONE

#if defined HAVE_CONFIG_H
#include "libsecp256k1-config.h"
#endif

#if defined(USE_NUM_GMP)
#include "num_gmp.h"
#else
#error "Please select num implementation"
#endif

static void 

/************************************************************************/
secp256k1_num_copy  
/************************************************************************/

/* Copy a number. */

(

  secp256k1_num               *r, 
  const secp256k1_num         *a
  
)

;



static void 

/************************************************************************/
secp256k1_num_get_bin
/************************************************************************/

/** Convert a number's absolute value to a binary big-endian string.
 *  There must be enough place. */

(

  unsigned char               *r, 
  unsigned int                rlen, 
  const secp256k1_num *a
  
)

;




static void 

/************************************************************************/
secp256k1_num_set_bin
/************************************************************************/

/** Set a number to the value of a binary big-endian string. */

(

  secp256k1_num               *r, 
  const unsigned char         *a, 
  unsigned int                alen
  
)

;



static void 

/************************************************************************/
secp256k1_num_mod_inverse
/************************************************************************/

/** Compute a modular inverse. The input must be less than the modulus. */

(

  secp256k1_num               *r, 
  const secp256k1_num         *a, 
  const secp256k1_num         *m
  
)

;



static int 

/************************************************************************/
secp256k1_num_jacobi
/************************************************************************/

/** Compute the jacobi symbol (a|b). b must be positive and odd. */

(

  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;



static int 

/************************************************************************/
secp256k1_num_cmp
/************************************************************************/

/** Compare the absolute value of two numbers. */

(
 
  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;


static int 

/************************************************************************/
secp256k1_num_eq
/************************************************************************/

/** Test whether two number are equal (including sign). */

(
 
  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;



static void 

/************************************************************************/
secp256k1_num_add
/************************************************************************/

/** Add two (signed) numbers. */

(
 
  secp256k1_num               *r, 
  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;


static void 

/************************************************************************/
secp256k1_num_sub
/************************************************************************/

/** Subtract two (signed) numbers. */

(
 
  secp256k1_num               *r, 
  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;


static void 

/************************************************************************/
secp256k1_num_mul
/************************************************************************/

/** Multiply two (signed) numbers. */

(
 
  secp256k1_num               *r, 
  const secp256k1_num         *a, 
  const secp256k1_num         *b
  
)

;



static void 

/************************************************************************/
secp256k1_num_mod
/************************************************************************/

/** Replace a number by its remainder modulo m. m's sign is ignored. 
 * The result is a number between 0 and m-1, even if r was negative. */

(
 
  secp256k1_num               *r, 
  const secp256k1_num         *m

)

;



static void 

/************************************************************************/
secp256k1_num_shift
/************************************************************************/

/** Right-shift the passed number by bits bits. */

(
 
  secp256k1_num               *r, 
  int                         bits
  
)

;



static int 

/************************************************************************/
secp256k1_num_is_zero
/************************************************************************/

/** Check whether a number is zero. */

(
 
  const secp256k1_num         *a
  
)

;



static int 

/************************************************************************/
secp256k1_num_is_one
/************************************************************************/

/** Check whether a number is one. */

(
 
  const secp256k1_num         *a
)

;



static int 

/************************************************************************/
secp256k1_num_is_neg
/************************************************************************/

/** Check whether a number is strictly negative. */

(
 
  const secp256k1_num         *a
  
)

;


static void 

/************************************************************************/
secp256k1_num_negate
/************************************************************************/

/** Change a number's sign. */

(
 
  secp256k1_num               *r

)

;

#endif

#endif
