#ifndef _SECP256K1_
# define _SECP256K1_

# ifdef __cplusplus
extern "C" {
# endif


/** This function does not exist in the original library. Its purpose is
 * simply to ensure that client code is indeed calling this version. 
 *
 * Returns: 1 always
 *
 */
int secp256k1_check_version();







# ifdef __cplusplus
}
# endif

#endif
