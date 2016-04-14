#ifndef FILE_PERMS_H
#define FILE_PERMS_H

#include <sys/types.h>

#define FP_SPECIAL 1      /* Include set-user-ID, set-group-ID, and sticky
                           * bit information in returned string */
char *filePermStr(mode_t perm, int flags);

#endif
