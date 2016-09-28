#ifndef CREATE_PID_FILE_H
#define CREATE_PID_FILE_H

#define CPF_CLOEXEC 1 /* not sure what value to set here */

/* Open/create the file named in 'pidFile', lock it, optionally set the
 * close-on-exec flag for the file descriptor, write our PID into the file,
 * and (in case the caller is interested) return the file descriptor
 * referring to the locked file. The caller is responsible for deleting
 * 'pidFile' file (just) before process termination. 'progName' should be the
 * name of the calling program (i.e., argv[0] or similar), and is used only for
 * diagnostic messages. If we can't open 'pidFile', or we encounter some other
 * error, then we print an appropriate diagnostic and terminate.
 */

int createPidFile(const char *progName, const char *pidFile, int flags);

#endif
