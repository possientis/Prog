#ifndef TTY_FUNCTIONS_H
#define TTY_FUNCTIONS_H

/* Place terminal referred to by 'fd' in cbreak mode (noncanonical mode
 * with echoing turned off). This function assumes that the terminal is
 * currently in cooked mode (i.e., we shouldn't call it if the terminal
 * is currently in raw mode, since it does not undo all of the changes
 * made by the ttySetRaw() function below). Return 0 on success, or -1
 * on error. If 'prevTermios' is non-NULL, then use the buffer to which
 * it points to return the previous terminal settings. */

int ttySetCbreak(int fd, struct termios *prevTermios);



/* Place terminal referred to by 'fd' in raw mode (noncanonical mode
 * with all input and output processing disabled). Return 0 on success,
 * or -1 on error. If 'prevTermios' is non-NULL, then use the buffer to
 * which it points to return the previous terminal settings. */

int ttySetRaw(int fd, struct termios *prevTermios);


#endif
