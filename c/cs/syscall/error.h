#ifndef ERROR_INCLUDE_H
#define ERROR_INCLUDE_H
void unix_error(const char* msg);
pid_t Fork(void);
char* Fgets(char* s, int size, FILE *stream);
#endif
