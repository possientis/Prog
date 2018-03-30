#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

#include "syscall/error.h"


#define MAXARGS 128
#define MAXLINE 8192

/* Function prototypes */
void eval(const char *cmdline);
int parseline(const char *buf, char* argv[]);
int builtin_command(const char *argv[]);


int main()
{
    char cmdline[MAXLINE]; /* command line */

    while(1) {
        /* Read */
        printf("> ");
        Fgets(cmdline,MAXLINE,stdin);
        if(feof(stdin))
            exit(0);

        /* Evaluate */
        eval(cmdline);
    }
}

void eval(const char *cmdline)
{
    char *argv[MAXARGS];    /* argument list execve() */
    char buf[MAXLINE];      /* holds modified command line */
    int bg;                 /* job run in background or not */
    pid_t pid;              /* process id */

    strcpy(buf,cmdline);
    bg = parseline(buf,argv);
    if(argv[0] == NULL)
        return;             /* ignore empty line */

    if(!builtin_command(argv)) {
        if ((pid = Fork()) == 0) {  /* child run user job */
            if(execve(argv[0], argv, environ) < 0) {
                fprintf(stderr,"%s: Command not found.\n",argv[0]);
                exit(0);
            }
        }

        /* parent waits for foreground job to terminate */
        if(!bg) {
            int status;
            if(waitpid(pid, &status, 0) < 0)
                unix_error("waitfg: waitpid error");
        }
        else {
            printf("%d %s", pid, cmdline);
        }
    }

    return;
}

int builtin_command(const char *argv[])
{
    if(!strcmp(argv[0],"quit")) /* quit command */
        exit(0);                /* command interpreted */

    if(!strcmp(argv[0],"&"))    /* ignore singleton & */
        return 1                /* command does nothing */

}


/* parse the command line and build the argv array */
int parseline(const char *buf, char* argv[])
{


}







