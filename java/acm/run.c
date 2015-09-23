// run.c
// this is an attempt at translating the scripts run.sh and run.py in C
// as an exercise in using fork() and execve to call linux commands

#include <stdlib.h> // exit
#include <stdio.h>  // fprintf
#include <string.h> // strstr, strlen,strcpy, strcat
#include <malloc.h> // malloc, free
#include <assert.h> // assert
#include <unistd.h> // fork
#include <sys/wait.h> // wait

// these are defined below
static int cleanUpFile(char*);
static int compileFile(char*);
static int copyAcmAsFile(char*);
static int addToJarFile(char*, char*);
static int launchApplet(char*);


int main(int argc, char* argv[]){


  /* checking a single argument has been passed */
  if(argc != 2){
    fprintf(stderr, "Usage: %s filename[.java]\n",argv[0]);
    exit(EXIT_FAILURE);
  }

  /* length of filename argument */
  char* filename = argv[1];
  int length = strlen(filename);

  /* testing whether filename contains .java extension */
  char *ptr = strstr(filename,".java");
  if(ptr != NULL){ // .java extension is present
    filename[length-5] = '\0';
    length -= 5;
  }

  /* allocating various strings */
  char filename_class[length + 7];  // .class + /0
  strcpy(filename_class,filename);
  strcat(filename_class,".class");


  char filename_jar[length + 5];  // .jar + /0
  strcpy(filename_jar,filename);
  strcat(filename_jar,".jar");

  char filename_html[length + 6];  // .html + /0
  strcpy(filename_html,filename);
  strcat(filename_html,".html");

  char filename_java[length + 6];  // .java + /0
  strcpy(filename_java,filename);
  strcat(filename_java,".java");

  /* cleaning up previously created files, if any */
  cleanUpFile(filename_class);
  cleanUpFile(filename_jar);
  cleanUpFile(filename_html);

  /* compiling filename.java */
  compileFile(filename_java);

  /* copying acm.jar as filename.jar */
  copyAcmAsFile(filename_jar);

  /* adding filename.class to filename.jar */
  addToJarFile(filename_jar,filename_class);

  /* creating html file */
  FILE *f;
  f = fopen(filename_html,"w");
  fprintf(f,"<html><applet archive=%s code=%s ", filename_jar,filename_class);
  fprintf(f,"width=1000 height=600></applet></html>");
  fclose(f);

  /* launching applet */
  launchApplet(filename_html);

  /* final clean-up */
  cleanUpFile(filename_class);
  cleanUpFile(filename_jar);
  cleanUpFile(filename_html);

  exit(EXIT_SUCCESS);

}


/* wapper around execve to execute linux command 'rm -f filename' */
static int cleanUpFile(char* filename){

  /* various declaration needed to call fork and execve */
  char*  newEnv[] = {NULL};   // needed for exceve
  assert(newEnv[0] == NULL);  // do not trust anyone
  pid_t pid;  // needed to fork and launch linux command
  int status; // return status of child process

  /* preparing to use the rm command */
  char cmd[8]; strcpy(cmd,"/bin/rm");
  char flag[3]; strcpy(flag,"-f");    // does not complain if file does not exist
  char* const newArg[4] = {cmd,flag,filename,NULL};
  /* just in case */
  assert(strcmp(newArg[0],"/bin/rm") == 0);
  assert(strcmp(newArg[1],"-f") == 0);
  assert(strcmp(newArg[2],filename) == 0);
  assert(newArg[3] == NULL);

  /* creating child process */
  pid = fork();
  if(pid == 0){                 // child process
    execve(cmd,newArg,newEnv);  // launching linux command
    exit(EXIT_FAILURE);         // does not return from execve unless failure
  }
  else{                         // parent process
    assert(pid > 0);            // pid should be pid of child process
    wait(&status);              // waiting for child to complete, retrieving status
    if(status != 0){            // child process failed
        fprintf(stderr, "Failed to remove %s\n",filename);
        exit(EXIT_FAILURE);
    }
  }
}

/* wapper around execve to execute command 'javac -classpath acm.jar filename */
static int compileFile(char* filename){

  /* various declaration needed to call fork and execve */
  char*  newEnv[] = {NULL};   // needed for exceve
  assert(newEnv[0] == NULL);  // do not trust anyone
  pid_t pid;  // needed to fork and launch linux command
  int status; // return status of child process

  /* preparing to use the javac command */
  char cmd[15]; strcpy(cmd,"/usr/bin/javac");
  char flag[11]; strcpy(flag,"-classpath");
  char acm[8]; strcpy(acm,"acm.jar");
  char* const newArg[5] = {cmd,flag,acm,filename,NULL};

  /* just in case */
  assert(strcmp(newArg[0],"/usr/bin/javac") == 0);
  assert(strcmp(newArg[1],"-classpath") == 0);
  assert(strcmp(newArg[2],"acm.jar") == 0);
  assert(strcmp(newArg[3],filename) == 0);
  assert(newArg[4] == NULL);

  /* creating child process */
  pid = fork();
  if(pid == 0){                 // child process
    execve(cmd,newArg,newEnv);  // launching linux command
    exit(EXIT_FAILURE);         // does not return from execve unless failure
  }
  else{                         // parent process
    assert(pid > 0);            // pid should be pid of child process
    wait(&status);              // waiting for child to complete, retrieving status
    if(status != 0){            // child process failed
        fprintf(stderr, "Failed to compile %s\n",filename);
        exit(EXIT_FAILURE);
    }
  }
}


/* wapper around execve to execute linux command 'cp acm.jar filename */
static int copyAcmAsFile(char* filename){

  /* various declaration needed to call fork and execve */
  char*  newEnv[] = {NULL};   // needed for exceve
  assert(newEnv[0] == NULL);  // do not trust anyone
  pid_t pid;  // needed to fork and launch linux command
  int status; // return status of child process

  /* preparing to use the cp command */
  char cmd[8]; strcpy(cmd,"/bin/cp");
  char acm[8]; strcpy(acm,"acm.jar");
  char* const newArg[4] = {cmd,acm,filename,NULL};

  /* just in case */
  assert(strcmp(newArg[0],"/bin/cp") == 0);
  assert(strcmp(newArg[1],"acm.jar") == 0);
  assert(strcmp(newArg[2],filename) == 0);
  assert(newArg[3] == NULL);

  /* creating child process */
  pid = fork();
  if(pid == 0){                 // child process
    execve(cmd,newArg,newEnv);  // launching linux command
    exit(EXIT_FAILURE);         // does not return from execve unless failure
  }
  else{                         // parent process
    assert(pid > 0);            // pid should be pid of child process
    wait(&status);              // waiting for child to complete, retrieving status
    if(status != 0){            // child process failed
        fprintf(stderr, "Failed to copy acm.jar as %s\n",filename);
        exit(EXIT_FAILURE);
    }
  }
}

/* wapper around execve to execute command 'jar uf filename.jar filename.class */
static int addToJarFile(char* filename_jar, char* filename_class){

  /* various declaration needed to call fork and execve */
  char*  newEnv[] = {NULL};   // needed for exceve
  assert(newEnv[0] == NULL);  // do not trust anyone
  pid_t pid;  // needed to fork and launch linux command
  int status; // return status of child process

  /* preparing to use the javac command */
  char cmd[13]; strcpy(cmd,"/usr/bin/jar");
  char flag[3]; strcpy(flag,"uf");
  char* const newArg[5] = {cmd,flag,filename_jar,filename_class,NULL};

  /* just in case */
  assert(strcmp(newArg[0],"/usr/bin/jar") == 0);
  assert(strcmp(newArg[1],"uf") == 0);
  assert(strcmp(newArg[2],filename_jar) == 0);
  assert(strcmp(newArg[3],filename_class) == 0);
  assert(newArg[4] == NULL);

  /* creating child process */
  pid = fork();
  if(pid == 0){                 // child process
    execve(cmd,newArg,newEnv);  // launching linux command
    exit(EXIT_FAILURE);         // does not return from execve unless failure
  }
  else{                         // parent process
    assert(pid > 0);            // pid should be pid of child process
    wait(&status);              // waiting for child to complete, retrieving status
    if(status != 0){            // child process failed
        fprintf(stderr, "Failed to add %s to %s\n",filename_class,filename_jar);
        exit(EXIT_FAILURE);
    }
  }
}


/* wapper around execve to execute command 'appletviewer filename */
static int launchApplet(char* filename){

  /* various declaration needed to call fork and execve */
  char env[13]; strcpy(env,"DISPLAY=:0.0");
  char*  newEnv[2] = {env,NULL};   // need DISPLAY=:0.0 for appletviewer to work
  assert(strcmp(newEnv[0],"DISPLAY=:0.0") == 0);  // do not trust anyone
  assert(newEnv[1] == NULL);  // do not trust anyone
  pid_t pid;  // needed to fork and launch linux command
  int status; // return status of child process

  /* preparing to use the javac command */
  char cmd[22]; strcpy(cmd,"/usr/bin/appletviewer");
  char* const newArg[3] = {cmd,filename,NULL};

  /* just in case */
  assert(strcmp(newArg[0],"/usr/bin/appletviewer") == 0);
  assert(strcmp(newArg[1],filename) == 0);
  assert(newArg[2] == NULL);

  /* creating child process */
  pid = fork();
  if(pid == 0){                 // child process
    execve(cmd,newArg,newEnv);  // launching linux command
    exit(EXIT_FAILURE);         // does not return from execve unless failure
  }
  else{                         // parent process
    assert(pid > 0);            // pid should be pid of child process
    wait(&status);              // waiting for child to complete, retrieving status
    if(status != 0){            // child process failed
        fprintf(stderr, "Failed to launch applet %s\n",filename);
        exit(EXIT_FAILURE);
    }
  }
}




