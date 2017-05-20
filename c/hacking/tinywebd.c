#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <fcntl.h>
#include <time.h>
#include <signal.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "hacking.h"
#include "hacking-network.h"

#define PORT 80                         // The port users will be connecting to
#define WEBROOT "./webroot"             // The webserver's root directory
#define LOGFILE "/var/log/tinywebd.log" // Log filename

int logfd, sockfd;                      // Global log and socket file descriptors
void handle_connection(int, struct sockaddr_in *, int logfd);
int get_file_size(int); // Returns the filesize of open file descriptor
void timestamp(int);    // Writes a time stamp to open file descriptor

// Called when process is killed
void handle_shutdown(int signal) {
  timestamp(logfd);
  write(logfd, "Shutting down.\n", 15);
  close(logfd);
  close(sockfd);
  exit(0);
}

int main(void) {
  int new_sockfd, yes=1;
  struct sockaddr_in host_addr, client_addr;  // My address information
  socklen_t sin_size;

  logfd = open(LOGFILE, O_WRONLY|O_CREAT|O_APPEND, S_IRUSR|S_IWUSR);
  if(logfd == -1)
    fatal("opening log file");

  if ((sockfd = socket(PF_INET, SOCK_STREAM, 0)) == -1)
    fatal("in socket");

  if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(int)) == -1)
    fatal("setting socket option SO_REUSEADDR");

  printf("Starting tiny web daemon.\n");
  if(daemon(1, 0) == -1) // Fork to a background daemon process.
    fatal("forking to daemon process");

  signal(SIGTERM, handle_shutdown); // Call handle_shutdown when killed.
  signal(SIGINT, handle_shutdown);  // Call handle_shutdown when interrupted.

  timestamp(logfd);
  write(logfd, "Starting up.\n", 13);

  host_addr.sin_family = AF_INET;
  host_addr.sin_port = htons(PORT);       // host to network byte order
  host_addr.sin_addr.s_addr = INADDR_ANY; // automatically fill in with my IP
  memset(&(host_addr.sin_zero), '\0', 8); // zero the rest of the struct

  if (bind(sockfd, (struct sockaddr *)&host_addr, sizeof(struct sockaddr)) == -1)
    fatal("binding to socket");

  if (listen(sockfd, 20) == -1)
    fatal("listening on socket");

  while(1) { // Accept loop.
    sin_size = sizeof(struct sockaddr_in);
    new_sockfd = accept(sockfd, (struct sockaddr *)&client_addr, &sin_size);
    if(new_sockfd == -1)
      fatal("accepting connection");

    handle_connection(new_sockfd, &client_addr, logfd);
  }

  return 0;
}

/* This function handles the connection on the passed socket from the
 * passed client address. The connection is processed as a web request,
 * and this function replies over the connected socket. Finally, the
 * passed socket is closed at the end of the function.
 */

void 
handle_connection(int sockfd, struct sockaddr_in *client_addr_ptr, int logfd) {

  unsigned char *ptr, request[500], resource[500], log_buffer[500];
  int fd, length;

  length = recv_line(sockfd, request);

  sprintf(log_buffer, "From %s:%d \"%s\"\t", 
      inet_ntoa(client_addr_ptr->sin_addr),
      ntohs(client_addr_ptr->sin_port), request);

  ptr = strstr(request, " HTTP/"); // Search for valid-looking request.
  if(ptr == NULL) { // Then this isn't valid HTTP.
    strcat(log_buffer, " NOT HTTP!\n");
  } else {
    *ptr = 0;   // Terminate the buffer at the end of the URL.
    ptr = NULL; // Set ptr to NULL (used to flag for an invalid request).
    if(strncmp(request, "GET ", 4) == 0) // GET request
      ptr = request+4; // ptr is the URL.
    if(strncmp(request, "HEAD ", 5) == 0) // HEAD request
      ptr = request+5; // ptr is the URL.
    if(ptr == NULL) { // Then this is not a recognized request.
        strcat(log_buffer, "\tUNKNOWN REQUEST!\n");
    } else { // Valid request, with ptr pointing to the resource name
        if (ptr[strlen(ptr) - 1] == '/')    // For resources ending with '/',
          strcat(ptr, "index.html");        // add 'index.html' to the end.
          strcpy(resource, WEBROOT);        // Begin resource with web root path
          strcat(resource, ptr);            // and join it with resource path.
          fd = open(resource, O_RDONLY, 0); // Try to open the file.
          if(fd == -1) {                    // If file is not found
            strcat(log_buffer, " 404 Not Found\n");
            send_string(sockfd, "HTTP/1.0 404 NOT FOUND\r\n");
            send_string(sockfd, "Server: Tiny webserver\r\n\r\n");
            send_string(sockfd, "<html><head><title>404 Not Found</title></head>");
            send_string(sockfd, "<body><h1>URL not found</h1></body></html>\r\n");
          } else {  // Otherwise, serve up the file.
            strcat(log_buffer, " 200 OK\n");
            send_string(sockfd, "HTTP/1.0 200 OK\r\n");
            send_string(sockfd, "Server: Tiny webserver\r\n\r\n");
            if(ptr == request + 4) { // Then this is a GET request
              if( (length = get_file_size(fd)) == -1)
                fatal("getting resource file size");
              if( (ptr = (unsigned char *) malloc(length)) == NULL)
                fatal("allocating memory for reading resource");
              read(fd, ptr, length); // Read the file into memory.
              send(sockfd, ptr, length, 0); // Send it to socket.
              free(ptr); // Free file memory.
            }
            close(fd); // Close the file.
          } // End if block for file found/not found.
    } // End if block for valid request.
  } // End if block for valid HTTP.
  timestamp(logfd);
  length=strlen(log_buffer);
  write(logfd, log_buffer, length);

  shutdown(sockfd, SHUT_RDWR); // Close the socket gracefully.
}

/* This function accepts an open file descriptor and returns
 * the size of the associated file. Returns -1 on failure.
 */
int get_file_size(int fd) {
  struct stat stat_struct;
  if(fstat(fd, &stat_struct) == -1)
    return -1;

  return (int) stat_struct.st_size;
}

/* This function writes a timestamp string to the open file descriptor
 * passed to it.
 */
void timestamp(int fd) {
  time_t now;
  struct tm *time_struct;
  int length;
  char time_buffer[40];
  time(&now); // Get number of seconds since epoch.
  time_struct = localtime((const time_t *)&now); // Convert to tm struct.
  length = strftime(time_buffer, 40, "%m/%d/%Y %H:%M:%S> ", time_struct);
  write(fd, time_buffer, length); // Write timestamp string to log.
}





