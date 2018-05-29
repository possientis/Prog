#include <arpa/inet.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/stat.h>

#include "connect.h"
#include "rio.h"

#define MAXLINE 1024
#define MAXBUF  8192

void doit(int fd);
void read_requesthdrs (rio_t *rp);


void
clienterror
    ( int fd
    , const char *cause
    , const char *errnum
    , const char *shortmsg
    , const char *longmsg
    );

int 
parse_uri
    ( char *uri
    , char *filename
    , char *cgiargs
    );

void
serve_static
    ( int fd
    , const char *filename
    , int filesize
    );

void
serve_dynamic
    ( int fd
    , const char *filename
    , const char *cgiargs
    );


void
get_filetype
    ( const char *filename
    , char *filetype
    );

int main(int argc, char **argv)
{

    int listenfd, connfd, port, clientlen;
    struct sockaddr_in clientaddr;

    /* check command line args */
    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(1);
    }

    port = atoi (argv[1]);
    fprintf(stderr, "tiny server starting on port %d\n", port);

    if ((listenfd = open_listenfd(port)) < 0) {
        fprintf(stderr, "failed to set up listening socket on port %d\n", port);
        exit(1);
    }
    else {
        fprintf(stderr, "listening socket successfully set up\n");
    }

    while (1) {

        clientlen = sizeof(clientaddr);
        fprintf(stderr, "server blocking, awaiting client connection\n");
        if ((connfd = accept(listenfd, (SA *)&clientaddr, &clientlen)) < 0) {
                fprintf(stderr,"failed to accept connections on port %d\n", port);
                exit(1);
        }
        else {
            fprintf(stderr, "client connection established\n");
        }
        

        fprintf(stderr, "processing client request\n");
        doit(connfd);
        fprintf(stderr, "client request complete\n");

        if(close(connfd) < 0) {
            fprintf(stderr, "failed to close connection on port %d\n", port);
            exit(1);
        }
        else {
            fprintf(stderr, "closing client connection\n");
        }

    }

}


void doit(int fd)
{
    int             is_static;
    struct stat     sbuf;
    rio_t           rio;

    char            buf         [MAXLINE];
    char            method      [MAXLINE];
    char            uri         [MAXLINE];
    char            version     [MAXLINE];
    char            filename    [MAXLINE];
    char            cgiargs     [MAXLINE];

    /* read request line and header */
    rio_readinitb(&rio, fd);
    if (rio_readlineb(&rio, buf, MAXLINE) < 0) {
        fprintf(stderr, "failed to read line from client\n");
        exit(1);
    }
    sscanf(buf, "%s %s %s", method, uri, version);
    if (strcasecmp(method, "GET")) {
        clienterror(fd,method,"501", "Not implemented", 
                "Tiny does not implement this method");
        return;
    }

    read_requesthdrs(&rio);

    /* parse uri from GET request */
    is_static = parse_uri(uri, filename, cgiargs);
    if(stat(filename, &sbuf) < 0) {
        clienterror(fd, filename, "404", "Not found",
                    "Tiny couldn't find this file");
        return;
    }

    if(is_static) { /* serve static content */
        if(!(S_ISREG(sbuf.st_mode)) || !(S_IRUSR & sbuf.st_mode)) {
            clienterror(fd, filename, "403", "Forbidden",
                        "Tiny coudn't read this file");
            return;
        }
        serve_static(fd,filename,sbuf.st_size);
    }
    else { /* serve dynamic content */
        if(!(S_ISREG(sbuf.st_mode)) || !(S_IXUSR & sbuf.st_mode)) {
            clienterror(fd, filename, "403", "Forbidden",
                        "Tiny couldn't run the CGI program");
            return;
        }
        serve_dynamic(fd, filename, cgiargs);
    }


}

void
clienterror
    ( int fd
    , const char *cause
    , const char *errnum
    , const char *shortmsg
    , const char *longmsg
    )
{
    char buf[MAXLINE], body[MAXBUF];

    /* build the HTTP response body */
    sprintf(body,"<html><title>Tiny Error</title>");
    sprintf(body,"%s<body bgcolor=""ffff"">\r\n",body);
    sprintf(body,"%s%s: %s\r\n", body, errnum, shortmsg);
    sprintf(body,"%s<p>%s: %s\r\n", body, longmsg, cause);
    sprintf(body,"%s<hr><em>The Tiny Web server</em>\r\n", body);

    /* print the HTTP response */
    sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
    rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-type: text/html\r\n");
    rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
    rio_writen(fd, buf, strlen(buf));
    rio_writen(fd, body, strlen(body));
}


void read_requesthdrs (rio_t *rp)
{
}

int 
parse_uri
    ( char *uri
    , char *filename
    , char *cgiargs
    )
{
    return 0;
}


void
serve_static
    ( int fd
    , const char *filename
    , int filesize
    )
{
}

void
serve_dynamic
    ( int fd
    , const char *filename
    , const char *cgiargs
    )
{
}

void
get_filetype
    ( const char *filename
    , char *filetype
    )
{
}


