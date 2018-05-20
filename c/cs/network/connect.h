typedef struct sockaddr SA;


int open_clientfd(const char *hostname, int port);
int open_listenfd(int port);
