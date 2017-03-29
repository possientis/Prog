#ifndef INCLUDE_HACKING_NETWORK_H
#define INCLUDE_HACKING_NETWORK_H

/* This function accepts a socket FD and a ptr to the null terminated
 * string to send. The function will make sure all the bytes of the
 * string are sent. Returns 1 on success and 0 on failure.
 */ 
int send_string(int sockfd, const unsigned char *buffer);


/* This function accepts a socket FD and a ptr to a destination
 * buffer. It will receive from the socket until the EOL byte
 * sequence in seen. The EOL bytes are read from the socket, but
 * the destination buffer is terminated before these bytes.
 * Returns the size of the read line (without EOL bytes). 
 */ 
int recv_line(int sockfd, unsigned char *dest_buffer); 


#define ETHER_ADDR_LEN 6
#define ETHER_HDR_LEN 14

struct ether_hdr {
  unsigned char ether_dest_addr[ETHER_ADDR_LEN];  // Destination MAC address
  unsigned char ether_src_addr[ETHER_ADDR_LEN];   // Source MAC address
  unsigned short ether_type;                      // Type of Ethernet packet
} __attribute__((packed));                        // no padding?

#endif


struct ip_hdr {
  unsigned char ip_version_and_header_length;     // Version and header length
  unsigned char ip_tos;                           // Type of service
  unsigned short ip_len;                          // Total length
  unsigned short ip_id;                           // Identification number
  unsigned short ip_frag_offset;                  // Fragment offset and flags
  unsigned char ip_ttl;                           // Time to live
  unsigned char ip_type;                          // Protocol type
  unsigned short ip_checksum;                     // Checksum
  unsigned int ip_src_addr;                       // Source IP address
  unsigned int ip_dest_addr;                      // Destination IP address
};


// Assuming little-endian host
struct tcp_hdr {
  unsigned short tcp_src_port;                    // Source TCP port
  unsigned short tcp_dest_port;                   // Destination TCP port
  unsigned int tcp_seq;                           // TCP sequence number
  unsigned int tcp_ack;                           // TCP acknowledgment number
  unsigned char reserved:4;                       // 4 bits from the 6 bits
  unsigned char tcp_offset:4;                     // TCP data offset 
  unsigned char tcp_flags;                        // TCP flags (and 2 bits)
#define TCP_FIN   0x01
#define TCP_SYN   0x02
#define TCP_RST   0x04
#define TCP_PUSH  0x08
#define TCP_ACK   0x10
#define TCP_URG   0x20
  unsigned short tcp_window;                      // TCP window size
  unsigned short tcp_checksum;                    // TCP checksum
  unsigned short tcp_urgent;                      // TCP urgent pointer
};

















