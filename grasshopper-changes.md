# string

string as `Array<Int>`

predicate string(s) ⇔ array(s) ∧ ∀ i. s[i] ≥ 0 ∧ s[i] ≤ 255

do we want strings to be '\0' terminated or use the lenght of the array ?
do we want to support UTF8/16/32 (variable length encoding except for UFT32)

# Files

    int open(const char *pathname, int flags);
    int open(const char *pathname, int flags, mode_t mode);
    int creat(const char *pathname, mode_t mode);

    ssize_t read(int fildes, void *buf, size_t nbyte);
    ssize_t pread(int fildes, void *buf, size_t nbyte, off_t offset);

    ssize_t write(int fd, const void *buf, size_t count);
    ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset);

    int close(int fd);

# socket

## structs

    // IPv4 AF_INET sockets:
    struct sockaddr_in {
        short            sin_family;   // address family, AF_INET
        unsigned short   sin_port;     // e.g. htons(3490)
        struct in_addr   sin_addr;     // see struct in_addr, below
        char             sin_zero[8];  // zero this if you want to
    };
    struct in_addr {
       unsigned long s_addr;          // load with inet_pton()
    };

    // IPv6 AF_INET6 sockets:
    struct sockaddr_in6 {
        u_int16_t       sin6_family;   // address family, AF_INET6
        u_int16_t       sin6_port;     // port number, Network Byte Order
        u_int32_t       sin6_flowinfo; // IPv6 flow information
        struct in6_addr sin6_addr;     // IPv6 address
        u_int32_t       sin6_scope_id; // Scope ID
    };
    struct in6_addr {
        unsigned char   s6_addr[16];   // load with inet_pton()
    };

## utils method

    inet_pton(AF_INET,  "10.0.0.1",               &ip4addr.sin_addr );
    inet_pton(AF_INET6, "2001:db8:8714:3a90::12", &ip6addr.sin6_addr);

    int sock = socket(PF_INET,  SOCK_DGRAM,  IPPROTO_UDP);
    int sock = socket(PF_INET6, SOCK_STREAM, IPPROTO_TCP);

    int success = bind(sock, (struct sockaddr *)&sa,      sizeof sa);
    int success = bind(sock, (struct sockaddr *)&ip6addr, sizeof ip6addr);

    int getaddrinfo(const char *node,     // e.g. "www.example.com" or IP
                    const char *service,  // e.g. "http" or port number
                    const struct addrinfo *hints,
                    struct addrinfo **res);

## API

### Both

    int socket(int domain, int type, int protocol);
    int bind(int sockfd, struct sockaddr *my_addr, int addrlen);
    void close(int sockfd);

### TCP only

    int listen(int sockfd, int backlog);
    int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
    int connect(int sockfd, struct sockaddr *serv_addr, int addrlen);
    int send(int sockfd, const void *msg, int len, int flags); 
    int recv(int sockfd, void *buf, int len, int flags);

### UDP only

    int sendto(int sockfd, const void *msg, int len, unsigned int flags, const struct sockaddr *to, socklen_t tolen);
    int recvfrom(int sockfd, void *buf, int len, unsigned int flags, struct sockaddr *from, int *fromlen);
