#!/bin/sh

SRC=tests/spl/ftp
LIB=lib
OUT=ftpCcode

echo calling GRASShopper to produce the C files

mkdir -p $OUT

./grasshopper.native -v -bitvector $SRC/client.spl -compile $OUT/ftpClient.c
./grasshopper.native -v -bitvector $SRC/server.spl -compile $OUT/ftpServer.c

echo compiling the C files

opts='--std=gnu99'

gcc $opts -c $LIB/console.c    -o $OUT/console.o
gcc $opts -c $LIB/file.c       -o $OUT/file.o
gcc $opts -c $LIB/socket.c     -o $OUT/socket.o
gcc $opts -c $LIB/makeStr.c    -o $OUT/makeStr.o
gcc $opts -c $OUT/ftpClient.c  -o $OUT/ftpClient.o
gcc $opts -c $OUT/ftpServer.c  -o $OUT/ftpServer.o
gcc $OUT/console.o $OUT/file.o $OUT/socket.o $OUT/makeStr.o $OUT/ftpServer.o -o $OUT/ftpServer
gcc $OUT/console.o $OUT/file.o $OUT/socket.o $OUT/makeStr.o $OUT/ftpClient.o -o $OUT/ftpClient

