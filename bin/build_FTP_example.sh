#!/bin/sh

SRC=tests/spl/ftp
LIB=lib
OUT=ftpCcode

echo calling GRASShopper to produce the C files

mkdir -p $OUT

./grasshopper.native -v -bitvector $SRC/client.spl -compile $OUT/ftpClient.c
./grasshopper.native -v -bitvector $SRC/server.spl -compile $OUT/ftpServer.c

echo compiling the C files

gcc -c ${1} $LIB/console.c    -o $OUT/console.o
gcc -c ${1} $LIB/file.c       -o $OUT/file.o
gcc -c ${1} $LIB/socket.c     -o $OUT/socket.o
gcc -c ${1} $LIB/makeStr.c    -o $OUT/makeStr.o
gcc -c ${1} $OUT/ftpClient.c  -o $OUT/ftpClient.o
gcc -c ${1} $OUT/ftpServer.c  -o $OUT/ftpServer.o
gcc ${1} $OUT/console.o $OUT/file.o $OUT/socket.o $OUT/makeStr.o $OUT/ftpServer.o -o $OUT/ftpServer
gcc ${1} $OUT/console.o $OUT/file.o $OUT/socket.o $OUT/makeStr.o $OUT/ftpClient.o -o $OUT/ftpClient

