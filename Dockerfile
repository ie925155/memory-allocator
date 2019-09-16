
FROM ubuntu:16.04
MAINTAINER Sheldon Lai <ie925155@gmail.com>

RUN \
	apt-get update && \
	apt-get -y install gcc libc-dev perl gdb make xz-utils vim wget

RUN wget --timeout=30 http://releases.llvm.org/7.0.0/clang+llvm-7.0.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz
RUN mkdir -p /usr/local/depot/llvm-7.0; tar Jxvf clang+llvm-7.0.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz \
  --transform s/clang+llvm-7.0.0-x86_64-linux-gnu-ubuntu-16.04/llvm-7.0/ -C /usr/local/depot/
RUN rm clang+llvm-7.0.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz
