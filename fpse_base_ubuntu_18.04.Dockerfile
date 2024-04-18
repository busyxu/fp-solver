FROM ubuntu:18.04

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        binutils \
        cmake \
        curl \
        ca-certificates \
        gcc-multilib \
        gcc-5-multilib \
        git \
        g++-multilib \
        g++-5-multilib \
        libgmp-dev \
        libgomp1 \
        libomp5 \
        libomp-dev \
        make \
        ninja-build \
        python3 \
        python3-setuptools \
        sudo && \
    apt-get clean && \
    ln -s /usr/bin/python3 /usr/bin/python

# Create `aaa` user for container with password `123`.  and give it
# password-less sudo access
RUN useradd -m aaa && \
    echo aaa:123 | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'aaa  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER aaa
WORKDIR /home/aaa
