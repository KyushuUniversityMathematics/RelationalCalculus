# Use the official Ubuntu 22.04 base image
FROM ubuntu:22.04
#
RUN apt-get update
#
RUN apt-get install -y tzdata
RUN ln -sf /usr/share/zoneinfo/Asia/Tokyo /etc/localtime
#
RUN apt-get -qqy install software-properties-common git make m4 aspcud ocaml opam
RUN apt-get clean
RUN rm -rf /var/lib/apt/lists/*
RUN opam init --compiler=4.05.0 --yes --auto-setup
RUN eval `opam config env`
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam pin add coq 8.5.3 --yes
RUN opam pin add coq-mathcomp-ssreflect 1.6.4 --yes 
