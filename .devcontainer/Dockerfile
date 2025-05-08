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
#
RUN opam init -y 
RUN eval $(opam env) 
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install coq-mathcomp-ssreflect.1.19.0 -y 
RUN opam install vscoq-language-server -y 
RUN coq_makefile -f _CoqProject -o Makefile 
RUN make
   
