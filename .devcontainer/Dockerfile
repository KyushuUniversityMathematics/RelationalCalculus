# Use the official Ubuntu 22.04 base image
FROM mathcomp/mathcomp:1.19.0-coq-8.20
#
RUN opam init -y 
RUN eval $(opam env) 
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install coq-mathcomp-ssreflect.1.19.0 -y 
RUN opam install vscoq-language-server -y 
# RUN coq_makefile -f _CoqProject -o Makefile 
# RUN make
CMD ["/bin/bash"]
