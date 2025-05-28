# Use the official Ubuntu 22.04 base image
FROM mathcomp/mathcomp:1.19.0-coq-8.20
#
#RUN opam init -y 
#RUN eval $(opam env) 
#RUN opam repo add coq-released https://coq.inria.fr/opam/released
#RUN opam install coq-mathcomp-ssreflect.1.19.0 -y 
#RUN opam install vscoq-language-server -y 
#
USER vscode
RUN sudo vscode opam init -y 
RUN sudo vscode eval $(opam env) 
RUN sudo vscode opam repo add coq-released https://coq.inria.fr/opam/released
RUN sudo vscode opam install coq-mathcomp-ssreflect.1.19.0 -y 
RUN sudo vscode opam install vscoq-language-server -y 
#
# RUN apt-get update && export DEBIAN_FRONTEND=noninteractive && apt-get -y install --no-install-recommends 
#
#USER codespace
