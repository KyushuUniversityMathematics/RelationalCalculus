# Use the official Ubuntu 22.04 base image
FROM mathcomp/mathcomp:1.19.0-coq-8.20
#
#RUN opam init -y 
#RUN eval $(opam env) 
#RUN opam repo add coq-released https://coq.inria.fr/opam/released
#RUN opam install coq-mathcomp-ssreflect.1.19.0 -y 
#RUN opam install vscoq-language-server -y 
#
#
# Docker from DockerするためにDockerをインストールします
RUN curl -fsSL https://get.docker.com | sh
# たとえばNode.jsのプロジェクトならここで開発用コンテナにもインストールしておく
RUN curl -Ls https://deb.nodesource.com/setup_18.x | bash
RUN apt update && apt install -y nodejs
#
# 実際に開発に使うroot以外のユーザーを作成します
RUN useradd -m user
# dockerコマンドを上記のroot以外のユーザーでも使えるようにするためにグチャグチャやってます
ARG NONROOT_USER=user
RUN echo "#!/bin/sh\n\
    sudoIf() { if [ \"\$(id -u)\" -ne 0 ]; then sudo \"\$@\"; else \"\$@\"; fi }\n\
    SOCKET_GID=\$(stat -c '%g' /var/run/docker.sock) \n\
    if [ \"${SOCKET_GID}\" != '0' ]; then\n\
        if [ \"\$(cat /etc/group | grep :\${SOCKET_GID}:)\" = '' ]; then sudoIf groupadd --gid \${SOCKET_GID} docker-host; fi \n\
        if [ \"\$(id ${NONROOT_USER} | grep -E \"groups=.*(=|,)\${SOCKET_GID}\(\")\" = '' ]; then sudoIf usermod -aG \${SOCKET_GID} ${NONROOT_USER}; fi\n\
    fi\n\
    exec \"\$@\"" > /usr/local/share/docker-init.sh \
    && chmod +x /usr/local/share/docker-init.sh
#
ENTRYPOINT [ "/usr/local/share/docker-init.sh" ]
CMD [ "sleep", "infinity" ]
