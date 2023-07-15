FROM ubuntu

# Avoid confirmation messages
ARG DEBIAN_FRONTEND=noninterfactive

RUN apt update; apt upgrade -y

RUN apt install -y apache2 vim systemctl

RUN systemctl start apache2

ENTRYPOINT /bin/bash -D FOREGROUND

# start apache2 service
#ENTRYPOINT apache2ctl -D FOREGROUND

