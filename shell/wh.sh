#!/bin/bash

# Does a 'whois domain-name' lookup on any 3 alternate servers:
#                    ripe.net, cw.net, radb.net
#
# place this script -- renamed 'wh' -- in /usr/local/bin

# Requires symbolic links:
# ln -s /usr/local/bin/wh /usr/local/bin/wh-ripe
# ln -s /usr/local/bin/wh /usr/local/bin/wh-apnic
# ln -s /usr/local/bin/wh /usr/local/bin/wh-tucows

E_NOARGS=75

if [ -z "$1" ]
then
  echo "Usage: `basename $0` [domain-name]"
  exit $E_NOARGS
fi

# Check script name and call proper server
case `basename $0` in   # or case ${0##*/} in
  "wh"        ) whois $1@whois.cw.net;;
  "wh-ripe"   ) whois $1@whois.ripe.net;;     
  "wh-apnic"  ) whois $1@whois.apnic.net;;
  "wh-tucows" ) whois $1@whois.tucows.com;;
  *           ) echo "This should not happen";;
esac

exit $?
