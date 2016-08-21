# netsnmp only for python2
# Use another snmp library for python3 such as pysnmp

# ok this fails even under python2
import netsnmp

oid = netsnmp.Varbind('sysDescr')

result = netsnmp.snmpwalk(
        oid, 
        Version = 2, 
        DestHost = "localhost", 
        Community = "public"
)




