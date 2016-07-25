import xml.etree.ElementTree as ET
# two other xml parsing libraries are sax and dom

tcusers = ET.parse("etree.xml")

print(tcusers)
print(repr(tcusers))


first_user = tcusers.find('./user')
print(first_user)
print(first_user.attrib)
print(first_user.get('name'))

list_users = tcusers.findall('./user')
print(list_users)

for user in [e for e in list_users if e.get('name') == 'tomcat']:
    print(user.attrib)
