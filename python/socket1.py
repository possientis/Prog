import socket

# creating socket object
mysock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

# connecting
mysock.connect(('www.py4inf.com', 80))

# send request (note the two newlines)
request='GET http://www.py4inf.com/code/romeo.txt HTTP/1.0\n\n'.encode('UTF-8')
mysock.send(request)


while True:
    data = mysock.recv(512)
    if ( len(data) < 1 ) :
        break
    print(data.decode('UTF-8'))

mysock.close()

# Note that you can achieve the same thing manually using telnet
# $ telnet www.py4inf.com 80
#
# Trying 2607:f1c0:1000:70e5:e1b4:a0e:2466:c040...
# Trying 216.250.120.69...
# Connected to www.py4inf.com.
# Escape character is '^]'.

# GET http://www.py4inf.com/code/romeo.txt HTTP/1.0 
# type <Enter> twice

# HTTP/1.1 200 OK
# Content-Type: text/plain
# Content-Length: 167
# Connection: close
# Date: Wed, 25 Jan 2017 18:25:15 GMT
# Server: Apache
# Last-Modified: Fri, 04 Dec 2015 19:05:04 GMT
# ETag: "a7-526172f5b5d89"
# Accept-Ranges: bytes
# Cache-Control: max-age=604800, public
# Access-Control-Allow-Origin: *
# Access-Control-Allow-Headers: origin, x-requested-with, content-type
# Access-Control-Allow-Methods: GET
# 
# But soft what light through yonder window breaks
# It is the east and Juliet is the sun
# Arise fair sun and kill the envious moon
# Who is already sick and pale with grief
#
# Connection closed by foreign host.
