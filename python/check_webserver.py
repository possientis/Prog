import socket
import re
import sys

def check_webserver(address, port, resource):
    #build up HTTP request string
    if not resource.startswith('/'):
        resource = '/' + resource
    request_string = "GET %s HTTP/1.1\r\nHost: %s\r\n\r\n" % (resource, address)
    print('HTTP request:')
    print('|||%s|||' % request_string)

    # create TCP socket
    s = socket.socket()
    print("Attempting to connect to %s on port %s" % (address, port))
    try:
        s.connect((address, port))
        print("Connected to %s on port %s" % (address, port))
        s.send(bytes(request_string, 'UTF-8'))
        # we should only need the first 100 bytes or so
        rsp = s.recv(100)
        print('Received 100 bytes of HTTP response')
        print('|||%s|||' % rsp)
    except socket.error as e:
        print("Connection to %s on port %s failed: %s" % (address, port, e))
        return False
    finally:
        # be a good citizen
        print("Closing the connection")
        s.close()
    lines = rsp.splitlines()
    print("First line of HTTP response: %s" % lines[0])
    try:
        version, status, message = re.split(r'\s+', str(lines[0]),2)
        print('Version: %s, Status: %s, Message: %s' % (version, status, message))
    except ValueError:
        print('Failed to split status line')
        return False
    if status in ['200', '300']:
        print('Success - status was %s' % status)
        return True
    else:
        print("Status was %s" % status)
        return False



check_webserver('127.0.0.1', 80, '/')
