# client code, server code needs to be running in background
# python3 xmlrpc_server.py &

import xmlrpc.client

server = xmlrpc.client.ServerProxy('http://localhost:8765')

# A function called 'ls' has been registered with the xmlrpc server

print(server)

result = server.ls('.') # rpc call generates output

print("here is the result obtain from rpc call:")
print(result)


