# this is for python 2

from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
import logging
import json

logging.basicConfig()
logging.getLogger("BitcoinRPC").setLevel(logging.DEBUG)

username = 'bitcoinrpc'
password = 'xxx'
url = "http://%s:%s@127.0.0.1:8332" % (username, password)

rpc_connection = AuthServiceProxy(url)
print(rpc_connection.getinfo())
