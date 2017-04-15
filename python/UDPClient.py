from socket import *

serverName = 'left'
serverPort = 12000
clientSocket = socket(AF_INET,SOCK_DGRAM)
message = input('Input a lowercase sentence:')
clientSocket.sendto(message.encode('utf-8'), (serverName, serverPort))
modifiedMessage, serverAddress = clientSocket.recvfrom(2048)
print(modifiedMessage.decode('utf-8'))
clientSocket.close()
