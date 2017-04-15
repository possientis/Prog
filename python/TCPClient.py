from socket import *
serverName = 'left'
serverPort = 12000
clientSocket = socket(AF_INET, SOCK_STREAM)
clientSocket.connect((serverName, serverPort))
message = input('Input lowercase sentence:')
clientSocket.send(message.encode('utf-8'))
modifiedSentence = clientSocket.recv(1024).decode('utf8')
print(modifiedSentence)
clientSocket.close()
