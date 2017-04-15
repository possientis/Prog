from socket import *
serverPort = 12000
serverSocket = socket(AF_INET, SOCK_STREAM)
serverSocket.bind(('',serverPort))
serverSocket.listen(1)
print("The server is ready to receive")
while True:
    connectionSocket, addr = serverSocket.accept()
    message = connectionSocket.recv(1024).decode('utf-8')
    modifiedSentence = message.upper()
    connectionSocket.send(modifiedSentence.encode('utf-8'))
    connectionSocket.close()

