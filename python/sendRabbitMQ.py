# this will not work under python3
import pika
params = pika.ConnectionParameters(host = '127.0.0.1')
connection = pika.BlockingConnection(params)
channel = connection.channel()
channel.queue_declare(queue = 'hello')
channel.basic_publish(exchange='', routing_key='hello', body='hello world!')
print " [x] Sent 'hello world!' "
connection.close()

