# this will not work under python3
import pika
params = pika.ConnectionParameters(host = '127.0.0.1')
connection = pika.BlockingConnection(params)
channel = connection.channel()
channel.queue_declare(queue = 'hello')
print " [*] Waiting for messages. To exit press CTRL+C"

def callback(ch, method, properties, body):
    print " [x] Received " + body

channel.basic_consume(callback, queue='hello', no_ack=True)
channel.start_consuming()
