# see process_dispatch.py for an implementation based on processes
# rather than threads.

# some insight: always use threads with queue so you don't need 
# to worry about synchronization as the Queue class is thread safe.

from threading import Thread
from queue import Queue
import time
import random

num_threads = 10
num_jobs = 100
queue = Queue()

def threadFunc(i, q):
    while True:
        message = q.get()   # guessing this will block on empty queue
        print("Thread %s starting work on %s" % (i, message))
        delay = random.randint(0,5)
        time.sleep(delay)       # simulating work being done
        print("%s complete" % message)
        q.task_done()       # allows q.join() to unblock when all taks done
        # The count of unfinished tasks goes up whenever an item is added to the
        # queue. The count goes down whenever a consumer thread calls task_done()
        
def setWorkers():
    for i in range(num_threads):
        worker = Thread(target=threadFunc, args=(i,queue))
        # needs to be daemon threads, otherwise main program will not exit
        # after queue.join. 
        worker.setDaemon(True)
        worker.start()

def setJobs():
    for i in range(num_jobs):
        queue.put("job n. %s" % (i+1))

def synchronize(q):
    q.join()

print("Main thread starting")
print("Setting up jobs")
setJobs()
print("Launching workers")
setWorkers()
print("Main thread waiting")
synchronize(queue)
print("Main thread complete")


