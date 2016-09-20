# see thread_dispatch.py for an implementation based on threads
# rather than new processes.

from multiprocessing import Process, Queue, Pool
import time
import random
import sys

num_proc = 10
num_jobs = 100
queue = Queue()

def procFunc(i, q):
    while True:
        if q.empty():
            sys.exit()
        message = q.get()
        print("Process %s starting work on %s" %(i, message))
        delay = random.randint(0,5)
        time.sleep(delay)               # simulating work being done
        print("%s complete" % message)

def setWorkers():
    seq = {}
    for i in range(num_proc):
        worker = Process(target=procFunc, args=[i,queue])
        worker.start()
        seq[i] = worker
    return seq

        

def setJobs():
    for i in range(num_jobs):
        queue.put("job n. %s" % (i+1))

def synchronize(seq):
    for i in range(num_proc):
        seq[i].join()

print("Main thread starting")
print("Setting up jobs")
setJobs()
print("Launching workers")
seq = setWorkers()
print("Main process waiting")
synchronize(seq)
print("Main process complete")




