from multiprocessing import Process, Queue
import time

def f(q):
    x = q.get()
    print("Process number %s, sleeps for %s seconds" % (x,x))
    time.sleep(x)
    print("Process number %s finished" % x)


q = Queue()

for i in range(10):
    q.put(i)
    i = Process(target=f, args=[q])
    i.start()


print("Main process joins on queue")
i.join() # ????
print("Main process finished")

