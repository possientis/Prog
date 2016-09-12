import threading
import time

# bad design, mutable shared state. no synchronisation
count = 1

class KissThread(threading.Thread):
    def run(self):
        global count
        print("Thread # %s: Pretending to do stuff" % count)
        count += 1
        time.sleep(2)
        print("done with stuff")



if __name__ == "__main__":
    for t in range(5):
        KissThread().start()


