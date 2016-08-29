import subprocess
import configparser
from threading import Thread
from queue import Queue
import time

"""
A threaded ssh-based command dispatch system

"""

def readConfig(file="dispatcher.conf"):
    """Extract IP addresss and commands from config file and returns tuple """

    parser = configparser.ConfigParser()
    parser.read(file)
    machines = parser.items("MACHINES")
    commands = parser.items("COMMANDS")

    return machines, commands

def launcher(i, q):
    """Spawns command in a thread to an ip"""
    while True:
        # grap machine from queue
        machine, command = q.get()
        user, ip = machine
        name, cmd = command
        ssh = "ssh %s@%s %s" %(user, ip, cmd)
        print("Thread %s: Running %s on %s's machine (ip %s)" % (i, cmd, user, ip))
        subprocess.call(ssh, shell=True)
        q.task_done()


if __name__ == "__main__":

    start = time.time()
    queue = Queue()

    machines, commands = readConfig()
    print("machines = %s" % machines)
    print("commands = %s" % commands)

    num_threads = 5

    # start thread pool
    for i in range(num_threads):
        worker = Thread(target=launcher, args=(i,queue))
        worker.setDaemon(True)
        worker.start()

    print("Main Thread Waiting")
    for machine in machines:
        for command in commands:
            queue.put((machine, command))

    queue.join()
    end = time.time()

    print("Dispatch Completed in %s seconds" % (end - start))





    
