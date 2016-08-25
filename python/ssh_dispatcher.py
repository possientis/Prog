import subprocess

"""
A ssh based command dispatching system

"""

machines = ["192.168.1.xxx", "192.168.1.xxx", "192.168.1.xxx"]
users = ["xxx", "xxx", "xxx"]

cmd = "ls -l"

for i in range(0,3):
    machine = machines[i]
    user = users[i]
    ssh = "ssh %s@%s %s" %(user, machine, cmd)
    subprocess.call(ssh, shell=True)
    



