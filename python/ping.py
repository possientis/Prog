import subprocess

ret = subprocess.call("ping -c 1 192.168.0.1",
                        shell=True,
                        stdout=open('/dev/null', 'w'),
                        stderr=subprocess.STDOUT)

print(ret)
