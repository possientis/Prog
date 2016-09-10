# Attempting to replicate the bash command:
# $ cat /etc/passwd | grep 0:0 | cut -d ':' -f 7 > temp.txt
# (which returns /bin/bash written to file temp.txt) with python piping


import subprocess

f = open('temp.txt', 'w')

p1 = subprocess.Popen("cat /etc/passwd", shell=True, stdout=subprocess.PIPE)
p2 = subprocess.Popen("grep 0:0", shell=True, stdin = p1.stdout, stdout=subprocess.PIPE)
p3 = subprocess.Popen("cut -d ':' -f 7", shell=True, stdin=p2.stdout, stdout=f)

f.close()

subprocess.call('rm temp.txt', shell=True)

# remember than you do not always need to use 'subprocess'
import pwd
print(pwd.getpwnam('root'))
shell = pwd.getpwnam('root')[-1]
print(shell)    # /bin/bash




