import subprocess

# equivalent to bash $ echo charactersinword | wc -c
p = subprocess.Popen("wc -c", shell=True, stdin=subprocess.PIPE)
res = p.communicate("charactersinword".encode('utf-8'))


f = open('temp.txt', 'w')
f.write('charactersinword')
f.close()

f=open('temp.txt', 'r')
text = f.read()

p = subprocess.Popen("wc -c", shell=True, stdin=subprocess.PIPE)
res = p.communicate(text.encode('utf-8'))



subprocess.call("rm temp.txt", shell=True)


