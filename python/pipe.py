import subprocess

res = subprocess.Popen(['uname','-sv'], stdout=subprocess.PIPE)

uname = str(res.stdout.read())

print(uname)

print('Linux' in uname)

print(uname.index('Linux'))

print(uname.find('Linux'))
# print(uname.index('Darwin')) # will throw
print(uname.find('Darwin')) # -1


