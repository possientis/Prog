import subprocess

p = subprocess.Popen("tr a-z A-Z", shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

output, error = p.communicate("translatetoupper".encode('utf-8'))

print(output.decode('utf-8'))   # TRANSLATETOUPPER
