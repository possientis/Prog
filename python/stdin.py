import sys

f = sys.stdin

print(type(f))

text = f.read() # type <enter> then ctrl+d to terminate input at runtime

print(text)


print(enumerate(sys.stdin))

for i,line in enumerate(sys.stdin):
    print(str(i) + str(line))
