#!/usr/bin/python3

for element in [1,2,3]:
    print(element)

for element in (1,2,3):
    print(element)

for key in {'one':1,'two':2}:
    print(key)

for char in '123':
    print(char)

for line in open("exception.py"):
    print(line, end='')

class Reverse:
    def __init__(self,data):
        self.data = data
        self.index = len(data)  # so len(data) needs to make sense

    def __iter__(self): # returns iterator object (something with a __next__)
        return self     # just need to make sure self has an implemented __next__
    def __next__(self):
        if self.index == 0:
            raise StopIteration
        self.index = self.index - 1
        return self.data[self.index]    # so operator[] defined for data

rev = Reverse('spam')
print (repr(iter(rev)))
for char in rev:
    print(char)

