import shelve

d = shelve.open('example.s')

print(dict(d))  # {}

d['key'] = 'some value'


print(dict(d))  # {'key': 'some value'}

d.close()

d2 = shelve.open('example.s')

print(dict(d2)) # {'key': 'some value'}

