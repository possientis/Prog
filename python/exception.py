#!/usr/bin/python3

class B(Exception):
    pass
class C(B):
    pass
class D(C):
    pass

for cls in [B,C,D]:
    try:
        raise cls()
    except D:
        print("D")
    except C:
        print("C")
    except B:
        print("B")

print("Out of exception handling")
