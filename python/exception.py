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
    except D as e:
        print("D: %s" % e)
    except C as e:
        print("C: %s" % e)
    except B as e:
        print("B: %s" % e)

print("Out of exception handling")
