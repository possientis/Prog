if True:
    print("True is considered true")
if False:
    pass
else:
    print("False is considered false")

if None:
    pass
else:
    print("None is considered false")

if 345:
    print("A non zero number is considered true")

if 0:
    pass
else:
    print("0 is considered false")

if "some string":
    print("A non-empty string is considered true")

if "":
    pass
else:
    print("The empty string is considered false")

