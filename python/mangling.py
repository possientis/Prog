#!/usr/bin/python3

class Mapping:
    def __init__(self,iterable):
        self.items = []
        self.__update(iterable)

    def update(self, iterable):
        for item in iterable:
            self.items.append(item)
    __update = update   # private copy of orginal update() method

class MappingSubclass(Mapping):
    def update(self,keys,values):
        # provides new signature for update()
        # but does not breal __init__()
        for item in zip(keys,values):
            self.items.append(item)

def main():
    x = Mapping([0,1,2,3,4])
    keys = [0,1,2,3]
    values = ["abc","def","ghi","jkl"]
    y = MappingSubclass([])
    y.update(keys,values)
    print(y.items)


main()


