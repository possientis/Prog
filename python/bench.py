def bench(action, iterations):
    for i in range(0, iterations):
        action()


def nop():
    pass

if __name__== "__main__":
    bench(nop, 1000000)

