def sieve (l):
    if len(l) <= 1:
        return l
    else:
        head = l[0]
        tail = l[1:]
        new = [x for x in tail if x % head != 0]  
        res = sieve(new)
        res.append(head)
        return res

def primes(N):
    l = range(2,(N+1))
    res = []
    while len(l) > 0:
        head = l[0]
        print(head)
        tail = l[1:]
        new = [x for x in tail if x % head != 0]  
        res.append(head)
        l = new
    return res


def main():
    xs = primes(2000000)
    print(sum(xs))


main()
