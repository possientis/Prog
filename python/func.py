import math

# removes all multiples of k in list l (except k itself)
def remove_mult(l,k):
    v = [x for x in l if (x == k) or (x % k != 0)]
    return v

# returns list of primes less than or equal to argument
def primes(n):
    N = int(math.sqrt(n) + 1)
    l = range(2,(n+1))
    index = 0
    while (l[index] <= N):
        l = remove_mult(l,l[index])
        index = index +1
    return l

def main():
    n = int(input("Enter an integer: "))
    l = primes(n)
    print("All primes less than or equal to", n, "are:")
    print(l)

def fac(n):
    if n == 0:
        res = 1
    else:
        res = n * fac (n -1)

    return res

def product(l):
    res = 1
    for i in l:
        res = res * i
    return res

def fac2(n):
    return product(range(1,n+1))

print(fac2(5))


