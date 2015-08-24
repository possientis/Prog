def Divisors(number):
    """ synthesizes a list of all the positive numbers
    that evenly divide into the specified number"""
    div = []
    for i in range(1,number+1):
        if number % i == 0:
            div.append(i)
    return div
