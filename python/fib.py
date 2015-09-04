def fibonnacci():
    i = j = 1
    while True:
        (r, i, j) = (i, j, i + j)
        yield r

def printRabbits():
    for rabbits in fibonnacci():
        print(rabbits)
        if rabbits > 100: break
