try:
    infile = open("log1","r") # built-in, not library
    print(infile.read())
    infile.close()
except Exception:
    print("cannot open file log1\n")




outfile = open("log2","w")

outfile.write("This is some\nRandom text\nTo be read")

outfile.close()


try:
    f = open("log3", "w")
    f.write('quick line here\n')
except Exception:
    print("io failed\n")
finally:
    f.close()
