
def create_big_file():
    f = open("big_file.txt", "w")
    statement = """This is a big line that I intend to 
                write over and over again."""
    for x in range(20000):
        x+=1
        f.write("%s\n" % statement)
    
    f.close()


if __name__ == "__main__":
    create_big_file()
