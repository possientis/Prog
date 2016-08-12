import sys

def wordDictFromFile(filename):

    f = open(filename,'r')
    text = f.read()
    f.close()

    wordList = text.split()
    # this is a comment
    dictionary = {}
    for word in wordList:
        w = word.lower().strip()
        if w in dictionary:
            dictionary[w] = dictionary[w] + 1
        else:
            dictionary[w] = 1

    return dictionary

def cdr(pair):
    return pair[1]


def main():
    dictionary = wordDictFromFile(sys.argv[1])
    items = list(dictionary.items())
    items.sort(key = cdr,reverse=True)
    for i in range(0,49):
        print(items[i][0], '\t: ', items[i][1])



if __name__ == '__main__':
    main()
