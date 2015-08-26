from urllib2 import urlopen
from xml.sax import make_parser
from xml.sax import ContentHandler

def listFeedTitles(url):
    infile = urlopen(url)
    parser = make_parser()
    parser.setContentHandler(RSSHandler())
    parser.parse(infile)

class RSSHandler(ContentHandler):
    def __init__(self):
        ContentHandler.__init__(self)
        self.__inItem = False
        self.__inTitle = False

    def characters(self,data):
        if self.__inTitle:
            sys.stdout.write(data)

    def startElements(self,tag,attrs):
        if tag == "item": self.__inItem = True
        if tag == "title" and self.__inItem:
            self.__inTitle = True

    def endElement(self,tag):
        if tag == "title" and self.__inTitle:
            sys.stdout.write("\n")
            self.__inTitle = False
        if tag == "item":
            self.__inItem = False

