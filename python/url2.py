import urllib.request

url_file = urllib.request.urlopen("http://icanhazip.com")
string = url_file.read()
print(string)

