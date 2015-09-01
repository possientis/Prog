import urllib.request
uf = urllib.request.urlopen('http://google.com')
text = uf.read()
print(text)

# urllib,request.urlretrieve('https://myurl','filename')
