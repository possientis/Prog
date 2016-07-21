import re

regex = "{{(.*?)}}"
some_string = """This is a string with {{words}} embedded in
    {{curly brackets}} to show an {{example}} of {{regular expression}}"""

for match in re.findall(regex, some_string):
    print("MATCH->" + match)

print("compiling regex ...")

re_obj = re.compile(regex)
for match in re_obj.findall(some_string):
    print("MATCH->" + match)

raw_pattern = r'\b[a-z]+\b' # \b matches word boundaries
non_raw_pattern = '\b[a-z]+\b'

str2 = 'a few little words'
print(re.findall(raw_pattern,str2))         # ['a', 'few', 'little', 'words']
print(re.findall(non_raw_pattern, str2))    # []

str3 = "a few \blittle\b words"             # a fewlittl words
print(str3)
print(re.findall(non_raw_pattern, str3))    # ['\x08little\x08'] 


