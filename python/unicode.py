unicode_string = u'This is a unicode string'

print(unicode_string)

unicode_string = u'abc_\u03a0\u03a3\u03a9_\u0414\u0424\u042F'
print(unicode_string)       # abc_ΠΣΩ_ДФЯ
print(repr(unicode_string)) # 'abc_ΠΣΩ_ДФЯ'
# b'abc_\xce\xa0\xce\xa3\xce\xa9_\xd0\x94\xd0\xa4\xd0\xaf'
print(unicode_string.encode('utf-8'))   

