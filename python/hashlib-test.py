import hashlib

def create_checksum(path):
    """
    Reads in file. Creates checksum of file line by line.
    Returns complete checksum total for file.
    """

    fp = open(path)
    checksum = hashlib.md5()
    while True:
        buffer = fp.read(8192)
        if not buffer:break
        checksum.update(buffer.encode('utf-8'))
    fp.close()
    checksum = checksum.digest()
    return hex(int.from_bytes(checksum, byteorder='big'))



b2 = b'\xce\xb0\xcer\xe0\x8co\x1cl;\xb2\x15\xe6\x97\x8a['

i2 = int.from_bytes(b2, byteorder='big')

print(hex(i2))







