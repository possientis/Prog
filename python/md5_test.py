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


if __name__ == "__main__":
    hashmd5 = create_checksum('log')
    print(hashmd5)
