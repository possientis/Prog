import hashlib

text = "I am Satoshi"

# iterate nonce from 0 to 19
for nonce in range(20):
    # add the nonce to the end of the text
    input = text + str(nonce)
    # calculate the SHA-256 hash of the input (text+nonce)
    hash = hashlib.sha256(input.encode('utf-8')).hexdigest()
    # show the input and hash result
    print(input, '=>', hash)
