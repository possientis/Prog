# install python3-websocket
from websocket import create_connection

ws = create_connection("wss://ws.blockchain.info/inv")
ws.send("""{"op":"unconfirmed_sub"}""")
while True:
    tx = ws.recv()
    print("tx!")
    with open("bitcointx.json", "a") as f:
        f.write(tx + "\n####\n")
