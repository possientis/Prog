# blockchain.info is unreliable. It will stop at 250 UTXOs ...
import json
import requests

# example address
address = '1Dorian4RoXcnBv9hnQ4Y2C1an6NJ4UrjX'

# The API URL is https://blockchain.info/unspent?active=<address>
# It returns a JSON object with a list "unspent_outputs", containing UTXO, like this:
#{ "unspent_outputs":[
# {
#   "tx_hash":"ebadfaa92f1fd29e2fe296eda702c48bd11ffd52313e986e99ddad9084062167",
#   "tx_index":51919767,
#   "tx_output_n": 1,
#   "script":"76a9148c7e252f8d64b0b6e313985915110fcfefcf4a2d88ac",
#   "value": 8000000,
#   "value_hex": "7a1200",
#   "confirmations":28691
# },
# ...
#]}

resp = requests.get('https://blockchain.info/unspent?active=%s' % address)

resp_as_json = json.loads(resp.text)

utxo_set = resp_as_json["unspent_outputs"]

total = 0
count = 0

for utxo in utxo_set:
    tx_hash = utxo['tx_hash']
    tx_out_n = utxo['tx_output_n']
    value = utxo['value']
    print('%s:%d - %ld Satoshis' % (tx_hash, tx_out_n, value))
    total = total + value
    count = count + 1

total_BTC = total / 100000000.0

print('total (BTC) = %f in %d UTXOs' % (total_BTC, count))
