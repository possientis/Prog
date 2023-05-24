import os
import sys
import logging
import tempfile


import utils  # PYTHONPATH set to ${HOME}/Libs/lightning/tests

bitcoind = None
TEST_DIR = tempfile.mkdtemp(prefix='lightning-')
VALGRIND = os.getenv("NO_VALGRIND","0") == "0"
DEVELOPER = os.getenv("DEVELOPER","0") == "1"
TEST_DEBUG = os.getenv("TEST_DEBUG","0") == "1"


print("Testing results are in {}".format(TEST_DIR))


if TEST_DEBUG:
    logging.basicConfig(level=logging.DEBUG, stream=sys.stderr)

logging.info("Tests running in '%s'",TEST_DIR)


# bitcoind testnet should be running
bitcoind = utils.BitcoinD(bitcoin_dir="${HOME}/.bitcoin/testnet3") # TODO: fix ${HOME} issue

info = bitcoind.rpc.getnetworkinfo()

version = info['version']

print(version)

info = bitcoind.rpc.getblockchaininfo()

blocks = info['blocks']

print(blocks)

info = bitcoind.rpc.getwalletinfo()

balance = info['balance']
print(balance)

print(bitcoind.rpc.getblockcount())


os.rmdir(TEST_DIR)







