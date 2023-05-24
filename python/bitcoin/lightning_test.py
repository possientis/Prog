from lightning import LightningRpc
import random

l = LightningRpc("${HOME}/.lightning/lightning-rpc") # TODO: fix ${HOME} issue

#invoice = l.invoice(100,"lbl{}".format(random.random()),"testpayment")

route = l.getroute(l.getinfo()['id'],100,1)

print(route)


