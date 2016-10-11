var bitcore = require('bitcore-lib');
var ECIES = require('bitcore-ecies');
var alicePrivateKey = new bitcore.PrivateKey();
var alicePublicKey = new bitcore.PublicKey.fromPrivateKey(alicePrivateKey) // alicePrivateKey.publicKey
var cypher1 = ECIES().privateKey(alicePrivateKey).publicKey(alicePublicKey);
var encrypted = cypher1.encrypt(data);
var cypher2 = ECIES().privateKey(alicePrivateKey).publicKey(alicePublicKey);
var decrypted = cypher2.decrypt(data);
