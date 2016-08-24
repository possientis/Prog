<?php
// failing to install bitwasp
use BitWasp\Bitcoin\Bitcoin;
use BitWasp\Bitcoin\Address;
use BitWasp\Bitcoin\Key\PrivateKeyFactory;

$network = Bitcoin::getNetwork();

$privateKey = PrivateKeyFactory::create(true);
$publicKey = $privateKey->getPublicKey();
$address = $publicKey->getAddress();

?>
