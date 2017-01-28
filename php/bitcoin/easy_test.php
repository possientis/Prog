<?php

require_once('easybitcoin.php');

$rpcuser = 'username';
$rpcpassword = 'password';
$bitcoin = new Bitcoin($rpcuser, $rpcpassword, '127.0.0.1', '8332');
$result = $bitcoin->getinfo();
var_dump($result);

?>
