<?php

$address = "1NPrfWgJfkANmd1jt88A141PjhiarT8d9U";

$link = "https://blockchain.info/address/".$address."?format=json";

$fgc = json_decode(file_get_contents($link), true);

$lastTx = $fgc["txs"][0];

$getOuts = $lastTx["out"];

foreach($getOuts as $output){
  $myAddress = $output["addr"];
  if($myAddress == $address){
    echo $output["value"];
  }
}


?>
