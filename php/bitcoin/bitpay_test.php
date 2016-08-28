<?php

$url = "https://bitpay.com/api/rates";

$json = file_get_contents($url);
$data = json_decode($json, TRUE);

$rate = $data[1]["rate"];    

echo $rate
?>
