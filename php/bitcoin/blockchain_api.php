<?php

$guid="xxxxxxxxx";
$main_password="xxxxxxxxx";

$json_url = "https://blockchain.info/merchant/$guid/balance?password=$main_password";

$json_data = file_get_contents($json_url);


$json_feed = json_decode($json_data);

echo ($json_feed == null).PHP_EOL;

$balance = $json_feed->balance;

echo $balance;
?>
