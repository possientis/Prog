<?php

  $url = "https://blockchain.info/stats?format=json";
  $stats = json_decode(file_get_contents($url), true);

    echo $stats['market_price_usd'];

?>
