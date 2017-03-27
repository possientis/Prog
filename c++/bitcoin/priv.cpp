#include <bitcoin/bitcoin.hpp>
#include <assert.h>

int main()
{
  // attempting to mirror output of pycoin key utility command:
  // $ ku -j KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ
 
  using namespace bc;
  using namespace std;

  // Private secret key.
  ec_secret secret; 
  decode_base16(
      secret, 
      // wif "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ"
      "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD"
  ); 

 // get public key
  ec_point public_key = secret_to_public_key(secret);
  ec_point public_key_uncomp = secret_to_public_key(secret, false);

  // get bitcoin address quickly
  payment_address payaddr;
  payment_address payaddr_uncomp;
  set_public_key(payaddr, public_key);
  set_public_key(payaddr_uncomp, public_key_uncomp);
  const string btc_address = payaddr.encoded(); 
  const string btc_address_uncomp = payaddr_uncomp.encoded();

  // get hash160 
  const short_hash hash = bitcoin_short_hash(public_key);
  const short_hash hash_uncomp = bitcoin_short_hash(public_key_uncomp);
 
  // computing corresponding address 
  data_chunk unencoded_address;
  // Reserve 25 bytes
  //
  // [ version:1 ] (0x00)
  //
  //[ hash:20 ]
  //
  //[ checksum:4 ]
  unencoded_address.reserve(25);
  // version byte, 0 is normal BTC address (P2PKH).
  unencoded_address.push_back(0);
  // Hash data
  extend_data(unencoded_address, hash);
  // Checksum is computed by hashing data, and adding 4 bytes from hash.
  append_checksum(unencoded_address);
  // Finally we must encode the result in Bitcoin's base58 encoding
  assert(unencoded_address.size() == 25);
  const string address = encode_base58(unencoded_address);
  assert(btc_address == address);

  // uncomp case
  data_chunk unencoded_address_uncomp;
  unencoded_address_uncomp.reserve(25);
  unencoded_address_uncomp.push_back(0);
  extend_data(unencoded_address_uncomp, hash_uncomp);
  append_checksum(unencoded_address_uncomp);
  assert(unencoded_address_uncomp.size() == 25);
  const string address_uncomp = encode_base58(unencoded_address_uncomp);
  assert(btc_address_uncomp == address_uncomp);
 
  // attempting to compute wif-uncomp
  data_chunk unencoded_priv;
  // Reserve 37 bytes
  //[ version:1  ] (0x80)
  //[ priv key: 32 ]
  //[ checksum:4 ]
  unencoded_priv.reserve(37);
  unencoded_priv.push_back(0x80);  // version
  extend_data(unencoded_priv, secret);
  append_checksum(unencoded_priv);
  assert(unencoded_priv.size() == 37);
  const string wif_uncomp = encode_base58(unencoded_priv);

  // attempting to compute wif
  data_chunk unencoded_priv2;
  // Reserve 38 bytes
  //[ version: 1]   (0x80)
  //[ priv key: 32 ]
  //[ suffix: 1]    (0x01)
  //[checksum: 4]
  unencoded_priv2.reserve(38);
  unencoded_priv2.push_back(0x80);  // version
  extend_data(unencoded_priv2, secret);
  unencoded_priv2.push_back(0x01);
  //[ checksum:4 ]
  append_checksum(unencoded_priv2);
  assert(unencoded_priv2.size() == 38);
  const std::string wif = bc::encode_base58(unencoded_priv2);


/* $ ku -j KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ  # pycoin key utility
  {
   "BTC_address": "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy",
   "BTC_address_uncomp": "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x",
   "address": "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy",
   "address_uncomp": "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x",
   "hash160": "bbc1e42a39d05a4cc61752d6963b7f69d09bb27b",
   "hash160_uncomp": "211b74ca4686f81efda5641767fc84ef16dafe0b",
   "input": "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ",
   "key_pair_as_sec": "03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a",
   "key_pair_as_sec_uncomp": "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
   "netcode": "BTC",
   "network": "Bitcoin mainnet",
   "public_pair_x": "108626704259373488493324494832963472198167093861790438979212875284973843395610",
   "public_pair_x_hex": "f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a",
   "public_pair_y": "3532285151429480400098290360892322426461524297929807392099748929454186978267",
   "public_pair_y_hex": "7cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
   "secret_exponent": "13840170145645816737842251482747434280357113762558403558088249138233286766301",
   "secret_exponent_hex": "1e99423a4ed27608a15a2616a2b0e9e52ced330ac530edcc32c8ffc6a526aedd",    # <--------- HERE !
   "wif": "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ",
   "wif_uncomp": "5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn",
   "y_parity": "odd"
}
*/

  // checking
  std::cout << "{" 
            << endl;
  
  std::cout << "   \"BTC_address\": \"" 
            << btc_address 
            << "\"," 
            << endl;

  std::cout << "   \"BTC_address_uncomp\": \"" 
            << btc_address_uncomp 
            << "\"," 
            << endl;

  std::cout << "   \"address\": \"" 
            << btc_address 
            << "\"," 
            << endl;

  std::cout << "   \"address_uncomp\": \"" 
            << btc_address_uncomp 
            << "\"," 
            << endl;

  std::cout << "   \"hash160\": \"" 
            << encode_hex(hash) 
            << "\"," 
            << endl;

  std::cout << "   \"hash160_uncomp\": \"" 
            << encode_base16(hash_uncomp) 
            << "\"," 
            << endl;

  std::cout << "   \"input\": \"" 
            << "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ\"," 
            << endl;

  std::cout << "   \"key_pair_as_sec\": \"" 
            << encode_hex(public_key) 
            << "\"," 
            << endl;

  std::cout << "   \"key_pair_as_sec_uncomp\": \"" 
            << encode_hex(public_key_uncomp) 
            << "\"," 
            << endl;

  std::cout << "   \"netcode\": \"BTC\"," 
            << endl;

  std::cout << "   \"network\": \"Bitcoin mainnet\"," 
            << endl;

  std::cout << "   \"public_pair_x\": \"" << "TODO\"" 
            << endl;

  std::cout << "   \"public_pair_x_hex\": \"" 
            << encode_hex(public_key).substr(2) 
            << "\"," 
            << endl; 

  std::cout << "   \"public_pair_y\": \"" 
            << "TODO\"" 
            << endl;

  std::cout << "   \"public_pair_y_hex\": \"" 
            << encode_hex(public_key_uncomp).substr(66) 
            << "\"," 
            << endl; 

  std::cout << "   \"secret_exponent\": \"" 
            << "TODO\"" 
            << endl;

  std::cout << "   \"secret_exponent_hex\": \"" 
            << encode_hex(secret) 
            << "\"," 
            << endl;

  std::cout << "   \"wif\": \"" << wif << "\"," << endl;

  std::cout << "   \"wif_uncomp\": \"" << wif_uncomp << "\"," << endl;

  std::cout << "   \"y_parity\": \"odd\"" << endl;

  std::cout << "}" << endl;

  return 0;
}

