// g++ -std=c++14 filename.cpp $(pkg-config --libs libbitcoin)
// $ pkg-config --libs libbitcoin ----> -L/usr/local/lib -lbitcoin -lboost_chrono 
//                                      -lboost_date_time -lboost_filesystem 
//                                      -lboost_locale -lboost_program_options 
//                                      -lboost_regex -lboost_system -lboost_thread 
//                                      -lpthread -lrt -ldl -lsecp256k1
//
// In case the above fails to compile, try to add the --cflags option
// $ pkg-config --cflags libbitcoin --> -I/usr/local/include

#include <bitcoin/bitcoin.hpp>
#include <assert.h>
int main()
{
  // attempting to mirror output of pycoin key utility command:
  // $ ku -j KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ
 

  // Private secret key.
  bc::ec_secret secret; 
  bc::decode_base16(
      // corresponds to wif "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ"
      secret, "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD"); 

 // get public key
  bc::ec_point public_key = bc::secret_to_public_key(secret);
  bc::ec_point public_key_uncompressed = bc::secret_to_public_key(secret, false);
  // get bitcoin address quickly
  bc::payment_address payaddr;
  bc::payment_address payaddr_uncompressed;
  bc::set_public_key(payaddr, public_key);
  bc::set_public_key(payaddr_uncompressed, public_key_uncompressed);
  const std::string btc_address = payaddr.encoded(); 
  const std::string btc_address_uncompressed = payaddr_uncompressed.encoded();

  // get hash160 
  const bc::short_hash hash = bc::bitcoin_short_hash(public_key);
  const bc::short_hash hash_uncompressed = bc::bitcoin_short_hash(public_key_uncompressed);
 
  // computing corresponding address 
  bc::data_chunk unencoded_address;
  // Reserve 25 bytes
  //
  // [ version:1 ]
  //
  //[ hash:20 ]
  //
  //[ checksum:4 ]
  unencoded_address.reserve(25);
  // version byte, 0 is normal BTC address (P2PKH).
  unencoded_address.push_back(0);
  // Hash data
  bc::extend_data(unencoded_address, hash);
  // Checksum is computed by hashing data, and adding 4 bytes from hash.
  bc::append_checksum(unencoded_address);
  // Finally we must encode the result in Bitcoin's base58 encoding
  assert(unencoded_address.size() == 25);
  const std::string address = bc::encode_base58(unencoded_address);
  assert(btc_address == address);

  // uncompressed case
  bc::data_chunk unencoded_address_uncompressed;
  unencoded_address_uncompressed.reserve(25);
  unencoded_address_uncompressed.push_back(0);
  bc::extend_data(unencoded_address_uncompressed, hash_uncompressed);
  bc::append_checksum(unencoded_address_uncompressed);
  assert(unencoded_address_uncompressed.size() == 25);
  const std::string address_uncompressed = bc::encode_base58(unencoded_address_uncompressed);
  assert(btc_address_uncompressed == address_uncompressed);
 
  // attempting to compute wif-uncompressed
  bc::data_chunk unencoded_priv;
  // Reserve 37 bytes
  //[ version:1 ]
  //[ priv key: 32 ]
  //[ checksum:4 ]
  unencoded_priv.reserve(37);
  unencoded_priv.push_back(128);  // version
  bc::extend_data(unencoded_priv, secret);
  bc::append_checksum(unencoded_priv);
  assert(unencoded_priv.size() == 37);
  const std::string wif_uncompressed = bc::encode_base58(unencoded_priv);

  // attempting to compute wif
  bc::data_chunk unencoded_priv2;
  // Reserve 38 bytes
  //[ version:1 ]
  //[ priv key: 32 ]
  //[ suffix: 0x01]
  unencoded_priv2.reserve(38);
  unencoded_priv2.push_back(128);  // version
  bc::extend_data(unencoded_priv2, secret);
  unencoded_priv2.push_back(0x01);
  //[ checksum:4 ]
  bc::append_checksum(unencoded_priv2);
  assert(unencoded_priv2.size() == 38);
  const std::string wif = bc::encode_base58(unencoded_priv2);


/* $ ku -j KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ  # pycoin key utility
  {
   "BTC_address": "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy",
   "BTC_address_uncompressed": "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x",
   "address": "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy",
   "address_uncompressed": "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x",
   "hash160": "bbc1e42a39d05a4cc61752d6963b7f69d09bb27b",
   "hash160_uncompressed": "211b74ca4686f81efda5641767fc84ef16dafe0b",
   "input": "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ",
   "key_pair_as_sec": "03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a",
   "key_pair_as_sec_uncompressed": "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
   "netcode": "BTC",
   "network": "Bitcoin mainnet",
   "public_pair_x": "108626704259373488493324494832963472198167093861790438979212875284973843395610",
   "public_pair_x_hex": "f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a",
   "public_pair_y": "3532285151429480400098290360892322426461524297929807392099748929454186978267",
   "public_pair_y_hex": "7cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
   "secret_exponent": "13840170145645816737842251482747434280357113762558403558088249138233286766301",
   "secret_exponent_hex": "1e99423a4ed27608a15a2616a2b0e9e52ced330ac530edcc32c8ffc6a526aedd",    # <--------- HERE !
   "wif": "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ",
   "wif_uncompressed": "5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn",
   "y_parity": "odd"
}
*/

  // checking
  std::cout << "{" << std::endl;
  std::cout << "   \"BTC_address\": \"" << btc_address << "\"," << std::endl;
  std::cout << "   \"BTC_address_uncompressed\": \"" << btc_address_uncompressed << "\"," << std::endl;
  std::cout << "   \"address\": \"" << btc_address << "\"," << std::endl;
  std::cout << "   \"address_uncompressed\": \"" << btc_address_uncompressed << "\"," << std::endl;
  std::cout << "   \"hash160\": \"" << bc::encode_hex(hash) << "\"," << std::endl;
  std::cout << "   \"hash160_uncompressed\": \"" << bc::encode_base16(hash_uncompressed) << "\"," << std::endl;
  std::cout << "   \"input\": \"KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ\"," << std::endl;
  std::cout << "   \"key_pair_as_sec\": \"" << bc::encode_hex(public_key) << "\"," << std::endl;
  std::cout << "   \"key_pair_as_sec_uncompressed\": \"" << bc::encode_hex(public_key_uncompressed) << "\"," << std::endl;
  std::cout << "   \"netcode\": \"BTC\"," << std::endl;
  std::cout << "   \"network\": \"Bitcoin mainnet\"," << std::endl;
  std::cout << "   \"public_pair_x\": \"" << "TODO\"" << std::endl;
  std::cout << "   \"public_pair_x_hex\": \"" << bc::encode_hex(public_key).substr(2) << "\"," << std::endl; 
  std::cout << "   \"public_pair_y\": \"" << "TODO\"" << std::endl;
  std::cout << "   \"public_pair_y_hex\": \"" << bc::encode_hex(public_key_uncompressed).substr(66) << "\"," << std::endl; 
  std::cout << "   \"secret_exponent\": \"" << "TODO\"" << std::endl;
  std::cout << "   \"secret_exponent_hex\": \"" << bc::encode_hex(secret) << "\"," << std::endl;
  std::cout << "   \"wif\": \"" << wif << "\"," << std::endl;
  std::cout << "   \"wif_uncompressed\": \"" << wif_uncompressed << "\"," << std::endl;
  std::cout << "   \"y_parity\": \"odd\"" << std::endl;


  std::cout << "}" << std::endl;
  return 0;
}

