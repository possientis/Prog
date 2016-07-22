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
int main()
{
  // Private secret key.
  bc::ec_secret secret; 
  bc::decode_base16(secret, 
      "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD");
//      "038109007313a5807b2eccc082c8c3fbb988a973cacf1a7df9ce725c31b14776");
  std::cout << "Secret key: " << bc::encode_base16(secret) << std::endl;
  
  // Get public key.
  bc::ec_point public_key = bc::secret_to_public_key(secret);
  std::cout << "Public key: " << bc::encode_hex(public_key) << std::endl;
  
  // Create Bitcoin address.
  bc::payment_address payaddr;
  bc::set_public_key(payaddr, public_key);
  const std::string address = payaddr.encoded();
  std::cout << "Address: " << address << std::endl;


  // Compute hash of public key for P2PKH address.
  const bc::short_hash hash = bc::bitcoin_short_hash(public_key);
  std::cout << "Hash: " << bc::encode_base16(hash) << std::endl;

  // attempting to compute corresponding address 
  bc::data_chunk unencoded_address;
  // Reserve 25 bytes
  //
  // [ version:1 ]
  //
  //[ hash:20 ]
  //
  //[ checksum:4 ]
  unencoded_address.reserve(25);
  //// Version byte, 0 is normal BTC address (P2PKH).
  unencoded_address.push_back(0);
  // Hash data
  bc::extend_data(unencoded_address, hash);
  // Checksum is computed by hashing data, and adding 4 bytes from hash.
  bc::append_checksum(unencoded_address);
  // Finally we must encode the result in Bitcoin's base58 encoding
  assert(unencoded_address.size() == 25);
  const std::string address2 = bc::encode_base58(unencoded_address);
  std::cout << "Address: " << address2 << std::endl;


  // attempting to compute wif and wif_uncompressed
  bc::data_chunk unencoded_priv;
  // Reserve 37 bytes
  //[ version:1 ]
  //[ priv key: 32 ]
  //[ checksum:4 ]
  unencoded_priv.reserve(38);
  unencoded_priv.push_back(128);  // version
  bc::extend_data(unencoded_priv, secret);
  bc::append_checksum(unencoded_priv);
  assert(unencoded_priv.size() == 37);
  const std::string wif_uncompressed = bc::encode_base58(unencoded_priv);
  std::cout << "WIF uncompressed: " << wif_uncompressed << std::endl;

  // TODO compute wif, this is wrong as it stands
  unencoded_priv.push_back(0x01);
  assert(unencoded_priv.size() == 38);
  const std::string wif = bc::encode_base58(unencoded_priv);
  std::cout << "WIF: " << wif << std::endl;


  return 0;
}

