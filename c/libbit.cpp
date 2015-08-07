#include <iostream>
#include <bitcoin/bitcoin.hpp>
using namespace bc;

void A();
void B();
void C();
void D();
int main()
{
//  A();
  C();
}

void A()
{
  block_type blk = genesis_block();
  std::cout << encode_hex(hash_block_header(blk.header)) << std::endl;
  return;
}

void B()
{
//  hash_digest block_hash = hash_block_header(genesis_block());
//  std::cout << encode_hex(block_hash) << std::endl;
}

void C()
{
  block_type block = genesis_block();
  // const auto block = genesis_block();
  const auto& tx = block.transactions[0];
  const auto& input = tx.inputs[0];
  const auto script = save_script(input.script);
  std::string message(script.begin(), script.end());
  std::cout << message << std::endl;
}

void D()
{
  // Private secret key.
  //  ec_secret secret = decode_hash(
  //      "038109007313a5807b2eccc082c8c3fbb988a973cacf1a7df9ce725c31b14776");
  // Get public key
  // bc::ec_point public_key = bc::secret_to_public_key(secret);
  // std::cout << "Public key: " << bc::encode_hex(public_key) << std::endl;
}

