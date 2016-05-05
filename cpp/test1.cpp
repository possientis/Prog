#include <bitcoin/bitcoin.hpp>

using namespace bc;

int main()
{
  block_type blk = genesis_block();
  std::cout << encode_hex(hash_block_header(blk.header)) << std::endl;
  return 0;
}
