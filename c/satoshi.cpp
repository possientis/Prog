#include <iostream>
#include <string>
#include <bitcoin/bitcoin.hpp>

// Extract Satoshi's words.
int main()
{
  const auto block = bc::genesis_block();
  const auto& tx = block.transactions[0];
  const auto& input = tx.inputs[0];
  const auto script = bc::save_script(input.script);
  std::string message(script.begin(), script.end());
  std::cout << message << std::endl;
  return 0;
}

