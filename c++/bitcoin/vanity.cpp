#include <bitcoin/bitcoin.hpp>

// The string we are searching for
const std::string search = "1kid";
// Generate a random secret key. A random 32 bytes.
bc::ec_secret random_secret(std::default_random_engine& engine);
// Extract the Bitcoin address from an EC secret.
std::string bitcoin_address(const bc::ec_secret& secret);
// Case insensitive comparison with the search string.
bool match_found(const std::string& address);


bc::ec_secret random_secret(std::default_random_engine& engine)
{
  // Create new secret...
  bc::ec_secret secret;
  // Iterate through every byte setting a random value...
  for (uint8_t& byte: secret)
    byte = engine() % std::numeric_limits<uint8_t>::max();
  // Return result.
  return secret;
}

std::string bitcoin_address(const bc::ec_secret& secret)
{
  // Convert secret to pubkey...
  bc::ec_point pubkey = bc::secret_to_public_key(secret);
  // Finally create address.
  bc::payment_address payaddr;
  bc::set_public_key(payaddr, pubkey);
  // Return encoded form.
  return payaddr.encoded();
}

bool match_found(const std::string& address)
{
  auto addr_it = address.begin();
  // Loop through the search string comparing it to the lower case
  // character of the supplied address.
  for (auto it = search.begin(); it != search.end(); ++it, ++addr_it)
    if (*it != std::tolower(*addr_it))
      return false;
  // Reached end of search string, so address matches.
  return true;
}

int main()
{
  std::random_device random;
  std::default_random_engine engine(random());
  // Loop continuously...
  while (true)
  {
    // Generate a random secret.
    bc::ec_secret secret = random_secret(engine);
    // Get the address.
    std::string address = bitcoin_address(secret);
    // Does it match our search string? (1kid)
    if (match_found(address))
    {
      // Success!
      std::cout << "Found vanity address! " << address << std::endl;
      std::cout << "Secret: " << bc::encode_hex(secret) << std::endl;
      return 0;
    }
  }
  // Should never reach here!
  return 0;
}



