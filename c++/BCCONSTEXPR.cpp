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
  BC_CONSTEXPR int x = 23;

  return 0;
}

