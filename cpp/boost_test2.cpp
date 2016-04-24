#include <boost/regex.hpp>
#include <iostream>
#include <string>

// linking to a boost library (boost_regex.a in this case)
// is sometimes necessary when boost functionality goes
// beyond the simple hpp header file (which is usually
// all there is to it, all template or inline stuff)
//
// g++ filename.cpp -L/usr/local/lib -lboost_regex
//
// furthermore, when attempting to run the binary which
// relies on a shared library (in this case), linux may 
// fail to find the said library.
//
// LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}
// export LD_LIBRARY_PATH
//
// then run...

int main()
{
  std::string line;
  boost::regex pat( "^Subject: (Re: |Aw: )*(.*)" );

  while (std::cin)
  {
    std::getline(std::cin, line);
    boost::smatch matches;
    if (boost::regex_match(line, matches, pat))
      std::cout << matches[2] << std::endl;
  }
}
