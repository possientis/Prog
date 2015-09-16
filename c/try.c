// exceptions
#include <iostream>
#include <exception>

class myexception: public std::exception
{
  virtual const char* what() const throw()
  {
    return "My exception happened";
  }
};

myexception myex;

int main(){

  try
  {
    throw myex;
  }
  catch(const std::exception& e)
  {
    std::cout << e.what() << '\n';
  }


  return 0;
}
