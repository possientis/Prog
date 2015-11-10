#include <iostream>
#include <memory>

class SingleObject;
typedef std::shared_ptr<SingleObject> pSingleObject;

class SingleObject {
  private:
    SingleObject(){}
    static pSingleObject mInstance;
  public:
    static pSingleObject getInstance(){
      if(mInstance == nullptr){
        mInstance = pSingleObject(new SingleObject());
      }
      return mInstance;
    }
    void showMessage() const{
      std::cout << "The single object is alive and well\n";
    }
};

// definition of static member
pSingleObject SingleObject::mInstance = nullptr;


int main(int argc, char* argv[]){
  // will not compile
  // SingleObject obj;
  pSingleObject pObj = SingleObject::getInstance();
  pObj->showMessage();

  return 0;
}
