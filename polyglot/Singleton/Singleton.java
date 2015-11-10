// Singleton design pattern

class SingleObject {
  // private constructor
  private SingleObject(){}
  // static data member pointing to unique instance
  private static SingleObject mInstance = null;
  // get the only object available
  public static SingleObject getInstance(){
    if(mInstance == null){
      mInstance = new SingleObject();
    }
    return mInstance;
  }
  public void showMessage(){
    System.out.println("The single object is alive and well");
  }
 }

public class Singleton {
  public static void main(String[] args){
    // will not compile
    // SingleObject nope = new SingleObject();

    SingleObject object = SingleObject.getInstance();
    object.showMessage();
  }
}

