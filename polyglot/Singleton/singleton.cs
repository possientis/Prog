// Singleton design pattern
using System;
class SingleObject {
  // private constructor
  private SingleObject(){}
  // static data member pointing to unique instance
  private static SingleObject mInstance = null;
  // get the only object available
  public static SingleObject GetInstance(){
    if(mInstance == null){
      mInstance = new SingleObject();
    }
    return mInstance;
  }
  public void ShowMessage(){
    Console.WriteLine("The single object is alive and well");
  }
}

public class Singleton {
  public static void Main(string[] args){
    // will not compile
    //SingleObject nope = new SingleObject();

    SingleObject obj = SingleObject.GetInstance();
    obj.ShowMessage();
  }
}

