// Three explicit ways to instantiate a java object: new, newInstance, clone

class Example4 implements Cloneable { // or else CloneNotSupportedException

  Example4(){
    System.out.println("Created by invoking newInstance()");
  }

  Example4(String msg){
    System.out.println(msg);
  }

  public static void main(String[] args)
    throws ClassNotFoundException /* forName */, InstantiationException /* newInstance */,
           IllegalAccessException /* newInstance */ , CloneNotSupportedException /* clone */ {

    // Create a new Example4 object with the new operator
    Example4 obj1 = new Example4("Created with new");

    // Get a reference to the Class instance for Example4, then
    // invoke newInstance() on it to create a new Example4 object
    Class myClass = Class.forName("Example4");
    Example4 obj2 = (Example4) myClass.newInstance();
    
    // Make an identical copy of the the second Example4 object
    // does not call 'new', does not call 'newInstance'
    // feels like it is calling a copy constructor...
   
    Example4 obj3 = (Example4) obj2.clone();

    System.out.println(obj2 == obj3); // false
  }
}
