public class Greet {
  // Arguments to this application:
  //
  // args[0] - path name of directory in which class files
  //
  // for greeters are stored
  //
  // args[1], args[2], ... - class names of greeters to load
  //
  // and invoke the greet() method on.
  //
  // All greeters must implement the COM.artima.greeter.Greeter
  // interface.
  //

  static public void main(String[] args) {

    if (args.length <= 1) {
      System.out.println(
          "Enter base path and greeter class names as args.");
      return;
    }

    GreeterClassLoader gcl = new GreeterClassLoader(args[0]);

    for (int i = 1; i < args.length; ++i) {
      try {
        // Load the greeter specified on the command line
        Class c = gcl.loadClass(args[i], true);

        // Instantiate it into a greeter object
        Object o = c.newInstance();
        
        // Cast the Object ref to the Greeter interface type
        // so greet() can be invoked on it
        Greeter greeter = (Greeter) o;

        // Greet the world in this greeter's special way
        greeter.greet();
      }
      catch (Exception e) {
        e.printStackTrace();
      }
    }
  }
}
