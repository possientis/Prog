import org.artima.greeter.Greeter;
import org.artima.greeter.GreeterClassLoader;

public class GreetAndForget {

  // Arguments to this application:
  //
  // args[0] - path name of directory in which class files
  // 
  //           for greeters are stored
  // 
  // args[1], args[2], ... - class names of greeters to load
  // 
  //           and invoke the greet() method on.
  // 
  // All greeters must implement the org.artima.greeter.Greeter
  // interface.
  // 

  static public void main(String[] args) {

    if (args.length <= 1) {

      System.out.println(

          "Enter base path and greeter class names as args.");

      return;

    }

    for (int i = 1; i < args.length; ++i) {
      try {

        GreeterClassLoader gcl = new GreeterClassLoader(args[0]);

        // Load the greeter specified on the command line

        Class c = gcl.loadClass(args[i], true);
        
        // Instantiate it into a greeter object

        Object o = c.newInstance();
        
        // Cast the Object ref to the Greeter interface type
        // so greet() can be invoked on it

        Greeter greeter = (Greeter) o;

        // Greet the world in this greeter's special way

        greeter.greet();

        // Forget the class loader object, Class
        // instance, and greeter object

        gcl = null;

        c = null;

        o = null;

        greeter = null;
        
        // At this point, the types loaded through the
        // GreeterClassLoader object created at the top of
        // this for loop are unreferenced and can be unloaded
        // by the virtual machine.

      }
      
      catch (Exception e) {

        e.printStackTrace();

        System.exit(1);

      }
    }
  }
}





