public class ClassTest
{
  public static void main(String[] args)
  {
    Class c = null;

    try
    {
      c = Class.forName("java.security.SecureRandom");
    }
    catch(ClassNotFoundException e)
    {
      System.err.println(e.toString());
    }

    System.out.println("Name: " + c.getName());
    System.out.println("Superclass: " + c.getSuperclass().getName());
    System.out.println("IsInterface: " + c.isInterface());
    System.out.println("Interfaces: ");
    for(Class i : c.getInterfaces())
    {
      System.out.println(i.getName());
    }

    
  }
}
