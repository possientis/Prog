using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {

      try
      {
        Console.Write("Divide 10 by ");
        int num = int.Parse(Console.ReadLine());
        Console.WriteLine("10/{0} = {1}", num,10/num);
      }
      catch(DivideByZeroException ex)
      {
        Console.WriteLine("Can't divide by zero");
        Console.WriteLine(ex.GetType().Name);
        Console.WriteLine(ex.Message);
        Console.WriteLine(ex.StackTrace);
        // throw ex;
        // throw new InvalidOperationException("Operation Failed",ex);
      }
      catch(Exception ex)
      {
        Console.WriteLine(ex.GetType().Name);
        Console.WriteLine(ex.Message);
        Console.WriteLine(ex.StackTrace);
      }
      finally
      {
        Console.WriteLine("Clean up code running");
      }
    }
  }
}
