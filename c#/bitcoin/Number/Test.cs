using System;
using System.Numerics;

public class Test
{
  public static void Main(string[] args)
  {
    Number x = Number.ZERO;
    Console.WriteLine("0 has {0} bits", x.BitLength());
    x = Number.ONE;
    Console.WriteLine("1 has {0} bits", x.BitLength());
    Console.WriteLine("-1 has {0} bits", x.Negate().BitLength());
    x = x.Add(x);
    Console.WriteLine("2 has {0} bits", x.BitLength());
    Console.WriteLine("-2 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("3 has {0} bits", x.BitLength());
    Console.WriteLine("-3 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("4 has {0} bits", x.BitLength());
    Console.WriteLine("-4 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("5 has {0} bits", x.BitLength());
    Console.WriteLine("-5 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("6 has {0} bits", x.BitLength());
    Console.WriteLine("-6 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("7 has {0} bits", x.BitLength());
    Console.WriteLine("-7 has {0} bits", x.Negate().BitLength());
    x = x.Add(Number.ONE);
    Console.WriteLine("8 has {0} bits", x.BitLength());
    Console.WriteLine("-8 has {0} bits", x.Negate().BitLength());

    int i = 16 / 8;
    Console.WriteLine("i = {0}", i);

  }
}
