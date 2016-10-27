/* expecting 03 3b 84 00 01 1a 05 68 3b a7 ff f9 when compiled */

//  0 iconst_0     -> 03
//  1 istore_0     -> 3b
//  2 iinc 0, 1    -> 84 00 01
//  5 iload_0      -> 1a
//  6 iconst_2     -> 05
//  7 imul         -> 68
//  8 istore_0     -> 3b
//  9 goto 2       -> a7 ff f9 (-7)

class Act {

  public static void doMathForever() {

    int i = 0;

    for(;;) {

      i += 1;
      i *= 2;

    }
  }
}
