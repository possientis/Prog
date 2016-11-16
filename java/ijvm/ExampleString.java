class ExampleString {
  // Assume this application is invoked with one command-line
  // argument, the string "Hi!".
  public static void main(String[] args) {
    // argZero, because it is assigned a String from the command
    // line, does not reference a string literal. This string
    // is not interned.
    String argZero = args[0];

    // literalString, however, does reference a string literal.
    // It will be assigned a reference to a String with the value
    // "Hi!" by an instruction that references a
    // CONSTANT_String_info entry in the constant pool. The
    // "Hi!" string will be interned by this process.
 
    String literalString = "Hi!";

    // At this point, there are two String objects on the heap
    // that have the value "Hi!". The one from arg[0], which
    // isn't interned, and the one from the literal, which
    // is interned.
    System.out.print("Before interning argZero: ");
    if (argZero == literalString) {
      System.out.println("they're the same string object!");
    }
    else {
      System.out.println("they're different string objects.");
    }
    // argZero.intern() returns the reference to the literal
    // string "Hi!" that is already interned. Now both argZero
    // and literalString have the same value. The non-interned
    // version of "Hi!" is now available for garbage collection.

    argZero = argZero.intern();
  
    System.out.print("After interning argZero: ");
    if (argZero == literalString) {
      System.out.println("they're the same string object!");
    }
    else {
      System.out.println("they're different string objects.");
    }
  }
}

  




