class ItsSubclass extends ItsABirdItsAPlaneItsSuperclass {

  ItsSubclass() {
    this(0);      // invokespecial (of an <init)
  }

  ItsSubclass(int i) {
    super(i);     // invokespecial (of an <init)
  }

  private void privateMethod() {
  }
  
  void instanceMethod() {
  }

  final void anotherFinalInstanceMethod() {
  }

  void exampleInstanceMethod() {

    instanceMethod();               // invokevirtual

    super.instanceMethod();         // invokespecial

    privateMethod();                // invokespecial

    finalInstanceMethod();          // invokevirtual

    anotherFinalInstanceMethod();   // invokeVirtual

    interfaceMethod();              // invokevirtual

    classMethod();                  // invokestatic

  }
}
