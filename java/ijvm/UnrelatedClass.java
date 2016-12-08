class UnrelatedClass {

  public static void main(String[] args) {

    ItsSubclass isc = new ItsSubclass();      // invokespecial (of an <init)

    ItsSubclass.classMethod();                // invokestatic

    isc.classMethod();                        // invokestatic

    isc.instanceMethod();                     // invokevirtual

    isc.finalInstanceMethod();                 // invokevirtual

    isc.interfaceMethod();                    // invokevirtual

    InYourFace iyf = isc;

    iyf.interfaceMethod();                    // invokeinterface

  }
}
