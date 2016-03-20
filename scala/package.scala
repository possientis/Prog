// Java-like package clause 
package bobsrockets.navigation
class Navigator {
}


// C# Namespace-like package
package bobsrockets.navigation {
  class Navigator {
  }
}


// Nested namespace-like package
package bobsrockets {
  package navigation {
    class Navigator3 {
    }
  }
}

package bobsrockets {
  package navigation {
    class Navigator2 {
    }
  }
  package tests {
    object NavigatorTest {
    val x = new navigation.Navigator2
    }
  }
}

package bobsrockets {
  package navigation {
    package tests {
      object Test1 {}
    }
    ///// how to access Test1, Test2, Test3 here?
    // tests.Test1
    // bobsrockets.tests.Test2
    // _root_.tests.Test3  // root package ish
  }
  package tests {
    object Test2 {}
  }
}

package tests {
  object Test3 {}
}




