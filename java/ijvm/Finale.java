class Finale {

  protected void finalize() /* throws Throwable */ {
    
   /*  super.finalize(); */

    System.out.println("A Finale object was finalized");

  }

  public static void main(String[] args){

    Finale a = new Finale();

    System.out.println("A Finale object has been created");

    a = null; // object no longer referenced

    System.out.println("Program terminating");

    // nothing.... won't see anything unless object is garbaged-collected

  }

}
