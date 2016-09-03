public abstract class Universe {

  public static Universe fromVersion(Version version) throws Exception {
    if(version.equals(Version.fromInt(1))){
      return new Universe1();
    }
    
    throw new Exception("Illegal version argument");
  }

  public abstract void run();
  public abstract Time time();
  public abstract Version version();

}
