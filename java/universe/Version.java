public abstract class Version {
  
  public static Version fromInt(int n){
    return new Version(){ public int toInt(){ return n; } };
  }

  public abstract int toInt();

  @Override
  public boolean equals(Object rhs){
    if(this.getClass() != rhs.getClass()) return false;
    return (hashCode() == rhs.hashCode());
  }

  @Override
  public int hashCode(){
    return toInt();
  }
}
