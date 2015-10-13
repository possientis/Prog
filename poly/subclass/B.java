public class B extends A{
  public int b;
  public B(int a,int b){super(a); this.b = b;}
  @Override   // optional
  public void foo(){System.out.println("B::foo() is running");}
}
