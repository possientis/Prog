public class B extends A{
  private int b;

  public B(int a,int b){super(a); this.b = b;}
  public B(B rhs){super(rhs); b = rhs.b;}
  public int bGet(){return this.b;}
  public void bSet(int b){this.b = b;}
  @Override   // optional
  public void foo(){System.out.println("B::foo() is running");}
  public static void swap(B x, B y){
    A.swap(x,y);
    int temp = x.b; x.b = y.b; y.b = temp;}
}
