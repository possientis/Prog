import java.math.BigInteger;

interface GroupStructure<G> {
  public G identity();
  public G inverse(G x);
  public G combine(G x, G y);
}


class ZStructure implements GroupStructure<BigInteger> {
  public BigInteger identity(){ return null; } // TODO
  public BigInteger inverse(BigInteger x){ return null; } // TODO
  public BigInteger combine(BigInteger x, BigInteger y){ return null; } // TODO
}

class Z {
  private static ZStructure op = new ZStructure();
  private BigInteger _n;
  public Z(BigInteger n){this._n = n; }
  public static Z identity = new Z(op.identity());
  public Z add(Z rhs){ return new Z(op.combine(this._n, rhs._n)); }
  public Z opp(){ return new Z(op.inverse(this._n)); }
}

public class Group {
  public static void main(String[] args){
  }
}


