public abstract class Number implements Comparable<Number> {
  private static final Ring _ring;
  static
  {
    _ring = new Ring1();  // choose implementation
  }


  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);


  public abstract String toString();
  public abstract int compareTo(Number rhs);
  public abstract int hashCode();
  public boolean equals(Number rhs){ return compareTo(rhs) == 0; }
}

