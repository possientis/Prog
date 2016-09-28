public abstract class Number implements Comparable<Number> {
  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);


  public abstract String toString();
  public abstract int compareTo(Number rhs);
  public abstract int hashCode();
  public boolean equals(Number rhs){ return compareTo(rhs) == 0; }
}

