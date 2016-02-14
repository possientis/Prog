interface MagnitudeObject<T> {
  int magnitude(T t);
}

class IntMag implements MagnitudeObject<Integer> {
  public int magnitude(Integer x){ if (x >= 0) return x; else return -x; }
}

interface DistanceObject<T> {
  int distance(T t1, T t2);
}

class Signature {

  public static void main(String[] args){
  }

  public static <T> DistanceObject<T> MakeDistanceObject(MagnitudeObject<T> mag){
    return (x,y) -> {
      int v = mag.magnitude(x) - mag.magnitude(y);
      if(v >= 0) return v; else return -v;
    };
  }

}
