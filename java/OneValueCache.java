import java.math.*;
import java.util.*;

// Immutable holder for caching a number and its factors
class OneValueCache {
  private final BigInteger lastNumber;
  private final BigInteger[] lastFactors;
  public OneValueCache(BigInteger i,
      BigInteger[] factors) {
    lastNumber = i;
    lastFactors = Arrays.copyOf(factors, factors.length);
  }
  public BigInteger[] getFactors(BigInteger i) {
    if (lastNumber == null || !lastNumber.equals(i))
      return null;
    else
      return Arrays.copyOf(lastFactors, lastFactors.length);
  }
}

// thread-safe without explicit locking
class VolatileCachedFactorizer {
  // volatile reference to immutable object
  private volatile OneValueCache cache = new OneValueCache(null, null);
  public void service(ServletRequest req, ServletResponse resp) {
    BigInteger i = extractFromRequest(req);
    BigInteger[] factors = cache.getFactors(i);
    if (factors == null) {
      factors = factor(i);
      cache = new OneValueCache(i, factors);
    }
    encodeIntoResponse(resp, factors);
  }
  private static BigInteger extractFromRequest(ServletRequest req){
    return null;
  }

  private static BigInteger [] factor(BigInteger i){
    return null;
  }

  private static void encodeIntoResponse(ServletResponse resp, BigInteger[] factors){
  }

}

class ServletRequest {
}
class ServletResponse {
}
