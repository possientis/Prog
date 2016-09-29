public abstract class Ring
{
  public abstract Number zero();
  public abstract Number one();
  public abstract Number signedFromBytes(byte[] val);   // input big-endian
  public abstract Number unsignedFromBytes(byte[] val); // input big-endian

}



