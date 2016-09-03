public class Universe1 extends Universe {
  private final int _version = 1;
  private int _time = 0;

  @Override
  public void run(){ _time = _time + 1; }

  @Override
  public Time time(){ return Time.fromInt(_time); }

  @Override
  public Version version() { return Version.fromInt(_version); }



}
