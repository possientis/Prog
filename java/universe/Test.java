public class Test {
  public static void main(String[] args) throws Exception{


    Universe universe = Universe.fromVersion(Version.fromInt(1));

    System.out.println("time = " + String.valueOf(universe.time().toInt()));
    universe.run();
    System.out.println("time = " + String.valueOf(universe.time().toInt()));


  }
}
