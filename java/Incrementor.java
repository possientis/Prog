public class Incrementor {

  // see javadoc for automated doc generation from comments
  /**
   * Incrementer constructor
   * @param startValue initial value of internal counter
   */
  public Incrementor(int startValue){

    counter_ = startValue;

  }

  public Incrementor(){

    counter_ = 1;

  }


  /**
   * Returns the current value and then increments internal counter
   */
  public int nextValue(){

    return counter_++;

  }

  public String toString()
  {
    return "<Incrementor object: " + counter_ + " >";
  }

  private int counter_;


}
