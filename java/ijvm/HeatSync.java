class HeatSync {

  private int[] intArray = new int[10];

  synchronized void reverseOrder() {

    int halfWay = intArray.length / 2;

    for (int i = 0; i < halfWay; ++i) {
      int upperIndex = intArray.length - 1 - i;
      int save = intArray[upperIndex];
      intArray[upperIndex] = intArray[i];
      intArray[i] = save;
    }

  }

}
