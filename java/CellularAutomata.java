import java.util.concurrent.*;

public class CellularAutomata {
  private final Board mainBoard;
  private final CyclicBarrier barrier;
  private final Worker[] workers;

  // constructor
  public CellularAutomata(Board board) {
    this.mainBoard = board;
    int count = Runtime.getRuntime().availableProcessors();
    this.barrier = new CyclicBarrier(count, //  <------ count argument for barrier
        new Runnable() {
          public void run() {
            mainBoard.commitNewValues();  // <---------------- executed after all threads have succesfully passed barrier
          }});
    this.workers = new Worker[count];
    for (int i = 0; i < count; i++)
      workers[i] = new Worker(mainBoard.getSubBoard(count, i));
  }

  private class Worker implements Runnable {
    private final Board board;
  
    public Worker(Board board) { this.board = board; }
    public void run() {
      while (!board.hasConverged()) {
        for (int x = 0; x < board.getMaxX(); x++)
          for (int y = 0; y < board.getMaxY(); y++)
            board.setNewValue(x, y, board.computeValue(x, y));
        try {
          barrier.await(); // <------------------------- barrier.await()
        } catch (InterruptedException ex) {
            return;
        } catch (BrokenBarrierException ex) {
        return;
        }
      }
    }
  }
  
  public void start() {
    for (int i = 0; i < workers.length; i++)
      new Thread(workers[i]).start();
    mainBoard.waitForConvergence();
  }
}


class Board {
  public void commitNewValues(){}
  public Board getSubBoard(int count, int index){ return null; }
  public boolean hasConverged(){ return true; }
  public int getMaxX(){ return 0; }
  public int getMaxY(){ return 0; }
  public int computeValue(int x, int y){ return 0; }
  public void setNewValue(int x, int y, int value){}
  public void waitForConvergence(){}
} 
