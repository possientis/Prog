// encapsulating nonstandard cancellation in a task with NewTaskfor.
import java.util.concurrent.*;
import java.net.*;
import java.io.*;

public interface CancellableTask<T> extends Callable<T> {
  void cancel();
  RunnableFuture<T> newTask();
}

//ThreadSafe
class CancellingExecutor extends ThreadPoolExecutor {
//  ...
    public CancellingExecutor(){
      super(5, 5, 60, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
    }

    @Override
    protected<T> RunnableFuture<T> newTaskFor(Callable<T> callable) {
      if (callable instanceof CancellableTask)
        return ((CancellableTask<T>) callable).newTask();
      else
        return super.newTaskFor(callable);
    }
}

abstract class SocketUsingTask<T> implements CancellableTask<T> {
  //GuardedBy("this") 
  private Socket socket;
  protected synchronized void setSocket(Socket s) { socket = s; }

  @Override
  public synchronized void cancel() {
    try {
      if (socket != null)
        socket.close();
    } catch (IOException ignored) { }
  }

  @Override
  public RunnableFuture<T> newTask() {
    return new FutureTask<T>(this) {
      public boolean cancel(boolean mayInterruptIfRunning) {
        try {
          SocketUsingTask.this.cancel();
        } finally {
          return super.cancel(mayInterruptIfRunning);
        }
      }
    };
  }
}
