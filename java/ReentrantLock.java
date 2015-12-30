public class ReentrantLock {

  public static void main(String[] args){
    LoggingWidget w = new LoggingWidget();
    w.doSomething();
  }
}

class Widget {

  public synchronized void doSomething(){
    System.out.println(toString() + " is calling Widget::doSomething");
  }
}

// object has an intrinsic lock
class LoggingWidget extends Widget {
  public synchronized void doSomething(){ // acquires first lock, count = 1
    System.out.println(toString() + " is calling LoggingWidget::soSomething");
    super.doSomething();                  // acquires same lock count = 2
    // lock is released, count = 1
  }
  // lock finally released, count = 0, can be acquired by someone else
}
// lock is reentrant, when the same owner attempts to reacquire the same lock,
// it does not create a deadlock
