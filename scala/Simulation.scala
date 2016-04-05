package simulator

abstract class Simulation {

  type Action = () => Unit    // Action is an alias of () => Unit

  case class WorkItem(time: Int, action: Action)

  private var curtime = 0
  def currentTime: Int = curtime

  private var agenda: List[WorkItem] = List()

  private def insert(ag: List[WorkItem], item: WorkItem): List[WorkItem] =
    if (ag.isEmpty || item.time < ag.head.time) item :: ag
    else ag.head :: insert(ag.tail, item)

  def afterDelay(delay: Int)(block: => Unit) {  // using block
  // => Unit is the type of all computations of type Unit which is passed byname (by-name)
  // Recall that callbyname (call-by-name) parameters are not evaluated when passed to a method 
    val item = WorkItem(currentTime + delay, () => block)
    agenda = insert(agenda, item)
  }

  private def next() {
    (agenda: @unchecked) match {
      case item :: rest =>
        agenda = rest;
        curtime = item.time
        item.action()
    }
  }

  def run() {
    afterDelay(0) { // using block
    println("*** simulation started, time = " + currentTime + " ***")
    }
    while (!agenda.isEmpty) next()
  }
}
