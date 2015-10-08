class Event_Handler;

class Reactor{
  public:
    ~Reactor();
    void run_event_loop();
    void end_event_loop();
    // Attach/detach event handlers
    void register_handler(Event_Handler *event_handler);
    void remove_handler(Event_Handler *event_handler);
    static Reactor *instance(); // Singleton access point
};
