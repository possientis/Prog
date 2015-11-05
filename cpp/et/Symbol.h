template <typename T> class Component_Node;

template <typename T>
class Symbol {
  Symbol *left;
  Symbol *right;
  public:
  virtual ~Symbol();
  virtual int precedence()=0;
  virtual Component_Node<T> *build()=0;
};
