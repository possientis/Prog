class ET_Visitor;

template <typename T>
class Component_Node{
  // important to have destructor virtual. Otherwise, when destructing
  // base pointer to derived object, the derived destructor won't be called
  virtual ~Component_Node()=0;
  virtual T item() const;
  virtual Component_Node *left() const;
  virtual Component_Node *right() const;
  virtual void accept(ET_Visitor &visitor) const;
};
