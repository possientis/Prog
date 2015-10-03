template <typename T> class Leaf_Node;
template <typename T> class Composite_Negate_Node;
template <typename T> class Composite_Add_Node;
template <typename T> class Composite_Subtract_Node;
template <typename T> class Composite_Divide_Node;
template <typename T> class Composite_Multiply_Node;

template<typename T>
class ET_Visitor{
  public:
  virtual void visit(const Leaf_Node<T> &node)=0;
  virtual void visit(const Composite_Negate_Node<T> &node)=0;
  virtual void visit(const Composite_Add_Node<T> &node)=0;
  virtual void visit(const Composite_Subtract_Node<T> &node)=0;
  virtual void visit(const Composite_Divide_Node<T> &node)=0;
  virtual void visit(const Composite_Multiply_Node<T> &node)=0;
};

template<typename T>
class Print_Visitor : public ET_Visitor<T>{
  public:
  virtual void visit(const Leaf_Node<T> &node);
  virtual void visit(const Composite_Negate_Node<T> &node);
  virtual void visit(const Composite_Add_Node<T> &node);
  virtual void visit(const Composite_Subtract_Node<T> &node);
  virtual void visit(const Composite_Divide_Node<T> &node);
  virtual void visit(const Composite_Multiply_Node<T> &node);
};

template<typename T>
class Evaluation_Visitor : public ET_Visitor<T>{
  public:
  virtual void visit(const Leaf_Node<T> &node);
  virtual void visit(const Composite_Negate_Node<T> &node);
  virtual void visit(const Composite_Add_Node<T> &node);
  virtual void visit(const Composite_Subtract_Node<T> &node);
  virtual void visit(const Composite_Divide_Node<T> &node);
  virtual void visit(const Composite_Multiply_Node<T> &node);
};



