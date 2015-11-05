class ET_Iterator_Impl;
template <typename T> class Expression_Tree;

// interface consistent with STL rather than GOF
template <typename T>
class ET_Iterator{
  public:
  ET_Iterator(ET_Iterator_Impl *);
  ET_Iterator(const ET_Iterator &);
  Expression_Tree<T> operator *();
  const Expression_Tree<T> operator *() const;
  ET_Iterator &operator++();
  ET_Iterator &operator++(int);
  bool operator==(const ET_Iterator &rhs);
  bool operator!=(const ET_Iterator &rhs);
  ~ET_Iterator();
};


