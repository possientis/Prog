#include <stack>

template <typename T> class Expression_Tree;

template <typename T>
class ET_Iterator_Impl{
  public:
    ET_Iterator_Impl(const Expression_Tree<T> &);
    virtual ~ET_Iterator_Impl();
    virtual Expression_Tree<T> operator *()=0;
    virtual void operator++()=0;
    virtual bool operator==(const ET_Iterator_Impl &)=0;
    virtual bool operator!=(const ET_Iterator_Impl &)=0;
    virtual ET_Iterator_Impl *clone()=0; // subclass performs a deep copy
};

template <typename T>
class Pre_Order_ET_Iterator_Impl : public ET_Iterator_Impl<T>{
  public:
    Pre_Order_ET_Iterator_Impl(const Expression_Tree<T> &root){
      if(!root.is_null()) stack_.push(root);}
    virtual Expression_Tree<T> operator *() {return stack_.top();}
    virtual void operator++(){
      if(!stack_.is_empty()){
        Expression_Tree<T>  current = stack_.top(); stack_.pop();
        if(!current.right().is_null())
          stack_.push(current.right());
        if(!current.left().is_null())
          stack_.push(current.left());
      }
    }
    // more

  private:
    std::stack<Expression_Tree<T>> stack_;

};
