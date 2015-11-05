#include <string> // std::string
#include <memory> // std::shared_ptr<T>

template <typename T> class Component_Node;
class ET_Visitor;
template <typename T> class ET_Iterator;
template <typename T> class const_ET_Iterator;



template<typename T>
class Expression_Tree{
  public:
    Expression_Tree(Component_Node<T> *root): root_(root){}
    Expression_Tree(const Expression_Tree &t);
    void operator=(const Expression_Tree &t);
    ~Expression_Tree();
    bool is_null() const;
    int item() const; // why declare const int item()...?
    Expression_Tree left();
    Expression_Tree right();
    void accept(ET_Visitor &visitor){root_->accept(visitor);}
    ET_Iterator<T> begin(const std::string &order = "");
    ET_Iterator<T> end(const std::string &ordder = "");
    const_ET_Iterator<T> begin(const std::string &order = "") const;
    const_ET_Iterator<T> end(const std::string &order = "") const;
  private:
    std::shared_ptr<Component_Node<T>> root_;
};
