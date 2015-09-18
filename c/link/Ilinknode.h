// Ilinknode.h
#ifndef INCLUDED_ILINKNODE
#define INCLUDED_ILINKNODE

class ILinkNode {
  public:
  ILinkNode();
  ~ILinkNode();
  virtual const void* key() const = 0;
  virtual const void* val() const = 0;
  virtual ILinkNode *next() const = 0;
  virtual void set(const void* value) = 0;  // changes pointer to value
  virtual void setNext(ILinkNode *next) = 0;
};

#endif
