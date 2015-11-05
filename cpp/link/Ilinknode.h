// Ilinknode.h
#ifndef INCLUDED_ILINKNODE
#define INCLUDED_ILINKNODE

class ILinkNode {
  public:
  //
  ~ILinkNode();
  // accessors
  virtual const void* key() const = 0;
  virtual const void* val() const = 0;
  virtual ILinkNode *next() const = 0;
  // manipulators
  virtual void set(const void* value) = 0;  // sets new value (via pointer)
  virtual void setNext(ILinkNode *next) = 0;
};

#endif
