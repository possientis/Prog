// dict.h
#ifndef INCLUDED_DICT
#define INCLUDED_DICT

class Dictionary_i;
class DictionaryIter;
class Link;


class Dictionary {

  //private data
  Dictionary_i* d_this;   // insulating implementation
  //
  Dictionary(const Dictionary&);              // not implemented
  Dictionary& operator=(const Dictionary&);   // not implemented

  // friends
  friend DictionaryIter;

  public:
  Dictionary(
      int  (*sameKey)(const void*, const void*),
      long (*prehash)(const void*)
      );
  ~Dictionary();

  // accessors
  const void* find(const void* key) const;    // returns value associated with key
  bool isCheckOk() const;                     // performs sanity checks
  void debug(                                 // provides debugging out
      void (*printKey)(const void*),
      void (*printValue)(const void*)
      ) const;

  // manipulators
  void insert(const void* key, const void* value);// val changed on duplicate key
  void del(const void* key);

};


#endif
