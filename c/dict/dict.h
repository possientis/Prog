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
  Dictionary(int (*)(const void*, const void*));  // creating from comparator
  ~Dictionary();

  // accessors
  const void* find(const void* key) const;    // returns value associated with key
  bool isCheckOk() const;                     // performs sanity checks
  void debug( void (*printKey)(const void*),
              void (*printValue)(const void*)) const;// provides debugging output

  // manipulators
  void insert(const void* key, const void* value);// val changed on duplicate key
  void del(const void* key);

};


#endif
