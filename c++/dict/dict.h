// dict.h
#ifndef INCLUDED_DICT
#define INCLUDED_DICT

class Dictionary_i;
class DictionaryIter;
class Link;


// The object file dict.o does not contain the code relating
// to every possible class K. Refer to the bottom of dict.c
// in order to expand the range of available classes K. Then
// recompile the file dict.c

// current implementation in dict.c requires:
// bool operator==(const K& k1, const K& k2)
// More specifically given k1, k2 of type K, the expression
// 'k1 == k2' needs to compile and return the right value

template <class K>  // keys are of type K
class Dictionary {

  //private data
  Dictionary_i* d_this;   // insulating implementation
  //
  Dictionary(const Dictionary&);              // not implemented
  Dictionary& operator=(const Dictionary&);   // not implemented

  // friends
  friend DictionaryIter;

  public:
  Dictionary();
  ~Dictionary();

  // accessors
  const void* find(const K& key) const;       // returns value associated with key
  bool isCheckOk() const;                     // performs sanity checks
  void debug(                                 // provides debugging out
      void (*printKey)(const void*),
      void (*printValue)(const void*)
      ) const;

  // manipulators
  void insert(const K& key, const void* value);// val changed on duplicate key
  void del(const K& key);

};


#endif
