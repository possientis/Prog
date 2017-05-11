#include <immintrin.h>

// restricted transactional memory
// gcc -mrtm ...
// illegal instruction error at runtime ...

int n_tries, max_tries = 100;
unsigned status = _XABORT_EXPLICIT;

int main()
{

  for (n_tries = 0; n_tries < max_tries; n_tries++){
    status = _xbegin ();
    if (status == _XBEGIN_STARTED || !(status & _XABORT_RETRY))
      break;
  }

  if (status == _XBEGIN_STARTED){
  //  ... transaction code...
    _xend ();
  }
  else
  {
  // ... non-transactional fallback path...
  }

  return 0;
}
