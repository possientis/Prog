#include <libguile.h>

SCM false = SCM_BOOL_F; // #f
SCM true = SCM_BOOL_T;  // #t 
SCM nil  = SCM_EOL;     // ()

// far more general function
SCM
increment1(SCM a, SCM flag)
{
  SCM result;

  if(scm_is_true(flag))
  {
    result = scm_sum(a, scm_from_int(1));
  }
  else
  {
    result = a;
  }

  return result;
}

SCM
increment2(SCM a, SCM flag)
{
  int result; // ooops, far less general

  if(scm_is_true(flag))
  {
    result = scm_to_int(a) + 1;
  }
  else
  {
    result = scm_to_int(a);
  }

  return scm_from_int(result);
}
