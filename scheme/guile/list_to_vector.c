#include <libguile.h>

SCM
my_list_to_vector(SCM list)
{
  SCM vector = scm_make_vector (scm_length (list), SCM_UNDEFINED);
  size_t len, i;

  len = scm_c_vector_length(vector);
  i = 0;
  while (i < len && scm_is_pair (list))
  {
    scm_c_vector_set_x(vector, i, scm_car(list));
    list = scm_cdr(list);
    i++;
  }

  return vector;
}

SCM
my_pedantic_list_to_vector (SCM list)
{
  SCM vector = scm_make_vector (scm_length (list), SCM_UNDEFINED);
  size_t len, i;

  len = scm_c_vector_length (vector);
  i = 0;
  while (i < len)
  {
    scm_c_vector_set_x (vector, i, scm_car (list));
    list = scm_cdr (list);
    i++;
  }

  return vector;
}
