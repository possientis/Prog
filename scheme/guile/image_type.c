#include <libguile.h>

struct image {
  int width, height;
  char *pixels;

  /* The name of this image */
  SCM name;

  /* A function to call when this image is
  modified, e.g., to update the screen,
  or SCM_BOOL_F if no action necessary */
  SCM update_func;
};

static scm_t_bits image_tag;

SCM mark_image(SCM img){}
size_t free_image(SCM img){}
int print_image(SCM img, SCM what,SCM ){}

void
init_image_type (void)
{
  image_tag = scm_make_smob_type ("image", sizeof (struct image));
  scm_set_smob_mark (image_tag, mark_image);
  scm_set_smob_free (image_tag, free_image);
  scm_set_smob_print (image_tag, print_image);
}
