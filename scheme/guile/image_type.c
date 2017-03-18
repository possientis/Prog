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

SCM mark_image(SCM);

void
init_image_type (void)
{
  image_tag = scm_make_smob_type ("image", sizeof (struct image));
  scm_set_smob_mark (image_tag, mark_image);
  scm_set_smob_free (image_tag, free_image);
  scm_set_smob_print (image_tag, print_image);
}

SCM
make_image(SCM name, SCM s_width, SCM s_height)
{
  SCM smob;
  struct image *image;
  int width = scm_to_int(s_width);
  int height = scm_to_int(s_height);

  // step 1: allocate the memory block (exception thrown if fails)
  image = (struct image *) scm_gc_malloc(sizeof(struct image),"image");

  // step 2: initialize it with straight code
  image->width = width;
  image->height = height;
  image->pixels = NULL;
  image->name = SCM_BOOL_F;
  image->update_func = SCM_BOOL_F;

  // step 3: create the smob (exception thrown if fails)
  smob = scm_new_smob(image_tag, image);

  // step 4: finish the initialization
  image->name = name;

  // exception thrown if fails
  // telling garbage collector there is no need to scan buffer for pointers
  image->pixels = scm_gc_malloc_pointerless (width*height, "image pixels");

  return smob;
}

SCM
clear_image(SCM image_smob)
{
  int area;
  struct image *image;

  scm_assert_smob_type(image_tag, image_smob);

  image = (struct image *) SCM_SMOB_DATA(image_smob);
  area = image->width * image->height;
  memset(image->pixels, 0, area); 

  // invoke the image update function
  if (scm_is_true(image->update_func))
    scm_call_0 (image->update_func);

  scm_remember_upto_here_1(image_smob);
  
  return  SCM_UNSPECIFIED;

}

// keep the code minimal
// written for illustration, not need as we used scm_gc_...
SCM
mark_image (SCM image_smob)
{

  /* Mark the image’s name and update function. */
  struct image *image = (struct image *) SCM_SMOB_DATA (image_smob);
  scm_gc_mark (image->name);
  scm_gc_mark (image->update_func);
  return SCM_BOOL_F;
}

// keep the code minimal
// written for illustration, not need as we used scm_gc_...
size_t
free_image(SCM image_smob)
{
  struct image *image = (struct image *) SCM_SMOB_DATA (image_smob);

  scm_gc_free (image->pixels, image->width * image->height, "image pixels");

  scm_gc_free (image, sizeof (struct image), "image");

  return 0;
}






