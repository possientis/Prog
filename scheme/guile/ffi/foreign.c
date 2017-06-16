/* dummy shared library */

int foreign_int = 45;




typedef struct {
  const char* name;
} bottle_t;

bottle_t foreign_bottle = {"Chateau Haut-Brion"};

const char* bottle_content(const bottle_t* bottle) {
  return bottle->name;
}


