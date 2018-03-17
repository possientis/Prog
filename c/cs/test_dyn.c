#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>


int main() {

    void *handle;
    void (*func)();

    handle = dlopen("./baz.so",RTLD_LAZY);
    if (!handle) {
        fprintf(stderr, "%s\n", dlerror());
        exit(1);
    }

    func = dlsym(handle,"baz");
    if (!func) {
        fprintf(stderr, "%s\n", dlerror());
        exit(1);
    }

    func();

    if (dlclose(handle) < 0) {
        fprintf(stderr, "%s\n", dlerror());
        exit(1);
    }

    return 0;
}

    
