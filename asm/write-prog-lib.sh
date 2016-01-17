#!/bin/sh
as --32 write-prog.s -o write-prog.o
ld -melf_i386 -L . -dynamic-linker /lib/ld-linux.so.2 \
  -o write-prog -lrecord write-prog.o

# --32            -> 32 bit assembly
# -melf_i386      -> 32 bit assembly
# -L .            -> look for library in directory '.'
# -dynamic-linker /lib/ld-linux.so.2 -> binary for dynamic linker
# -o write-prog   -> name of produced executable
# -lrecord        -> library is called 'librecord.so' just like ...
# -lc             -> library is called 'libc.so' (not relevant here)

# At this stage of the shell, the executable 'write-prog' has been
# produced, but it will not run. This is because by default, the
# dynamic linker only searches /lib, /usr/lib and whatever directories
# are listed in /etc/ld.so.conf for libraries. This seems like a 
# paradox since we did go through the trouble of specifying the 
# full location of the file 'librecord.so' when creating the executable
# (-L . -lrecord). This information is seemingly not part of the 
# executable file, or if it is, it is ignored by the dynamic-linker.
# anyway, in order to run the program you either need to move the 
# library  to obe of these directories, or set the environment 
# variable LD_LIBRARY_PATH as follows:

LD_LIBRARY_PATH=.; export LD_LIBRARY_PATH


./write-prog
rm write-prog.o
