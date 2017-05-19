#!/bin/sh

# Returns the number of types of programming languages
# which have been worked on since the last github sync.

# The script simply returns the number of unique file
# extensions which appear from the 'git status' command,
# where .h files and.c files are identified etc.

if [ -n "$1" ]; then
  debug=1   # set to 1 for debugging info
else
  debug=0
fi


# getting output of 'git status' command
changed=$(git status | grep ":  ")

if [ $debug -eq "1" ]; then echo "$changed"; echo; fi

# filtering out everything which is not a file name
# with some extension
filtered=$( \
  for item in $changed; \
  do echo $item; \
  done \
  | grep -v "modified:" \
  | grep -v "renamed:" \
  | grep -v "^new$" \
  | grep -v "^->$" \
  | grep -v "file:" \
  | grep -v 'deleted:' \
  | grep -v '.out' \
  | grep -v '.vim' \
  | grep -v '.txt' \
  | grep -v '.pdf' \
  | grep -v '.gdbinit' \
  | grep -v '.vimrc' \
  | grep -v '.dircolors' \
  | grep -v '.mem' \
  | grep '\.' \
  )

if [ $debug -eq "1" ]; then echo "$filtered"; echo; fi

# keeping only file extensions, sorting and removing 
# duplicates, with the following identifications:

# .h files are viewed as .c files
# .hpp files are viewed as .hpp files
# .y and .txt files are viewed as .l files 

extensions=$( \
  for item in $filtered; \
  do echo ${item##*.}; \
  done \
  | sed 's/^h$/c/g' \
  | sed 's/^hpp$/cpp/g' \
  | sed 's/^y$/l/g' \
  | sed 's/^ac$/m4/g' \
  | sed 's/^am$/m4/g' \
  | sed 's/^in$/m4/g' \
  | sed 's/^jar$/java/g' \
  | sed 's/^bin$/asm/g' \
  | sort \
  | uniq \
  )

if [ $debug -eq "1" ]; then echo "$extensions"; echo; fi

# if not in debug mode then bring back 'git status' output
if [ ! $debug -eq "1" ]; then
  git status
fi

# returning the number of file extensions left
echo "Total number of languages: $(echo "$extensions" | wc -l)"
echo "$changed" | grep -v "deleted:"


