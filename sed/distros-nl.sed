# sed script to produce Linux destribution report

1 i\
\\:\\:\\:\
\
Linux Distributions Report\
\
Released    Name    Version\
--------    ----    -------\
\\:\\:
s/\([0-9]\{2\}\)\/\([0-9]\{2\}\)\/\([0-9]\{4\}\)/\2-\1-\3/
$ i\
\\:\
\
End Of Report

