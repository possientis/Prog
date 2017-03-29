
# AAAAAAAAAAAAAAAAAAAA
perl -e 'print "A" x 20;'     
echo

# AAAAAAAAAAAAAAAAAAAA
perl -e 'print "\x41" x 20;'  
echo

# AAAAAAAAAAAAAAAAAAAABCDafgiafgiZ
perl -e 'print "A"x20 . "BCD" . "\x61\x66\x67\x69"x2 . "Z";'
echo


# uname
perl -e 'print "uname";'
echo


# uname
var=uname
echo $var

# Linux
echo `uname`  # command substitution: evaluates to output of command

# Linux
echo $(uname) # command substitution: evaluates to output of command

# Linux
echo `$var`

# Linux
echo $($var)

# uname
echo `perl -e 'print "uname";'` # evaluates to output of command

# uname
echo $(perl -e 'print "uname";')

# Linux
`perl -e 'print "uname";'`  # command evaluates to 'uname' -> Linux

# Linux
$(perl -e 'print "uname";') # command evalutes to 'uname' -> Linux

# Linux
una$(perl -e 'print "m";')e

# Linux
u`perl -e 'print "na";'`me

# Linux
u`echo "na"`me

# Linux
uname

# Linux
`echo uname`

#Linux
$(echo `echo uname`)

# Linux
`echo $(echo uname)`

# Linux
$(echo $(echo uname))

# Linux
$(echo $(echo $(echo uname)))










