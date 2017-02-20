# creating archive from shell directory
# output piped into archive extraction 

tar cf - ../shell | ( tar xvf - )
