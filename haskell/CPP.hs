{-# LANGUAGE CPP #-}

#if (__GLASGOW_HASKELL__ > 790)
main = print "yes it is"
#else
main = print "no it is not"
#endif




