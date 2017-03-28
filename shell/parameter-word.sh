unset param_unset
param_null=
param_set_non_null=hello
word=word

##########################################################################
# :-                                                                     #
##########################################################################

echo 1. ${param_unset:-word}          # word
echo 2. ${param_null:-word}           # word
echo 3. ${param_set_non_null:-word}   # hello


##########################################################################
# :=                                                                     #
##########################################################################

echo 4. ${param_unset:=word}          # word
echo 5. ${param_unset}                # word, variable set to word
unset param_unset                     # restoring state

echo 6. ${param_null:=word}           # word
echo 7. ${param_null}                 # word, variable set to word
param_null=                           # restoring state

echo 8. ${param_set_non_null:=word}   # hello
echo 9. ${param_set_non_null}         # hello, variable not set to word


##########################################################################
# :? (running examples as subshell to prevent main shell termination)    #
##########################################################################

( # subshell (will exit before 'any_command' is attempted) 
  any_command ${param_unset:?"Error: param_unset is unset or null"} 
  echo This will not appear as subshell has exited
)
echo 10. exit status = $?             # exit status = 1 from subshell
echo                                  # exit status = 0

( # subshell (will exit before 'any_command' is attempted)
  any_command ${param_null:?"Error: param_null is unset or null"}
  echo This will not appear as subshell has exited
)
echo 11. exit status = $?             # exit status = 1 from subshell
echo                                  # exit status = 0


##########################################################################
# :+                                                                     #
##########################################################################

echo 12. x${param_unset:+word}x       # xx
echo 13. x${param_null:+word}x        # xx
echo 14. ${param_set_non_null:+word}  # word (not hello)



