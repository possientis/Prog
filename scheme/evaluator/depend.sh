#!/bin/sh

echo analyze-procedure
scm -b -f analyze-procedure.scm           > /dev/null
./run.scm analyze-procedure.scm           > /dev/null

echo analyze
scm -b -f analyze.scm                     > /dev/null               
./run.scm analyze.scm                     > /dev/null

echo and
scm -b -f and.scm                         > /dev/null               
./run.scm and.scm                         > /dev/null

echo application
scm -b -f application.scm                 > /dev/null               
./run.scm application.scm                 > /dev/null

echo assignment
scm -b -f assignment.scm                  > /dev/null               
./run.scm assignment.scm                  > /dev/null

echo begin
scm -b -f begin.scm                       > /dev/null               
./run.scm begin.scm                       > /dev/null

echo cond
scm -b -f cond.scm                        > /dev/null               
./run.scm cond.scm                        > /dev/null

echo defined-primitive
scm -b -f defined-primitive.scm           > /dev/null               
./run.scm defined-primitive.scm           > /dev/null

echo defined
scm -b -f defined.scm                     > /dev/null               
./run.scm defined.scm                     > /dev/null

echo definition
scm -b -f definition.scm                  > /dev/null               
./run.scm definition.scm                  > /dev/null

echo dictionary-test
scm -b -f dictionary-test.scm             > /dev/null               
./run.scm dictionary-test.scm             > /dev/null

echo dict
scm -b -f dict.scm                        > /dev/null               
./run.scm dict.scm                        > /dev/null

echo environment1
scm -b -f environment1.scm                > /dev/null               
./run.scm environment1.scm                > /dev/null

echo environment 
scm -b -f environment.scm                 > /dev/null               
./run.scm environment.scm                 > /dev/null

echo environment-test
scm -b -f environment-test.scm            > /dev/null               
./run.scm environment-test.scm            > /dev/null

echo eval-mode
scm -b -f eval-mode.scm                   > /dev/null               
./run.scm eval-mode.scm                   > /dev/null

echo eval-procedure
scm -b -f eval-procedure.scm              > /dev/null               
./run.scm eval-procedure.scm              > /dev/null

echo file-to-code
scm -b -f file-to-code.scm                > /dev/null               
./run.scm file-to-code.scm                > /dev/null

echo frame1
scm -b -f frame1.scm                      > /dev/null               
./run.scm frame1.scm                      > /dev/null

echo frame2
scm -b -f frame2.scm                      > /dev/null               
./run.scm frame2.scm                      > /dev/null

echo frame3
scm -b -f frame3.scm                      > /dev/null               
./run.scm frame3.scm                      > /dev/null


# echo frame4
# scm -b -f frame4.scm                       > /dev/null               
# ./run.scm frame4.scm                       > /dev/null

echo frame
scm -b -f frame.scm                       > /dev/null               
./run.scm frame.scm                       > /dev/null

echo frame-test
scm -b -f frame-test.scm                  > /dev/null               
./run.scm frame-test.scm                  > /dev/null

echo global-env
scm -b -f global-env.scm                  > /dev/null               
./run.scm global-env.scm                  > /dev/null

echo if
scm -b -f if.scm                          > /dev/null               
./run.scm if.scm                          > /dev/null

echo lambda
scm -b -f lambda.scm                      > /dev/null               
./run.scm lambda.scm                      > /dev/null

echo lazy-apply
scm -b -f lazy-apply.scm                  > /dev/null               
./run.scm lazy-apply.scm                  > /dev/null

echo lazy-eval
scm -b -f lazy-eval.scm                   > /dev/null               
./run.scm lazy-eval.scm                   > /dev/null

echo let-rec
scm -b -f let-rec.scm                     > /dev/null               
./run.scm let-rec.scm                     > /dev/null

echo let
scm -b -f let.scm                         > /dev/null               
./run.scm let.scm                         > /dev/null

echo let-star
scm -b -f let-star.scm                    > /dev/null               
./run.scm let-star.scm                    > /dev/null

echo named-let
scm -b -f named-let.scm                   > /dev/null               
./run.scm named-let.scm                   > /dev/null

echo new-apply
scm -b -f new-apply.scm                   > /dev/null               
./run.scm new-apply.scm                   > /dev/null

echo new-display
scm -b -f new-display.scm                 > /dev/null               
./run.scm new-display.scm                 > /dev/null

echo new-eval
scm -b -f new-eval.scm                    > /dev/null               
./run.scm new-eval.scm                    > /dev/null

echo new-load
scm -b -f new-load.scm                    > /dev/null               
./run.scm new-load.scm                    > /dev/null

echo new-map
scm -b -f new-map.scm                     > /dev/null               
./run.scm new-map.scm                     > /dev/null

echo new-object-to-string
scm -b -f new-object-to-string.scm        > /dev/null               
./run.scm new-object-to-string.scm        > /dev/null

echo new-require
scm -b -f new-require.scm                 > /dev/null               
./run.scm new-require.scm                 > /dev/null

echo not
scm -b -f not.scm                         > /dev/null               
./run.scm not.scm                         > /dev/null

echo or
scm -b -f or.scm                          > /dev/null               
./run.scm or.scm                          > /dev/null

echo primitive-procedure
scm -b -f primitive-procedure.scm         > /dev/null               
./run.scm primitive-procedure.scm         > /dev/null

echo primitive
scm -b -f primitive.scm                   > /dev/null               
./run.scm primitive.scm                   > /dev/null

echo quote
scm -b -f quote.scm                       > /dev/null               
./run.scm quote.scm                       > /dev/null

echo self-evaluating
scm -b -f self-evaluating.scm             > /dev/null               
./run.scm self-evaluating.scm             > /dev/null

echo strict-eval
scm -b -f strict-eval.scm                 > /dev/null               
./run.scm strict-eval.scm                 > /dev/null

echo tagged-list
scm -b -f tagged-list.scm                 > /dev/null               
./run.scm tagged-list.scm                 > /dev/null

echo thunk
scm -b -f thunk.scm                       > /dev/null               
./run.scm thunk.scm                       > /dev/null

echo true-false 
scm -b -f true-false.scm                  > /dev/null               
./run.scm true-false.scm                  > /dev/null

echo unspecified 
scm -b -f unspecified.scm                 > /dev/null               
./run.scm unspecified.scm                 > /dev/null

echo variable
scm -b -f variable.scm                    > /dev/null               
./run.scm variable.scm                    > /dev/null
