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


echo apply-in-underlying-scheme
scm -b -f apply-in-underlying-scheme.scm  > /dev/null               
./run.scm apply-in-underlying-scheme.scm  > /dev/null


echo apply-primitive
scm -b -f apply-primitive.scm             > /dev/null               
./run.scm apply-primitive.scm             > /dev/null


echo apply
scm -b -f apply.scm                       > /dev/null               
./run.scm apply.scm                       > /dev/null


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


echo eval-primitive
scm -b -f eval-primitive.scm              > /dev/null               
./run.scm eval-primitive.scm              > /dev/null


echo eval-procedure
scm -b -f eval-procedure.scm              > /dev/null               
./run.scm eval-procedure.scm              > /dev/null


echo eval
scm -b -f eval.scm                        > /dev/null               
./run.scm eval.scm                        > /dev/null


echo frame1
scm -b -f frame1.scm                       > /dev/null               
./run.scm frame1.scm                       > /dev/null


echo frame2
scm -b -f frame2.scm                       > /dev/null               
./run.scm frame2.scm                       > /dev/null


echo frame3
scm -b -f frame3.scm                       > /dev/null               
./run.scm frame3.scm                       > /dev/null


# echo frame4
# scm -b -f frame4.scm                       > /dev/null               
# ./run.scm frame4.scm                       > /dev/null




