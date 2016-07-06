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








