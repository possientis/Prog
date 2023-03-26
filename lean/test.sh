#!/bin/sh

DIR=/home/john/Prog/lean

check(){ 

    echo "${1}"
    lean ${1}.lean
}

main(){
    echo
    echo "testing main folder..."
    echo
    check choice
    check setoid
    check quotient
    check set
#    check funext
    check propext
    check coercions
    check WellFounded
    check Vec
#    check typeclass
    check tactic
    check tacticComb
    check structure
#    check simp
    check semigroup
#    check rewrite
#    check real
    check pattern
    check negation
#    check nat
    check mutual
    check match
    check list
    check instance
#    check inductive
#    check inaccessible
    check implicit
    check have
    check first_order
#    check exists
#    check exercise_7_10_1
#    check exercise_7_10_2
#    check exercise_7_10_3
    check equivalence
#    check eq
#    check divides
    check disjunction
    check decidable
#    check conjunction
    check classical
#    check calc
    check attribute
    echo
    echo 'main test completed successfully'
    echo
}

set -e 
cd ${DIR}

echo
echo "testing lean..."
echo

./while/test.sh
main
./clean.sh
 
echo
echo 'All lean tests completed successfully'
echo
