foo=0

funct_1 () {
  local foo
  foo=1
  echo "funct_1: foo = $foo"
}

funct_2 () {
  local foo
  foo=2
  echo "funct_2: foo = $foo"
}


echo "global:  foo = $foo"
funct_1
echo "global:  foo = $foo"
funct_2
echo "global:  foo = $foo"

