# shell function demo

# first possible syntax for functions
function funct2 {
  echo "Step 2"
  return
}

# second possible syntax
funct3 () {
  echo "Step 3"
  return
}



# main program 

echo "Step 1"
funct2
funct3
echo "Step 4"
