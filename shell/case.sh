# This works with sh and bash

variable=$1

case "$variable" in
  abc)  echo "\$variable = abc" ;;  # double semicolon
  def)  echo "\$variable = def" ;;  # double semicolon 
esac

