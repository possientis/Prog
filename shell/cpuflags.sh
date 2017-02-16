FLAGS=$(grep ^flags /proc/cpuinfo| sed 's/.*: //' | head -1)

for f in $FLAGS; do
  case $f in
    fpu) MSG="floating point unit" ;;
    3dnow) MSG="3DNOW graphics extensions" ;;
    mtrr) MSG="memory type range register" ;;
    *)  MSG="unknown" ;;
  esac

  echo $f: $MSG

done
