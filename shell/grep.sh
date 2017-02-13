if grep -q 'daemon:x' /etc/passwd; then
  echo The daemon user is in the passwd file.
else
  echo There is a big problem. daemon is not in the passwd file.
fi
