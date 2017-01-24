#bash and sh

for i in 1 2 3 4 5 6 7 8 9 10   # First loop
do
  echo -n "$i "; sleep 1
done &  # Run loop in background, may execute after second loop

echo    # This 'echo' sometimes will not display 

for i in 11 12 13 14 15 16 17 18 19 20  # Second loop
do
  echo -n "$i "; sleep 1
done

echo    # This 'echo' sometimes will not display

# The expected output from the script:
# 1 2 3 4 5 6 7 8 9 10
# 11 12 13 14 15 16 17 18 19 20

# Sometimes, though, you get:
# 11 12 13 14 15 16 17 18 19 20
# 1 2 3 4 5 6 7 8 9 10 john $
# (The second 'echo' doesn't execute. Why?)

# Occasionally also:
# 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
# (The first 'echo' doesn't execute. Why?)

# Very rarely something like:
# 11 12 13 1 2 3 4 5 6 7 8 9 10 14 15 16 17 18 19 20
# The foreground loop preempts the background one

exit 0

# Nasimuddin Ansari suggests adding sleep 1
#+ after the two echo -n "$i" for some real fun.
