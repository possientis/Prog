
echo "`seq 10 | sed -e 's/.*/export var&=ZZZZZZZ/'`"

# export var1=ZZZZZZZ
# export var2=ZZZZZZZ
# export var3=ZZZZZZZ
# export var4=ZZZZZZZ
# export var5=ZZZZZZZ
# export var6=ZZZZZZZ
# export var7=ZZZZZZZ
# export var8=ZZZZZZZ
# export var9=ZZZZZZZ
# export var10=ZZZZZZZ

eval "`seq 10 | sed -e 's/.*/export var&=ZZZZZZZ/'`"

echo "var1 = $var1" # var1 = ZZZZZZZ
echo "var2 = $var2" # var2 = ZZZZZZZ
echo "var3 = $var3" # var3 = ZZZZZZZ
echo "var4 = $var4" # var4 = ZZZZZZZ
echo "var5 = $var5" # var5 = ZZZZZZZ
echo "var6 = $var6" # var6 = ZZZZZZZ
echo "var7 = $var7" # var7 = ZZZZZZZ
echo "var8 = $var8" # var8 = ZZZZZZZ
echo "var9 = $var9" # var9 = ZZZZZZZ
echo "var10 = $var10" # var10 = ZZZZZZZ

