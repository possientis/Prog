var=$1


(( res1 = var<98?9:21 ))

#same as
if [ "$var" -lt 98 ]
then
    res2=9
else
    res2=21
fi

echo $res1
echo $res2


