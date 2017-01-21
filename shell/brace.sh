# bash only

echo \"{These,words,are,quoted}\" # "These" "words" "are" "quoted"


echo -n "abc" > log1
echo -n "def" > log2
echo -n "ghi" > log3

cat {log1,log2,log3} > log.txt  # concatenates log1 log2 log3 into log
cat log.txt                     # abcdefghi
rm {log1,log2,log3}

cp log.{txt,bak}                # cp log.txt log.bak
cat log.bak                     # abcdefghi 

rm log.{txt,bak}

echo 
echo {dog,cat}\ :{\ A," B",' C'}  # dog : A dog : B dog : C cat : A cat : B cat : C

echo {a..z} # a b c d e f g h i j k l m n o p q r s t u v w x y z
echo {0..3} # 0 1 2 3

a=123
{ a=321; }  # anonymous function but variable global
echo "a = $a" # a = 321





