# for sh not bash

escseq="\033[s\033[0;0H\033[0;41m\033[K\033[1;33mHello World!\033[0m\033[u"
restore="\033[s\033[0;0H\033[0m\033[K\033[u"

store="\033[s"            # save cursor location
home="\033[0;0H"          # go to line 0 column 0
redback="\033[0;41m"      # set red background color
clearline="\033[K"        # clear current line (hence color it red)
yellowfont="\033[1;33m"   
coloroff="\033[0m"        
load="\033[u"             # restore cursor location


echo -n $escseq
sleep 1
echo -n $restore


echo -n $store
echo -n $home
echo -n "Oh I have left..."
echo -n $load

sleep 1

echo -n $store
echo -n $home
echo -n $redback
echo -n $clearline
echo -n $yellowfont
echo -n "Hello again..."
echo -n $coloroff
echo -n $load

sleep 1
echo -n $restore


