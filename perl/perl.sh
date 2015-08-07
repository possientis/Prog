#!/usr/bin/perl
# repl.pl
# A simple REPL for Perl
#
# Copyright (c) 2014 by Jim Lawless (jimbo@radiks.net)
# MIT / X11 license
# See: http://www.mailsend-online.com/license2014.php

$t="\"Jimbo's Perl REPL\"";
while($t) {
     chomp $t;
        print eval($t),"\n";
           $t=<STDIN>;
         }
