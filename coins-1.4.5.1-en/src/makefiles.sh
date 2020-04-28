#!/bin/sh
find . -type f -name '*.java' -print | \
gawk '{
       sub("\./", "");
       gsub("/", "\\");
       print $1;
     }' > files
