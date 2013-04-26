#. ./config.sh
JPB_BIB=~/repo/gitroot/bibtex/jp.bib
if [ `whoami` = bernardy ]; then
  redo-ifchange "$JPB_BIB"
  cp "$JPB_BIB" "$3"
else
  fail
fi
