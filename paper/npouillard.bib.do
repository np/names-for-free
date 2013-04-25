#. ./config.sh
NPOUILLARD_BIB=~/Documents/bib.bib
if [ `whoami` = np ]; then
  redo-ifchange "$NPOUILLARD_BIB"
  cp "$NPOUILLARD_BIB" "$3"
else
  fail
fi
