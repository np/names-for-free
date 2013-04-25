redo-ifchange "$2".hs
grep '^ *\(\[agdaF\?P\||\)' "$2".hs |
  grep -v 'and stop  with' |
  grep -v 'and stops at the end' |
  grep -v '{|' |
  sed -e 's/\[agdaF\?P|//' \
      -e 's/^ *|]\?//' \
      -e 's/^\(.\)/  \1/' \
      -e 's/[☐ ]/ /g' \
      -e 's/  *$//'
