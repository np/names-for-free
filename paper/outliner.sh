#!/bin/sh
[ $# = 0 ] || exit 1
ruby -e 'puts STDIN.read.gsub(/^([^\n]*\{[^}\n]*)\n%paragraphName: /m,'"'\\1 ')" | \
ruby -e 'puts STDIN.read.gsub(/^([^\n]*\{[^}\n]*)\n/m,'"'\\1 ')" | \
  grep '%paragraphName:\|^\\\(sub\)*section\|^\\paragraph' | \
  sed -Ee 's/\{\\!\}//g' \
       -e 's/\\textcolor[][{},0-9cymkrgb.]*\{([^}]*)\}/\1/g' \
       -e 's/\\text(tt|sc|bf|color[][{},0-9cymkrgb.]*)\{([^}]*)\}/\2/g' \
       -e 's/\\text(tt|sc|bf|color[][{},0-9cymkrgb.]*)\{([^}]*)\}/\2/g' \
       -e 's/\\emph\{([^}]*)\}/**\1**/g' \
       -e 's/\$ *([^ $]*) *\$/\1/g' \
       -e 's/\$ *([^$]*) *\$/\1/g' \
       -e 's/\\alpha/α/g' \
       -e 's/\\lambda/λ/g' \
       -e 's/\\mu/μ/g' \
       -e 's/\\Pi/Π/g' \
       -e 's/\\Sigma/Σ/g' \
       -e 's/\\bigcirc/◯/g' \
       -e 's/\\textsuperscript\{N\}/ᴺ/g' \
       -e 's/\\ensuremath\{\\ell\}/ℓ/g' \
       -e "s/[{}]//g" \
       -e "s/''/”/g" \
       -e 's/``/“/g' \
       -e 's/\\&/\&/g' \
       -e 's/  */ /g' \
       -e 's/^\\chapter\*?([^\\]*)(\\label.*)?$/\1/' \
       -e 's/^\\section\*?([^\\]*)(\\label.*)?$/ \1/' \
       -e 's/^\\subsection\*?([^\\]*)(\\label.*)?$/  \1/' \
       -e 's/^\\subsubsection\*?([^\\]*)(\\label.*)?$/   \1/' \
       -e 's/^\\paragraph\*?([^\\]*)(\\label.*)?$/    \1/' \
       -e 's/^\%paragraphName: *$/     TODO/' \
       -e 's/^\%paragraphName: */     /' \
       -e 's/^\%code: */     code/' | \
  grep -v '^ *$'
echo '# vim: foldmethod=indent'
echo '# vim: shiftwidth=1'
echo '# vim: cc='
