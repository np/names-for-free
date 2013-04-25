redo-ifchange "$2".md
pandoc --mathjax -t html -s "$2".md -o $3
sed -i -e 's/^code > span.dt.*$//' \
       -e 's/TODO/<span style="color:red; font-weight:bold">TODO<\/span>/g' $3
