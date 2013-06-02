. ./config.sh
redo-ifchange "${ALLSOURCES[@]}"
if git rev-parse --verify -q $REV; then : ; else echo "unexpected value for REV"; exit 42; fi
git archive --prefix=$BASE $REV --output=$BASE.tar.gz -- "${ALLSOURCES[@]}"
