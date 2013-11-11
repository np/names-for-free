. ./config.sh
BASE=main
redo-ifchange "$BASE".hs "${LIBSOURCES[@]}"
runghc "${ghcopts[@]}" "$BASE".hs --comments >"$3"
