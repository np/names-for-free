. ./config.sh
BASE=main
redo-ifchange "$BASE".hs "${LIBSOURCES[@]}"
runghc "${ghcopts[@]}" "${PACKAGES[@]}" "$BASE".hs --agda >"$3"
