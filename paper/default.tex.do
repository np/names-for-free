. ./config.sh

runghcmode=1

if (( runghcmode )); then
  redo-ifchange "$BASE".hs "${LIBSOURCES[@]}"
  CMD=(runghc "${ghcopts[@]}" "${PACKAGES[@]}" "$BASE".hs)
else
  redo-ifchange "$2".bin
  CMD=(./"$2".bin)
fi

"${CMD[@]}" --tex > "$3"
sed -e 's/^%.*//' < "$3" | show-non-ascii >>/dev/stderr || :
