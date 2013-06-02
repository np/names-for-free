. ./config.sh

case "$BASE" in
  (main)
    redo-ifchange "$BASE".hs "${LIBSOURCES[@]}"
    # side productions *.hi *.o
    ghc --make "${ghcopts[@]}" "${PACKAGES[@]}" "$BASE".hs -o "$3" >>/dev/stderr
    ;;
  (*)
    exit 1

   # If we need to we can do it like that
   #redo-ifchange main.bin
   #echo "$(pwd)/main.bin $BASE" >"$DEST"
   #chmod +x "$DEST"
    ;;
esac
