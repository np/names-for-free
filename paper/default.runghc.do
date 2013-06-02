. ./config.sh
# Here we over approx deps&pkgs with LIBSOURCES&PACKAGES
redo-ifchange "$BASE".hs "${LIBSOURCES[@]}"
runghc "${ghcopts[@]}" "${PACKAGES[@]}" "$BASE".hs -- "${runghcprgargs[@]}" >"$3"
