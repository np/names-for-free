. ./config.sh
# Here we over approx deps&pkgs with LIBSOURCES&PACKAGES
redo-ifchange "$BASE" "${LIBSOURCES[@]}"
runghc "${ghcopts[@]}" "${PACKAGES[@]}" "$BASE" -- "${runghcprgargs[@]}" >"$3"
