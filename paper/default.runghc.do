. ./config.sh
# Here we over approx deps&pkgs with LIBSOURCES&ghcopts
redo-ifchange "$BASE" "${LIBSOURCES[@]}"
runghc "${ghcopts[@]}" "$BASE" -- "${runghcprgargs[@]}" >"$3"
