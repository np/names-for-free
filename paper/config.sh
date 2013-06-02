BIBS=(local.bib npouillard.bib)
# generate this
# 

LIBSOURCES=(
  `find NomPaKit MiniTikz -type f`
  ColorizeAgda.hs)

ALLSOURCES=(main.hs
            sigplanconf/sigplanconf.cls
            abstract
            keywords
            "${LIBSOURCES[@]}"
            "${BIBS[@]}")

# TODO extract from cabal file or use cabal directly
PACKAGES=(-hide-all-packages
          -package=Agda
          -package=array
          -package=base
          -package=containers
          -package=directory
          -package=hlatex
          -package=HSH
          -package=mtl
          -package=process
          -package=QuickCheck
          -package=split
          -package=template-haskell
          -package=uniplate
          -package=wl-pprint
         )

# redo arguments
TARGET="$1"
BASE="$2"
DEST="$3"

# -Werror
ghcopts=(-Wall)

rubberopts=()

# Hooks!
# Example:
#case "$TARGET" in
#  jfp.pdf)
#    export BSTINPUTS=../../jfp-class
#    rubberopts=(-I jfp-class)
#    find jfp-class -print0 | xargs -0 redo-ifchange
#  ;;
#esac

copy(){
  redo-ifchange "$1"
  cp "$1" "$DEST"
}

fail(){
  echo "No rule to build $TARGET" >>/dev/stderr
  exit 1
}

redo-ifchange config.sh
