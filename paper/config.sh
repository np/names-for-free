BIBS=(local.bib npouillard.bib)
# generate this
# 

LIBSOURCES=(
  `find Paper Kit MiniTikz -type f -name '*.hs'`
  Kit.hs)

ALLSOURCES=(main.hs
            sigplanconf/sigplanconf.cls
            abstract
            keywords
            "${LIBSOURCES[@]}"
            "${BIBS[@]}")

# TODO extract from cabal file or use cabal directly
PACKAGES=(-hide-all-packages
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
          -package=highlighting-kate
          -package=filepath
         )

# redo arguments
TARGET="$1"
BASE="$2"
DEST="$3"

# -Werror
ghcopts=(-Wall)

rubberopts=()

# to be extended by hooks
runghcprgargs=()

# Hooks!
case "$TARGET" in
  (main.pdf)
    rubberopts=(-I sigplanconf)
    find sigplanconf -type f -print0 | xargs -0 redo-ifchange
    ;;
  (TestPaperCode.hs.runghc)
    redo-ifchange PaperCode.hs;;
esac

copy(){
  redo-ifchange "$1"
  cp "$1" "$DEST"
}

fail(){
  echo "No rule to build $TARGET" >>/dev/stderr
  exit 1
}

redo-ifchange config.sh
