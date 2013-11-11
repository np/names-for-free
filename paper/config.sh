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

redo-ifchange ghc-opts.sh
. ./ghc-opts.sh
# OLD static version
#ghcopts=(-hide-all-packages
#          -package=array
#          -package=base
#          -package=containers
#          -package=directory
#          -package=hlatex
#          -package=HSH
#          -package=mtl
#          -package=process
#          -package=QuickCheck
#          -package=split
#          -package=template-haskell
#          -package=uniplate
#          -package=wl-pprint
#          -package=highlighting-kate
#          -package=filepath
#          -Wall
#         )

#ghcopts=("${ghcopts[@]}" -Werror)

# redo arguments
TARGET="$1"
BASE="$2"
DEST="$3"

# -Werror
ghcopts=(-Wall)

rubberopts=()

# to be extended by hooks
runghcprgargs=()

rubberinclude(){
  d="$(pwd)"
  for i; do
    i="$d/$i"
    rubberopts=("${rubberopts[@]}"
                -I "$i"
                -c "bibtex.path $i"
                -c "bibtex.stylepath $i"
                -c "index.path $i"
                -c "makeidx.path $i")
  done
  find "$@" -type f -print0 | xargs -0 redo-ifchange
}

# Hooks!
case "$TARGET" in
  (main.pdf) rubberinclude sigplanconf;;
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
