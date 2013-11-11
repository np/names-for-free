redo-ifchange *.cabal
cabal build -v2 \
  | grep 'ghc --make .*main.hs' \
  | head -n 1 \
  | sed -e 's/.*-hide-all-packages/ghcopts=(-hide-all-packages/' \
  | sed -e 's/ -\(package-id\|package-db\) / -\1=/g' \
  | sed -e 's/ .\/main.hs//' \
  | sed -e 's/$/)/' \
  > $3
