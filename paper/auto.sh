# This one better not to be run by redo it self this it might
# break assumptions about one-build/multiple-builds
set -e
. ./config.sh
redo all
while : ; do
  inotifywait -e delete "${ALLSOURCES[@]}" || :
  . ./config.sh
  redo all || :
done
