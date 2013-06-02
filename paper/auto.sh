# This one better not to be run by redo it self this it might
# break assumptions about one-build/multiple-builds
. ./config.sh
while : ; do
  inotifywait -e delete "${ALLSOURCES[@]}" || :
  redo all
done
