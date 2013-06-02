echo '#!/bin/bash' > $3
curl https://raw.github.com/apenwarr/redo/master/minimal/do >> $3
chmod +x $3
