#!/bin/bash
set -u
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR" || exit 1
python3 install_cookie_monster_plus.py "$@"
STATUS=$?
echo
if [ "$STATUS" -eq 0 ]; then
  echo "Finished."
else
  echo "Cookie Monster+ was not installed. Review the error above."
fi
read -r -p "Press Return to close..." _
exit "$STATUS"
