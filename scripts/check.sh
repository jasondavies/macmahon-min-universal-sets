#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
python3 scripts/palomar/check-lean-sources.py
ruby scripts/palomar/validate-formalization.rb
lake build
check_dir=$(mktemp -d)
trap 'rm -rf "$check_dir"' EXIT
lake env lean validation/Axioms.lean > "$check_dir/axioms.txt"
diff -u validation/axioms.txt "$check_dir/axioms.txt"
python3 scripts/check-package.py
