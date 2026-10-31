#!/usr/bin/env python3
"""Check the submission surface and reproducibility of generated Lean sources."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import shutil

root = Path(__file__).resolve().parents[1]
config = json.loads((root/'comparator.json').read_text())
challenge = (root/'Challenge.lean').read_text()
assert challenge.count(':= by sorry') + challenge.count('  sorry\n') == len(config['theorem_names'])
for name in config['theorem_names']:
    assert re.search(r'^theorem '+re.escape(name.split('.')[-1])+r'\b', challenge, re.M), name
assert re.findall(r'^public import (.+)$', challenge, re.M) == ['Mathlib']
for p in [root/'MacMahon.lean', root/'Solution.lean', *sorted((root/'MacMahon').rglob('*.lean'))]:
    assert not re.search(r'\b(sorry|admit|native_decide)\b', p.read_text()), p
    assert not re.search(r'^\s*axiom\s', p.read_text(), re.M), p
files = [Path('MacMahon/Data.lean'), Path('MacMahon/Classification.lean'),
         *[p.relative_to(root) for p in sorted((root/'MacMahon/ClassificationCases').glob('*.lean'))]]
with tempfile.TemporaryDirectory(prefix='macmahon-generate-') as td:
    tmp=Path(td)
    shutil.copytree(root/'scripts',tmp/'scripts')
    shutil.copytree(root/'results/cubes',tmp/'results/cubes')
    (tmp/'MacMahon').mkdir()
    for script in ['generate_lean_data.py','generate_lean_classification.py']:
        subprocess.run(['python3',str(tmp/'scripts'/script)],check=True)
    for p in files:
        assert (tmp/p).read_bytes()==(root/p).read_bytes(), f'Generator mismatch: {p}'
print(f'PASS: {len(config["theorem_names"])} independent challenge statements; no proof holes; {len(files)} reproducible generated modules')
