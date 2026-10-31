#!/usr/bin/env python3
"""Record exact commands, source/binary/data hashes, and completed cube runs."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
command=['./build/cubes',*sys.argv[1:]]
def digest(path): return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
record={'command':command,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_sha256':digest('src/cubes.cpp'),'binary_sha256':digest('build/cubes'),
        'tableau_sha256':digest('results/tableau.txt')}
start=time.monotonic()
run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
record.update(returncode=run.returncode,wall_seconds=time.monotonic()-start,stdout=run.stdout,stderr=run.stderr)
with (ROOT/'results/experiments.jsonl').open('a') as stream: stream.write(json.dumps(record)+'\n')
print(run.stdout,end='');print(run.stderr,end='',file=sys.stderr)
sys.exit(run.returncode)
