"""Replay the supplied downstream sources against the pinned upstream project.
No existing .olean is accepted as evidence of a downstream replay.
Run from the cloned upstream eth directory after installing dependencies.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

project = Path.cwd()
manifest = json.loads((project/'downstream_sources.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
sources = {i['module']: i for i in manifest['sources']}
ordered, active, done = [], set(), set()

def visit(module):
    if module in done:
        return
    if module in active:
        raise RuntimeError('Cyclic imports: '+module)
    active.add(module)
    item = sources[module]
    path = project/item['path']
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != item['sha256']:
        raise RuntimeError('Source hash mismatch: '+str(path))
    for dep in re.findall(r'^import (Downstream\.\S+)', raw.decode(), re.M):
        visit(dep)
    active.remove(module)
    done.add(module)
    ordered.append(item)

for module in sorted(sources):
    visit(module)
if '--check-sources' in sys.argv[1:]:
    print('Source-integrity check only: '+str(len(ordered))+' modules, all hashes and downstream imports valid. No Lean replay performed.')
    raise SystemExit(0)
logdir = project/'downstream_replay_logs'
logdir.mkdir(exist_ok=True)
records = []
env = dict(os.environ, LEAN_NUM_THREADS='1')
for item in ordered:
    path = project/item['path']
    obj = project/'.lake/build/lib/lean'/Path(*item['module'].split('.')).with_suffix('.olean')
    obj.parent.mkdir(parents=True, exist_ok=True)
    before = hashlib.sha256(path.read_bytes()).hexdigest()
    command = ['lake', 'env', 'lean', '-o', str(obj), str(path)]
    print('Checking '+item['module'], flush=True)
    run = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, env=env)
    output = run.stdout
    log = logdir/(item['module']+'.log')
    log.write_text(output)
    after = hashlib.sha256(path.read_bytes()).hexdigest()
    if run.returncode or before != after or re.search(r'\bsorryAx\b|declaration uses .sorry.|error:', output):
        print(output)
        raise SystemExit('FAILED: '+item['module'])
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    if not reports:
        raise SystemExit('No dependency reports: '+item['module'])
    for name, deps in reports:
        if not set(filter(None,(s.strip() for s in deps.split(',')))) <= allowed:
            raise SystemExit('Unexpected axioms: '+name)
    records.append(dict(module=item['module'],source_sha256=after,
                        object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),
                        log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                        reports=reports,exit_code=run.returncode))
(logdir/'results.json').write_text(json.dumps(records,indent=2)+'\n')
print('Verified '+str(len(records))+' downstream modules; see downstream_replay_logs/results.json')
