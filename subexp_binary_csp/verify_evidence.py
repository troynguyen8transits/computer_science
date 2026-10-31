"""Validate release files and retained compiler output; does not run Lean."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit('FAILED: ' + message)


release = json.loads((root / 'release_manifest.json').read_text())
actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()
          and p.name != 'release_manifest.json'}
expected = {item['path'] for item in release['files']}
require(actual == expected, 'release file list differs from manifest')
for item in release['files']:
    require(digest(root / item['path']) == item['sha256'], item['path'])

manuscript = json.loads((root / 'manuscript_manifest.json').read_text())
for name, expected_hash in manuscript['files'].items():
    require(digest(root / name) == expected_hash, 'manuscript: ' + name)

sources = json.loads((root / 'lean/downstream_sources.json').read_text())
checks = json.loads((root / 'evidence/downstream_checks.json').read_text())
require(len(checks['components']) == len(sources['sources']) == 82,
        'expected 82 downstream modules')
source_index = {item['path']: item for item in sources['sources']}
require(len(source_index) == 82, 'duplicate source records')
require({item['source'] for item in checks['components']} == set(source_index),
        'receipt/source coverage differs')
reports_total = 0
for item in checks['components']:
    path = item['source']
    require(digest(root / 'lean' / path) == item['source_sha256']
            == source_index[path]['sha256'], 'source: ' + path)
    log = root / 'evidence' / item['log']
    require(digest(log) == item['log_sha256'], 'log: ' + path)
    output = log.read_text()
    require(not re.search(r'\bsorryAx\b|declaration uses .sorry.|error:', output),
            'failure/admission in log: ' + path)
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    require(bool(reports), 'missing axiom reports: ' + path)
    for name, dependencies in reports:
        axioms = {s.strip() for s in dependencies.split(',') if s.strip()}
        require(axioms <= allowed_axioms, 'unexpected axiom: ' + name)
    reports_total += len(reports)

endpoint = json.loads((root / 'evidence/verification.json').read_text())
final = next(item for item in checks['components']
             if item['source'] == 'Downstream/MarxConjecture.lean')
require(final['source_sha256'] == endpoint['final_source_sha256'], 'endpoint source')
require(final['object_sha256'] == endpoint['final_object_sha256'], 'endpoint receipt')
require(final['log_sha256'] == endpoint['final_log_sha256'], 'endpoint log')
require(reports_total == 269, 'expected 269 axiom reports')
fresh_path = root / 'evidence/clean_reproduction/summary.json'
if fresh_path.exists():
    fresh = json.loads(fresh_path.read_text())
    fresh_root = fresh_path.parent
    require(fresh['status'] == 'passed', 'fresh reproduction status')
    require(digest(fresh_root / 'results.json') == fresh['results_sha256'],
            'fresh reproduction results')
    results = json.loads((fresh_root / 'results.json').read_text())
    by_module = {item['module']: item for item in sources['sources']}
    require(len(results) == 82 and {item['module'] for item in results} == set(by_module),
            'fresh reproduction source coverage')
    fresh_reports = 0
    for item in results:
        source = by_module[item['module']]
        require(item['source_sha256'] == source['sha256'] and item['exit_code'] == 0,
                'fresh receipt: ' + item['module'])
        log = fresh_root / 'logs' / (item['module'] + '.log')
        require(digest(log) == item['log_sha256'], 'fresh log: ' + item['module'])
        output = log.read_text()
        require(not re.search(r'\bsorryAx\b|declaration uses .sorry.|error:', output),
                'fresh log failure: ' + item['module'])
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        require([list(report) for report in reports] == item['reports'] and bool(reports),
                'fresh report mismatch: ' + item['module'])
        for name, dependencies in reports:
            require({s.strip() for s in dependencies.split(',') if s.strip()}
                    <= allowed_axioms, 'fresh unexpected axiom: ' + name)
        fresh_reports += len(reports)
    require(fresh_reports == fresh['standard_axiom_reports'] == 269,
            'fresh axiom-report count')
    for stage in fresh['dependency_stages']:
        require(stage['exit_code'] == 0
                and digest(fresh_root / stage['log']) == stage['log_sha256'],
                'fresh stage: ' + stage['stage'])
    print('Fresh-reproduction receipts also pass: 82 modules and 269 standard-axiom reports.')
print(f'Integrity checks passed: {len(release["files"])} release files, '
      f'82 Lean sources, 82 retained logs, {reports_total} standard-axiom reports.')
print('No Lean compiler was run. Omitted objects and upstream sources were not checked.')
