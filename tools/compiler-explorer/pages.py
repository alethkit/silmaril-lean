#!/usr/bin/env python3
"""Publish the existing read-only compiler viewer using public project evidence.

Only committed manifests and their checked public input paths are ingested. The
project adapter accepts exact row/shape/argument/kernel/axiom matches; no evidence
file is promoted and no exporter result is invented. Output is static JSON/text,
not a database server or compile service. Never pass a private project database.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
_spec = importlib.util.spec_from_file_location("cexplorer_pages", Path(__file__).with_name("cexplorer.py"))
cx = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cx)


def export(project, output):
    output.mkdir(parents=True, exist_ok=True)
    (output / 'api/problems').mkdir(parents=True, exist_ok=True)
    downloads = output / 'api/artifacts'
    downloads.mkdir(parents=True, exist_ok=True)
    index = output.parent / 'compiler-artifacts/index.json'
    catalog = ('../', json.loads(index.read_bytes())['artifacts']) if index.is_file() else None
    with tempfile.TemporaryDirectory(prefix='compiler-pages-') as tmp:
        db = cx.connect(str(Path(tmp) / 'explorer.sqlite'))
        try:
            for manifest in sorted((cx.ROOT / 'examples/compiler-explorer/manifests').glob('*.json')):
                cx.ingest_manifest(db, manifest)
            matched = cx.ingest_project(db, project) if project else 0
            problems = cx.problem_list(db)
            statuses = Counter()
            for problem in problems:
                filename = hashlib.sha256(problem['id'].encode()).hexdigest() + '.json'
                problem['static_path'] = 'api/problems/' + filename
                payload = cx.problem_view(db, problem['id'], catalog)
                statuses.update(o['status'] for o in payload['obligations'])
                (output / problem['static_path']).write_text(json.dumps(payload, ensure_ascii=False) + '\n')
            for row in db.execute('SELECT sha256, content FROM artifacts'):
                (downloads / row['sha256']).write_bytes(row['content'])
            (output / 'api/problems.json').write_text(json.dumps(problems, ensure_ascii=False) + '\n')
        finally:
            db.close()
    (output / 'integration.json').write_text(json.dumps({'compiler_problems': len(problems),
        'obligation_status_counts': dict(statuses), 'project_obligation_rows_read': matched,
        'scope': 'committed fixtures; not whole-corpus source-to-ELF coverage',
        'interactive_compilation': False}, indent=2) + '\n')
    for name in ['index.html', 'app.js', 'view.js', 'style.css']:
        shutil.copyfile(cx.UI / name, output / name)
    index = output / 'index.html'
    index.write_text(index.read_text().replace('</header>', '''<p class="note"><a href="../#/corpus">Corpus catalog</a> · <a href="../#/compiler">Integration status</a>.
This viewer covers committed compiler fixtures, not every corpus function. Missing evidence remains missing; no compile service runs here.</p></header>'''))
    print(json.dumps({'compiler_problems': len(problems), 'project_obligation_rows_read': matched,
                      'output': str(output), 'evidence': 'exact public project row adapter; no invented exporter runs'}))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, help='public project database; omit for a navigation-only snapshot')
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    export(a.project, a.out)


if __name__ == '__main__':
    main()
