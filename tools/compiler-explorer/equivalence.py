"""Export measured binary problems as two real ELF endpoints, never C/Core fixtures."""
import importlib.util
import json
from pathlib import Path
import re
import sqlite3

_spec = importlib.util.spec_from_file_location('binary_corpus', Path(__file__).with_name('corpus.py'))
c = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(c)
MANIFEST = 'corpus/sqlite/equivalence/build-queries/manifest.json'


def validate_pair(pair, left, right):
    """Reject incompatible observed queries; this does not prove machine semantics."""
    key = 'version_number' if pair['function_symbol'] == 'sqlite3_libversion_number' else 'threadsafe_setting'
    if pair['function_symbol'] not in ['sqlite3_libversion_number', 'sqlite3_threadsafe']:
        raise ValueError('unsupported binary query')
    if left[key] != right[key] or pair['value'] != left[key]:
        raise ValueError('incompatible query results; not selected for equivalence')
    for role, endpoint in [('left', left), ('right', right)]:
        frame = 8 if endpoint['build']['optimization'] == 'O0' else 0
        if pair[role + '_frame'] != frame:
            raise ValueError('unexpected private stack frame')


def export(project, output, root=c.ROOT):
    registry_data = c.public_file(root, c.REGISTRY).read_bytes()
    statements = [s for s in json.loads(registry_data)['statements'] if s.get('viewer_kind') == 'binary_equivalence']
    output.mkdir(parents=True, exist_ok=True)
    (output / 'blobs').mkdir(exist_ok=True)
    if not statements:
        (output / 'index.json').write_text('[]\n')
        return []
    data = c.public_file(root, MANIFEST).read_bytes()
    manifest = json.loads(data)
    if manifest['schema'] != 'silmaril.binary-equivalence.v1':
        raise ValueError('unsupported binary manifest')
    pairs = {p['declaration']: p for p in manifest['pairs']}
    if set(pairs) != {s['declaration'] for s in statements}:
        raise ValueError('binary registry/manifest mismatch')
    endpoints = {e['id']: e for e in manifest['endpoints']}
    listing = []
    with sqlite3.connect(project.resolve().as_uri() + '?mode=ro', uri=True) as db:
        db.row_factory = sqlite3.Row
        revision = db.execute("SELECT value FROM corpus_meta WHERE key='revision'").fetchone()[0]
        if not re.fullmatch('[0-9a-f]{40}', revision):
            raise ValueError('missing immutable public revision')
        for s in statements:
            if s['kind'] != 'functional_equivalence' or s['status'] != 'stated-unproved':
                raise ValueError('unexpected binary problem status')
            pins = {**s['artifact_sha256'], **s['module_sha256']}
            for name, digest in pins.items():
                if c.sha(c.public_file(root, name).read_bytes()) != digest:
                    raise ValueError('stale binary evidence: ' + name)
            if pins.get(MANIFEST) != c.sha(data):
                raise ValueError('unpinned binary manifest')
            pair = pairs[s['declaration']]
            validate_pair(pair, endpoints[pair['left']], endpoints[pair['right']])
            artifacts = []
            for role in ['left', 'right']:
                e = endpoints[pair[role]]
                for evidence in [e['source'], e['receipt'], e['build']]:
                    raw = c.public_file(root, evidence['path']).read_bytes()
                    if pins.get(evidence['path']) != c.sha(raw) or evidence['sha256'] != c.sha(raw):
                        raise ValueError('stale binary build/source receipt')
                actual_receipt = json.loads(c.public_file(root, e['receipt']['path']).read_bytes())
                actual_build = json.loads(c.public_file(root, e['build']['path']).read_bytes())
                if any(e['build'][key] != actual_build[key] for key in ['configuration', 'version', 'optimization', 'image_id', 'source_inputs']):
                    raise ValueError('binary build fields mismatch')
                if e['build']['cflags'] != actual_receipt['cflags'] or e['source']['path'] not in {x['path'] for x in actual_build['included_source_files']}:
                    raise ValueError('binary build/source correspondence mismatch')
                setting = re.search(r'-DSQLITE_THREADSAFE=(\d)', actual_receipt['cflags'])
                if not setting or int(setting[1]) != e['threadsafe_setting']:
                    raise ValueError('binary THREADSAFE option mismatch')
                raw_source = c.public_file(root, e['source']['path']).read_bytes()
                version = re.search(rb'#define SQLITE_VERSION_NUMBER\s+(\d+)', raw_source)
                if not version or int(version[1]) != e['version_number']:
                    raise ValueError('binary source version mismatch')
                span = e['source']['definitions'][pair['function_symbol']]
                excerpt = raw_source[span['offset']:span['offset']+span['length']]
                if c.sha(excerpt) != span['sha256'] or excerpt.decode() != span['text']:
                    raise ValueError('binary source definition span mismatch')
                row = db.execute('SELECT id,sha256 FROM corpus_artifacts WHERE path=?', (e['path'],)).fetchone()
                if row is None or row['sha256'] != pins.get(e['path']) or row['sha256'] != e['sha256']:
                    raise ValueError('binary catalog artifact mismatch')
                actual = c.elf_function(c.public_file(root, e['path']).read_bytes(), pair['function_symbol'], e['functions'][pair['function_symbol']]['address'])
                if any(actual[k] != e['functions'][pair['function_symbol']][k] for k in actual):
                    raise ValueError('binary function identity mismatch')
                if not db.execute('SELECT count(*) FROM corpus_functions WHERE artifact=? AND symbol=? AND address=? AND size=?',
                        (row['id'], pair['function_symbol'], actual['address'], actual['size'])).fetchone()[0]:
                    raise ValueError('binary catalog function mismatch')
                artifacts.append(dict(role=role, id=row['id'], path=e['path'], sha256=e['sha256'], frame=pair[role+'_frame'], build=e['build'], receipt=e['receipt'], source=e['source'], **actual))
            run = json.loads(c.public_file(root, s['run_receipt']).read_bytes())
            if run['exit_code'] != 0 or s['root'] not in run['command']:
                raise ValueError('binary measured check mismatch')
            modules = []
            for name in [manifest['definition'], s['root'].replace('.', '/') + '.lean', 'Silmaril/Project/Shapes/SysV/Defs.lean', 'Silmaril/Project/Shapes/X86/Defs.lean']:
                raw = c.public_file(root, name).read_bytes()
                if pins.get(name) != c.sha(raw) or len(raw) > c.MAX_TEXT:
                    raise ValueError('unpinned or excessive binary context')
                digest = c.sha(raw)
                (output / 'blobs' / (digest + '.txt')).write_bytes(raw)
                modules.append(dict(path=name,sha256=digest,size=len(raw),static_path='api/equivalences/blobs/'+digest+'.txt'))
            payload = dict(schema='silmaril.binary-view.v1', declaration=s['declaration'], function_symbol=pair['function_symbol'], root=s['root'],
                status='UNPROVED', kind='functional_equivalence', revision=revision, artifacts=artifacts, modules=modules, pair=pair,
                excluded=manifest['excluded'], limits=manifest['limits'], run_receipt=s['run_receipt'], proof_evidence=None, exporter_run=None,
                interactive_compilation=False, source_refinement_assumed=False, manifest=dict(path=MANIFEST,sha256=c.sha(data)),
                registry=dict(path=c.REGISTRY,sha256=c.sha(registry_data)))
            key=c.sha(s['declaration'].encode())
            (output/(key+'.json')).write_text(json.dumps(payload,indent=2)+'\n')
            listing.append(dict(declaration=s['declaration'],function_symbol=pair['function_symbol'],status='UNPROVED',static_path='api/equivalences/'+key+'.json'))
    (output/'index.json').write_text(json.dumps(listing,indent=2)+'\n')
    return listing
