"""Release identity and supported upstream embedding-plan checks."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('boringssl_embed', ROOT / 'corpus/boringssl/embed.py')
embed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(embed)


class Profiles(unittest.TestCase):
    def test_distinct_sqlite_upstream_versions_and_exact_sources(self):
        releases = tomllib.loads((ROOT / 'corpus/sqlite/releases.toml').read_text())
        self.assertEqual(len({r['sha256'] for r in releases.values()}), len(releases))
        for version, release in releases.items():
            result = subprocess.check_output(['python3', '-I', 'corpus/sqlite/release.py'],
                cwd=ROOT, env={**os.environ, 'CORPUS_SQLITE_VERSION': version}, text=True).splitlines()
            self.assertEqual(result, [version, release['root'], release['sha256'], release['url']])
        result = subprocess.run(['python3', '-I', 'corpus/sqlite/release.py'], cwd=ROOT,
            env={**os.environ, 'CORPUS_SQLITE_VERSION': '../../other'}, capture_output=True)
        self.assertNotEqual(result.returncode, 0)

    def test_unknown_version_rejected_before_docker(self):
        result = subprocess.run(['python3', 'scripts/corpus/variants.py', '--package', 'sqlite',
            '--version', '9.99.9', '--work', '/unused'], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('pinned release', result.stderr)

    def test_bcm_boundary_is_upstream_target_with_no_generated_asm_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'gen').mkdir()
            sources = {name: {'srcs': [f'{name}.cc'], 'asm': [f'{name}.S']}
                       for name in ['bcm', 'crypto', 'ssl', 'bssl']}
            (root / 'gen/sources.json').write_text(json.dumps(sources))
            for name in sources:
                for suffix in ['.cc', '.S']:
                    (root / (name + suffix)).write_text('upstream input')
            for config in ['asm', 'no-asm']:
                embed.generate(root, 'aarch64-linux-gnu-', '-O2 -g0', config)
                plan = json.loads((root / 'embedding-plan.json').read_text())
                bcm = next(p for p in plan['planned_commands'] if p['output'] == 'boringcrypto-bcm.o')
                self.assertEqual(bcm['inputs'], ['obj/bcm.cc.o'] + (['obj/bcm.S.o'] if config == 'asm' else []))
                self.assertEqual(bcm['command'][:2], ['aarch64-linux-gnu-ld', '-r'])
                self.assertEqual(plan['generators_invoked'], [])
                self.assertTrue(all('BORINGSSL_FIPS' not in arg for p in plan['planned_commands'] for arg in p['command']))
                self.assertEqual(any('-DOPENSSL_NO_ASM' in p['command'] for p in plan['planned_commands']), config == 'no-asm')
            (root / 'bcm.cc').unlink()
            with self.assertRaisesRegex(ValueError, 'missing upstream compiler input'):
                embed.generate(root, '', '-O2', 'asm')


if __name__ == '__main__':
    unittest.main()
