"""Corpus database integration: real inputs, additive backup, no ELF blob storage."""
import hashlib
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class CorpusDatabase(unittest.TestCase):
    def test_real_inputs_and_preserved_base(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, output = Path(tmp) / 'base.sqlite', Path(tmp) / 'corpus.sqlite'
            db = sqlite3.connect(base)
            db.executescript('CREATE TABLE preserve(value TEXT); INSERT INTO preserve VALUES("unchanged");')
            db.close()
            before = hashlib.sha256(base.read_bytes()).hexdigest()
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--base', str(base), '--output', str(output)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(before, hashlib.sha256(base.read_bytes()).hexdigest())
            db = sqlite3.connect(output)
            self.assertEqual(db.execute('SELECT value FROM preserve').fetchone(), ('unchanged',))
            self.assertGreaterEqual(db.execute('SELECT count(*) FROM corpus_artifacts').fetchone()[0], 54)
            self.assertEqual(db.execute("SELECT count(*) FROM corpus_artifacts WHERE metadata LIKE '%whole-file parse unavailable%'").fetchone()[0], 6)
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_functions').fetchone()[0], 42000)
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_timings').fetchone()[0], 10)
            self.assertTrue(all(row[2].upper() != 'BLOB' for row in db.execute('PRAGMA table_info(corpus_artifacts)')))
            db.close()
            again = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--output', str(output)], capture_output=True)
            self.assertNotEqual(again.returncode, 0)


if __name__ == '__main__':
    unittest.main()
