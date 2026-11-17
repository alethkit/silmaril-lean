"""Parser regressions: byte accounting, invalid encodings and syscall sites."""
import unittest
import hashlib
import json
from pathlib import Path
from census import disassembly


class DecoderEvidence(unittest.TestCase):
    def test_canonical_report_coverage(self):
        root = Path(__file__).resolve().parents[2]
        expected = set()
        for receipt in (root / 'corpus/elf').glob('*/*/receipt.json'):
            for artifact in json.loads(receipt.read_text())['outputs']:
                rel = Path(artifact['path']).relative_to('corpus/elf')
                report_path = root / 'corpus/census' / rel.parent / (rel.name + '.json')
                expected.add(report_path)
                report = json.loads(report_path.read_text())
                self.assertEqual(report['sha256'], artifact['sha256'])
                with (root / artifact['path']).open('rb') as f:
                    self.assertEqual(report['sha256'], hashlib.file_digest(f, 'sha256').hexdigest())
                for section in report['executable_sections']:
                    self.assertEqual(section['size'], sum(section[k] for k in ['decoded_bytes', 'undecoded_bytes', 'unreported_bytes']))
        self.assertEqual(expected, set((root / 'corpus/census').glob('*/*/*.json')))

    def test_x86(self):
        report = disassembly('''Disassembly of section .text:
  10: 01 c0                 add %eax,%eax
  12: 0f 05                 syscall
  14: 0f                    (bad)
''', 'x86_64')['.text']
        self.assertEqual(report['decoded_bytes'], 4)
        self.assertEqual(report['undecoded_bytes'], 1)
        self.assertEqual(report['mnemonics']['add'], 1)
        self.assertEqual(report['syscall_sites'][0]['address'], 0x12)
        self.assertIsNone(report['syscall_sites'][0]['number'])

    def test_aarch64(self):
        report = disassembly('''Disassembly of section .text:
  100: d4000001             svc #0x0
  104: 00000000             .inst 0x00000000 ; undefined
  108: d50b7b22             dc cvau, x2
Disassembly of section .init:
  110: d65f03c0             ret
''', 'aarch64')
        self.assertEqual(report['.text']['decoded_bytes'], 8)
        self.assertEqual(report['.text']['undecoded_bytes'], 4)
        self.assertEqual(report['.init']['decoded_bytes'], 4)
        self.assertEqual(len(report['.text']['syscall_sites']), 1)


if __name__ == '__main__':
    unittest.main()
