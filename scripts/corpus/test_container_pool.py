"""Failure, isolation and lifetime regressions without requiring a Docker daemon."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from container_pool import ContainerPool, ENV, RESET, sha


class PoolContract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.recipes = self.root / 'recipes'
        lock = self.recipes / 'corpus/toolchain/lock.txt'
        lock.parent.mkdir(parents=True)
        lock.write_bytes(b'pkg\t1\n')
        self.hashes = {'corpus/toolchain/lock.txt': sha(lock)}
        self.pool = ContainerPool('sha256:' + 'a' * 64, self.recipes,
                                  self.root / 'cache', self.root / 'pool')

    def outputs(self, command, **kwargs):
        if command[:2] == ['docker', 'run']:
            return f'worker-{len(self.pool.containers)}\n'
        if 'dpkg-query' in command:
            return b'pkg\t1\n'
        self.fail(f'unexpected captured command {command}')

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_fixed_two_workers_reset_and_sanitized_environment(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.pool as pool:
            first = pool.prepare('one', self.hashes, {})
            for slot in range(2):
                (pool.output(slot) / '.stale').write_text('old config')
                (pool.output(slot) / 'generated').mkdir()
                (pool.output(slot) / 'generated/result').write_text('old output')
            second = pool.prepare('two', self.hashes, {})
            self.assertFalse(first['profiles'][0]['container_reused'])
            self.assertTrue(second['profiles'][0]['container_reused'])
            for slot in range(2):
                self.assertEqual([p.name for p in pool.output(slot).iterdir()], ['repository.json'])
            with self.assertRaisesRegex(ValueError, 'environment'):
                pool.exec(0, ['true'], env={'CC': 'ccache gcc'})
        launches = [c.args[0] for c in output.call_args_list if c.args[0][1] == 'run']
        self.assertEqual(len(launches), 2)
        for slot, command in enumerate(launches):
            for token in ['--read-only', '--network', 'host', '--cpus', '3', '--memory', '12g']:
                self.assertIn(token, command)
            self.assertIn(f'{self.pool.output(slot)}:/out', command)
            self.assertNotIn(f'{self.pool.output(1-slot)}:/out', command)
        executions = [c.args[0] for c in run.call_args_list if c.args[0][1] == 'exec']
        self.assertEqual(len(executions), 4)
        for command in executions:
            self.assertEqual(command[3:5], ['env', '-i'])
            self.assertIn('JOBS=3', command)
            self.assertEqual(command[-len(RESET):], RESET)
        removals = [c.args[0] for c in run.call_args_list if c.args[0][1] == 'rm']
        self.assertEqual(len(removals), 2)

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_lock_mismatch_fails_and_removes_initialized_worker(self, output, run):
        output.side_effect = ['worker-0\n', b'pkg\twrong\n']
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaisesRegex(ValueError, 'whole installed package lock differs'):
            with self.pool:
                self.fail('must not enter a mismatched image')
        self.assertEqual(run.call_args.args[0], ['docker', 'rm', '--force', 'worker-0'])
        self.assertIn('failure', (self.pool.directory / 'lifecycle.json').read_text())

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_second_initialization_failure_has_no_retry(self, output, run):
        output.side_effect = ['worker-0\n', b'pkg\t1\n',
                              subprocess.CalledProcessError(125, ['docker', 'run'])]
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaises(subprocess.CalledProcessError):
            with self.pool:
                self.fail('must not continue with one worker')
        self.assertEqual(output.call_count, 3)
        self.assertEqual(run.call_args.args[0], ['docker', 'rm', '--force', 'worker-0'])

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_changed_frozen_recipe_stops_before_reset(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.pool:
            (self.recipes / 'corpus/toolchain/lock.txt').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'frozen recipe changed'):
                self.pool.prepare('bad', self.hashes, {})
        self.assertFalse(any(c.args[0][1] == 'exec' for c in run.call_args_list))


if __name__ == '__main__':
    unittest.main()
