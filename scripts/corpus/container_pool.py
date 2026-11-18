"""Two isolated, persistent corpus workers; no per-profile container creation.

Only immutable recipes/cache and each worker's own output directory are mounted.
The root filesystem is read-only. All writable container state is reset between
profiles. This is workspace independence, not fresh-container independence.
"""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import uuid


RESET = ['bash', '-eu', '-c',
         'find /build /tmp /root /dev/shm -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +; '
         'test -z "$(find /build /tmp /root /dev/shm -mindepth 1 -print -quit)"']
ENV = {'PATH': '/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
       'HOME': '/root', 'LC_ALL': 'C', 'TZ': 'UTC', 'SOURCE_DATE_EPOCH': '1762128000',
       'JOBS': '3'}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


class ContainerPool:
    def __init__(self, image, recipes, cache, directory):
        if not image.startswith('sha256:') or len(image) != 71:
            raise ValueError('pool requires an immutable Docker image ID')
        self.image, self.recipes, self.cache = image, recipes, cache
        self.directory = directory
        self.directory.mkdir(parents=True, exist_ok=False)
        self.containers = []
        self.profiles = 0
        self.record = {'pool_id': str(uuid.uuid4()), 'image_id': image,
                       'lifecycle': 'two independently initialized persistent containers; reused across profiles',
                       'isolation': 'read-only root; private /build, /tmp, /root tmpfs; separate writable output mounts',
                       'reset': RESET, 'environment': ENV,
                       'resources': {'containers': 2, 'cpu_per_container': 3,
                                     'memory_bytes_per_container': 12 * 1024**3,
                                     'execution': 'serial builds, strips and tests; no third container'},
                       'started_utc': self.now(), 'workers': [], 'profiles': []}

    @staticmethod
    def now():
        return datetime.datetime.now(datetime.timezone.utc).isoformat()

    def save(self):
        (self.directory / 'lifecycle.json').write_text(json.dumps(self.record, indent=2) + '\n')

    def output(self, slot):
        return self.directory / str(slot)

    def __enter__(self):
        try:
            for slot in range(2):
                self.output(slot).mkdir()
                command = ['docker', 'run', '--network', 'host', '--pull=never', '--detach',
                           '--read-only', '--cpus', '3', '--memory', '12g', '--memory-swap', '12g',
                           '--pids-limit', '256', '--workdir', '/',
                           '--tmpfs', '/build:rw,exec,size=8g', '--tmpfs', '/tmp:rw,exec,size=1g',
                           '--tmpfs', '/root:rw,size=64m',
                           '-v', f'{self.recipes / "corpus"}:/corpus:ro',
                           '-v', f'{self.recipes / "scripts"}:/scripts:ro',
                           '-v', f'{self.cache}:/cache:ro', '-v', f'{self.output(slot)}:/out',
                           self.image, 'sleep', 'infinity']
                container = subprocess.check_output(command, text=True, timeout=45).strip()
                self.containers.append(container)
                worker = {'slot': slot, 'container_id': container, 'creation_command': command,
                          'initialized_utc': self.now()}
                self.record['workers'].append(worker)
                self.save()
                lock = self.exec(slot, ['dpkg-query', '-W', '-f=${binary:Package}\t${Version}\n'], capture=True)
                expected = (self.recipes / 'corpus/toolchain/lock.txt').read_bytes()
                (self.directory / f'packages-{slot}.txt').write_bytes(lock)
                if lock != expected:
                    raise ValueError(f'worker {slot}: whole installed package lock differs')
                worker['package_lock_sha256'] = hashlib.sha256(lock).hexdigest()
                self.save()
            return self
        except BaseException as error:
            self.__exit__(type(error), error, error.__traceback__)
            raise

    def exec(self, slot, command, env=None, capture=False, log=None):
        # env -i also removes Docker image ENV, proxy/credential/cache/compiler overrides.
        clean = {**ENV, **(env or {})}
        if set(clean) - set(ENV) - {'CORPUS_OPT_LEVEL', 'CORPUS_OPENSSL_CONFIG', 'CORPUS_COLLECT'}:
            raise ValueError('unexpected environment override')
        command = ['docker', 'exec', self.containers[slot], 'env', '-i',
                   *(f'{k}={v}' for k, v in clean.items()), *command]
        if capture:
            return subprocess.check_output(command, timeout=60)
        if log is None:
            subprocess.run(command, check=True, timeout=60)
        else:
            with log.open('wb') as output:
                subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, check=True)

    def prepare(self, identity, recipe_hashes, repository):
        # Recheck every frozen recipe before each profile. Each build recipe verifies
        # its archive hash inside BOTH workers; cache mounts are read-only.
        for name, expected in recipe_hashes.items():
            if sha(self.recipes / name) != expected:
                raise ValueError(f'frozen recipe changed: {name}')
        for slot in range(2):
            self.exec(slot, RESET)
            for path in self.output(slot).iterdir():
                if path.is_dir() and not path.is_symlink():
                    shutil.rmtree(path)
                else:
                    path.unlink()
            (self.output(slot) / 'repository.json').write_text(json.dumps(repository))
        self.profiles += 1
        profile = {'identity': identity, 'sequence': self.profiles, 'started_utc': self.now(),
                   'container_reused': self.profiles > 1,
                   'workspace_reset_verified': True, 'status': 'running'}
        self.record['profiles'].append(profile)
        self.save()
        return {**self.record, 'profiles': [dict(profile)]}

    def complete(self):
        self.record['profiles'][-1].update(status='passed', finished_utc=self.now())
        self.save()

    def __exit__(self, kind, error, traceback):
        if error is not None:
            self.record['failure'] = {'type': type(error).__name__, 'message': str(error), 'utc': self.now()}
        results = []
        for container in self.containers:
            result = subprocess.run(['docker', 'rm', '--force', container], capture_output=True, text=True, timeout=45)
            results.append({'container_id': container, 'exit_code': result.returncode,
                            'stderr': result.stderr})
        self.record.update(stopped_utc=self.now(), removal=results)
        self.save()
