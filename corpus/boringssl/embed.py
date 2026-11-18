"""Supported BoringSSL embedding contract: consume upstream gen/sources.json.

This generates only a Makefile/build plan. Upstream pregenerated code is consumed
verbatim; no Go/Perl generator execution is claimed. Platform guards in upstream
assembly select the actual target just as the upstream CMake ASM source list does.
"""
import hashlib
import json
from pathlib import Path
import shlex
import sys


def generate(root, prefix, flags, configuration):
    if configuration not in ['asm', 'no-asm']:
        raise ValueError('unsupported BoringSSL configuration')
    sources = json.loads((root / 'gen/sources.json').read_text())
    compiler_flags = shlex.split(flags) + ['-fPIC', '-pthread', '-DBORINGSSL_IMPLEMENTATION',
        '-DBORINGSSL_SHARED_LIBRARY', '-Iinclude', '-MMD', '-MP']
    if configuration == 'no-asm':
        compiler_flags.append('-DOPENSSL_NO_ASM')
    plan, groups, rules, depfiles = [], {}, [], []

    def command(args, target, dependencies):
        plan.append({'output': target, 'inputs': dependencies, 'command': args})
        rules.append(f'{target}: {" ".join(dependencies)}\n\tmkdir -p $(dir $@)\n\t{shlex.join(args)}\n')

    for group in ['bcm', 'crypto', 'ssl', 'bssl']:
        groups[group] = []
        paths = sources[group]['srcs'] + (sources[group].get('asm', []) if configuration == 'asm' else [])
        for source in paths:
            if Path(source).suffix not in ['.c', '.cc', '.S'] or not (root / source).is_file():
                raise ValueError(f'unsupported/missing upstream compiler input: {source}')
            target = f'obj/{source}.o'
            groups[group].append(target)
            cc = prefix + ('g++' if source.endswith('.cc') else 'gcc')
            extra = ['-std=c++17', '-fno-exceptions', '-fno-rtti'] if source.endswith('.cc') else []
            command([cc, *compiler_flags, *extra, '-c', source, '-o', target], target, [source])
            depfiles.append(target[:-1] + 'd')

    # The boundary is upstream's BCM target, including its listed assembly. The
    # non-FIPS CMake object-library branch uses these same inputs; no delocation,
    # integrity hash or certification is implied by packaging it with ld -r.
    command([prefix + 'ld', '-r', '-o', 'boringcrypto-bcm.o', *groups['bcm']],
            'boringcrypto-bcm.o', groups['bcm'])
    command([prefix + 'g++', '-shared', '-Wl,-soname,libcrypto.so', '-o', 'libcrypto.so',
             'boringcrypto-bcm.o', *groups['crypto'], '-pthread'],
            'libcrypto.so', ['boringcrypto-bcm.o', *groups['crypto']])
    command([prefix + 'g++', '-shared', '-Wl,-soname,libssl.so', '-Wl,-z,defs', '-o', 'libssl.so',
             *groups['ssl'], '-L.', '-lcrypto', '-pthread'],
            'libssl.so', [*groups['ssl'], 'libcrypto.so'])
    command([prefix + 'g++', '-o', 'bssl', *groups['bssl'], '-L.', '-lssl', '-lcrypto', '-pthread'],
            'bssl', [*groups['bssl'], 'libssl.so', 'libcrypto.so'])
    (root / 'embed.mk').write_text('all: bssl\n\n' + '\n'.join(rules) + '\n-include ' + ' '.join(depfiles) + '\n')
    (root / 'embedding-plan.json').write_text(json.dumps({'configuration': configuration,
        'upstream_source_list_sha256': hashlib.sha256((root / 'gen/sources.json').read_bytes()).hexdigest(),
        'upstream_targets': groups, 'planned_commands': plan, 'generators_invoked': [],
        'generator_status': 'upstream committed pregenerated inputs consumed verbatim',
        'module_configuration': 'NON-FIPS; BORINGSSL_FIPS undefined; no integrity injection',
        'contract': 'upstream INCORPORATING.md Build support; gen/sources.json; CMakeLists.txt non-FIPS fipsmodule object-library branch'},
        indent=2) + '\n')


if __name__ == '__main__':
    generate(Path(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4])
