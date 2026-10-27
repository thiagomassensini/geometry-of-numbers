#!/usr/bin/env python3
"""Restore only source-matched, previously checked Lean objects in this worktree."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tarfile

root = Path(__file__).resolve().parent
repo = root.parents[1]
operator = Path('/home/thlinux/carry-self-adjoint-operator')
parser = argparse.ArgumentParser()
parser.add_argument('--verify-only', action='store_true')
args = parser.parse_args()
archive = root / '.cache/input-cache.tar.gz'
expected_archive_sha256 = 'db4433fcf9ff62169ad957d6879a00b17945c85436374eab53c1516e41af586f'

def run(argv, cwd=repo):
    return subprocess.check_output(argv, cwd=cwd, text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(archive) == expected_archive_sha256
with tarfile.open(archive) as tf:
    meta = json.load(tf.extractfile('CACHE-MANIFEST.json'))
    assert meta['commit'] == '24741f75b8f2ebd72ccd53a1e7211d476014afd0'
    assert run(['git', 'merge-base', 'HEAD', meta['commit']]) == meta['commit']
    assert run(['git', 'rev-parse', 'HEAD:GeometryOfNumbers']) == meta['core_tree']
    assert sha(repo/'lean-toolchain') == meta['lean_toolchain_sha256']
    assert sha(repo/'lake-manifest.json') == meta['lake_manifest_sha256']
    native = meta['operator_provenance']
    assert run(['git', 'rev-parse', 'HEAD'], operator) == native['operator_head']
    assert run(['git', 'status', '--porcelain=v1'], operator) == native['operator_status']
    for name, expected in meta['package_states'].items():
        package = operator/'.lake/packages'/name
        assert run(['git', 'rev-parse', 'HEAD'], package) == expected['head'], name
        assert run(['git', 'status', '--porcelain=v1'], package) == expected['status'], name
    for path, digest in native['source_sha256'].items():
        assert sha(operator/path) == digest, path
    for path, digest in native['protected_sha256'].items():
        assert sha(Path(path)) == digest, path
    for path, digest in native['geometry_tfvd_sources_sha256'].items():
        assert sha(repo/path) == digest, path
    assert sha(operator/'.lake/packages/CPFormal/CPFormal/Analytic/CpNativeGpreTowerNorm.lean') == native['native_tower_source_sha256']
    assert len(meta['modules']) == 73
    pending = []
    modules = {}
    for item in meta['modules']:
        src = Path(item['source'])
        obj = Path(item['object'])
        assert src.parts[0] == obj.parts[0] == 'research'
        assert not src.is_absolute() and not obj.is_absolute()
        assert '..' not in src.parts and '..' not in obj.parts
        assert src.suffix == '.lean' and obj.suffix == '.olean'
        assert obj.parent == src.parent/'.cache' and obj.stem == src.stem
        assert sha(repo/src) == item['source_sha256'], str(src)
        tracked = subprocess.check_output(['git', 'show', 'HEAD:'+str(src)], cwd=repo)
        assert hashlib.sha256(tracked).hexdigest() == item['source_sha256']
        info = tf.getmember(str(obj))
        assert info.isfile()
        raw = tf.extractfile(info).read()
        assert hashlib.sha256(raw).hexdigest() == item['olean_sha256']
        target = repo/obj
        assert target.resolve().is_relative_to(repo.resolve()) and not target.is_symlink()
        if args.verify_only or target.exists():
            assert target.is_file() and sha(target) == item['olean_sha256'], str(obj)
        pending.append((target, raw))
        assert src.stem not in modules
        modules[src.stem] = {'source': str(src), 'source_sha256': item['source_sha256'],
                             'olean_sha256': item['olean_sha256']}
    if not args.verify_only:
        for target, raw in pending:
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(raw)
        (root/'evidence').mkdir(exist_ok=True)
        (root/'evidence/upstream.json').write_text(json.dumps({'base': meta['commit'], 'modules': modules}, indent=2)+'\n')
        (root/'evidence/cache-restoration.json').write_text(json.dumps({
            'PASS': True, 'archive_sha256': expected_archive_sha256, 'source_commit': meta['commit'],
            'objects': len(modules), 'actual_source_and_object_hashes_verified': True,
            'core_toolchain_manifest_native_and_package_fingerprints_verified': True,
            'old_objects_reused_not_recompiled_this_run': True,
            'new_modules_require_fresh_build_and_axiom_audit': True}, indent=2)+'\n')
print('PASS: 73 cached Lean objects checked against actual sources, hashes and dependency fingerprints; '+('verified in place.' if args.verify_only else 'restored only into task-owned caches.'))
