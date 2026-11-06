"""Fetch pinned dependencies through official codeload; never execute remote scripts."""
from pathlib import Path
import concurrent.futures, hashlib, json, tarfile, io, urllib.request
root = Path(__file__).resolve().parents[1]
dest = root / 'vendor/dependencies'
mathlib_pin = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
dest.mkdir(parents=True, exist_ok=True)
if not (dest/'mathlib/lake-manifest.json').exists():
    raw = urllib.request.urlopen(
        f'https://codeload.github.com/leanprover-community/mathlib4/tar.gz/{mathlib_pin}',
        timeout=120).read()
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as tf:
        for m in tf.getmembers():
            parts = Path(m.name).parts[1:]
            if not parts: continue
            m.name = str(Path('mathlib', *parts))
            tf.extract(m, dest, filter='data')
manifest = json.loads((dest / 'mathlib/lake-manifest.json').read_text())
assert (dest/'mathlib/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'

def fetch(p):
    name, rev = p['name'], p['rev']
    repo = p['url'].removesuffix('.git').split('github.com/')[1]
    url = f'https://codeload.github.com/{repo}/tar.gz/{rev}'
    out = dest / name
    raw = urllib.request.urlopen(url, timeout=120).read()
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as tf:
        prefix = tf.getmembers()[0].name.split('/')[0]
        for m in tf.getmembers():
            parts = Path(m.name).parts[1:]
            if not parts: continue
            m.name = str(Path(name, *parts))
            tf.extract(m, dest, filter='data')
    print(name, rev, len(raw), flush=True)
    return {'name':name, 'revision':rev, 'url':url,
            'archive_sha256':hashlib.sha256(raw).hexdigest()}

with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    lock = list(pool.map(fetch, manifest['packages']))
lock_path = root/'vendor/dependency-lock.json'
if lock_path.exists():
    assert json.loads(lock_path.read_text()) == lock, 'Pinned archive digest mismatch'
else:
    lock_path.write_text(json.dumps(lock,indent=2)+'\n')
# Deliberately do not regenerate lakefile.toml: it also declares the audited OAI library.
