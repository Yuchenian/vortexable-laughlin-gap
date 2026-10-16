"""Fetch pinned upstream files; verify SHA-256 before optional execution."""
import argparse
from datetime import datetime, timezone
import hashlib
from pathlib import Path
import subprocess
import sys
import urllib.request

BASE = "https://arxiv.org/src/2610.12700v1/anc/"
FILES = {
    "certificate.json": "b9a94d46c8a90e0206d98b700712686d3f2bc2725efcadab3e6513759abbba81",
    "verify.py": "ded1fd1769185bae6df52c95f144832c71c7cfe13d9c36de5556b0f3ec848a45",
}
ROOT = Path(__file__).resolve().parent.parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Run the hash-checked upstream verifier.")
    args = parser.parse_args()
    dest = ROOT / "third_party" / "gao_2610.12700v1"
    dest.mkdir(parents=True, exist_ok=True)
    for name, expected in FILES.items():
        path = dest / name
        if path.exists():
            data = path.read_bytes()
        else:
            req = urllib.request.Request(BASE + name, headers={"User-Agent": "vortexable-laughlin-gap-reproduction"})
            with urllib.request.urlopen(req, timeout=60) as response:
                data = response.read()
        actual = hashlib.sha256(data).hexdigest()
        if actual != expected:
            raise RuntimeError(f"SHA-256 mismatch for {name}; expected {expected}, got {actual}.")
        if not path.exists():
            path.write_bytes(data)
        print(f"SHA-256 OK: {name} {actual}", flush=True)
    if args.verify:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        out = ROOT / "results" / ("rerun_reference_" + stamp)
        out.mkdir(parents=True)
        logfile = out / "gao_reference_certificate.log"
        with logfile.open("w", encoding="utf-8") as log:
            result = subprocess.run([sys.executable, "-u", "verify.py", "certificate.json"],
                                    cwd=dest, stdout=log, stderr=subprocess.STDOUT)
        print(f"Reference verifier exit={result.returncode}; log={logfile.relative_to(ROOT)}")
        if result.returncode:
            raise SystemExit(result.returncode)

if __name__ == "__main__":
    main()
