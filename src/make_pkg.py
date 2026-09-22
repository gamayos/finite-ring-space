#!/usr/bin/env python3
"""make_pkg.py — a validation package as an installable sdist, served by the site.

    python3 src/make_pkg.py 10-dimensions [--out docs/pkg] [--version 2026.9.22]

writes docs/pkg/frc-10-dimensions.tar.gz: a PEP 517 source distribution of `src/10-dimensions/` under the import name
`frc_10_dimensions` (the directory's `__init__.py` exports `row`), built by hand so that no build tool is needed here —
pip builds it on installation (setuptools ≥ 61 in pip's isolated build environment). Every `.py` of the directory is
included; notebooks, results and README are not. The version is the date unless given; pip treats a changed version as
a new package, an unchanged one as already installed. A notebook cell then needs only

    !pip install -q https://www.finitering.space/pkg/frc-10-dimensions.tar.gz
    from frc_10_dimensions import row; row("10:C5")
"""
import argparse, datetime, io, sys, tarfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent          # the repository

def sdist(pkgdir, out_dir, version):
    d = ROOT / "src" / pkgdir
    name = "frc-" + pkgdir; mod = "frc_" + pkgdir.replace("-", "_")
    if not (d / "__init__.py").exists(): sys.exit(f"{d}/__init__.py missing: the package needs its import surface")
    pyproject = (f'[build-system]\nrequires = ["setuptools>=61"]\nbuild-backend = "setuptools.build_meta"\n\n'
                 f'[project]\nname = "{name}"\nversion = "{version}"\ndescription = "The validation package of the FRC paper {pkgdir}: one check per ledger row, exact arithmetic"\n'
                 f'requires-python = ">=3.9"\nlicense = {{text = "MIT"}}\n\n[tool.setuptools]\npackages = ["{mod}"]\n')
    pkginfo = f"Metadata-Version: 2.1\nName: {name}\nVersion: {version}\nSummary: The validation package of the FRC paper {pkgdir}\n"
    files = sorted(p for p in d.glob("*.py"))
    out = out_dir / f"{name}.tar.gz"; out_dir.mkdir(parents=True, exist_ok=True)
    top = f"{name}-{version}"; stamp = 0                       # a fixed mtime: the archive is a function of its contents and version
    def add(tar, arcname, data):
        info = tarfile.TarInfo(arcname); info.size = len(data); info.mtime = stamp; info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=9) as tar:   # mtime of the gzip header left at 0 by not passing a name
        add(tar, f"{top}/pyproject.toml", pyproject.encode()); add(tar, f"{top}/PKG-INFO", pkginfo.encode())
        for p in files: add(tar, f"{top}/{mod}/{p.name}", p.read_bytes())
    out.write_bytes(buf.getvalue())
    return out, len(files)

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("pkgdir"); ap.add_argument("--out", default=str(ROOT / "docs" / "pkg"))
    ap.add_argument("--version", default=datetime.date.today().strftime("%Y.%-m.%-d"))
    a = ap.parse_args()
    out, n = sdist(a.pkgdir, Path(a.out), a.version)
    print(f"{out.relative_to(ROOT)}: {n} modules, version {a.version}, {out.stat().st_size} bytes")
