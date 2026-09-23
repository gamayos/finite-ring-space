#!/usr/bin/env python3
"""make_pkg.py — a validation package as an installable sdist, served by the site.

    python3 src/make_pkg.py 10-dimensions [--out docs/pkg] [--version 20260923]

writes docs/pkg/frc-10-dimensions-<version>.tar.gz: a PEP 517 source distribution of `src/10-dimensions/` under the import
name `frc_10_dimensions` (the directory's `__init__.py` exports `row`), built by hand so that no build tool is needed here —
pip builds it on installation (setuptools ≥ 61 in pip's isolated build environment). Every `.py` of the directory is
included; notebooks, results and README are not. The version is the date, YYYYMMDD, unless given; the file name is the
project name as the notebooks spell it plus the version (pip splits a find-links file name at the dash after the requested
name, so the dashes of the project name are fine; PEP 625's underscore form was the earlier spelling), earlier versions of the
same package are removed from the directory, and docs/pkg/index.html is rewritten to list every archive there — a pip
"find links" page. A notebook cell then needs only

    !pip install -q frc-10-dimensions --find-links https://www.finitering.space/pkg/
    from frc_10_dimensions import row; row("10:C5")

and pip, given a named requirement, checks the installed set first: a second call in the same session is
"Requirement already satisfied" — no download, no rebuild (a URL archive would be rebuilt on every call).
"""
import argparse, datetime, gzip, html, io, re, sys, tarfile, time
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
    out = out_dir / f"{name}-{version}.tar.gz"; out_dir.mkdir(parents=True, exist_ok=True)
    top = f"{name}-{version}"; stamp = 0                       # a fixed mtime: the archive is a function of its contents and version
    def add(tar, arcname, data):
        info = tarfile.TarInfo(arcname); info.size = len(data); info.mtime = stamp; info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
    buf = io.BytesIO()
    with gzip.GzipFile(fileobj=buf, mode="wb", compresslevel=9, mtime=0) as gz, tarfile.open(fileobj=gz, mode="w") as tar:   # the gzip header's mtime fixed at 0: the archive is a function of its contents and version alone
        add(tar, f"{top}/pyproject.toml", pyproject.encode()); add(tar, f"{top}/PKG-INFO", pkginfo.encode())
        for p in files: add(tar, f"{top}/{mod}/{p.name}", p.read_bytes())
    for old in list(out_dir.glob(f"{name}-*.tar.gz")) + list(out_dir.glob(f"{mod}-*.tar.gz")):   # one version per package in the directory (git keeps the history); the underscore spelling is the earlier form
        if old != out: old.unlink()
    legacy = out_dir / f"{name}.tar.gz"                       # the unversioned name of the first pilot
    if legacy.exists(): legacy.unlink()
    out.write_bytes(buf.getvalue())
    index(out_dir)
    return out, len(files)

def index(out_dir):
    """docs/pkg/index.html: one link per archive, what `pip install <name> --find-links https://www.finitering.space/pkg/` reads."""
    items = sorted(p.name for p in out_dir.glob("*.tar.gz"))
    body = "\n".join(f'<a href="{html.escape(n)}">{html.escape(n)}</a><br>' for n in items)
    (out_dir / "index.html").write_text("<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"><title>FRC validation packages</title></head><body>\n"
                                        "<h1>FRC validation packages</h1>\n<p>The validation package of each paper of the Finite Ring Continuum corpus as a source distribution; "
                                        "<code>pip install frc-&lt;paper&gt; --find-links https://www.finitering.space/pkg/</code> installs one.</p>\n" + body + "\n</body></html>\n", encoding="utf-8")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("pkgdir"); ap.add_argument("--out", default=str(ROOT / "docs" / "pkg"))
    ap.add_argument("--version", default=datetime.date.today().strftime("%Y%m%d"))
    a = ap.parse_args()
    out, n = sdist(a.pkgdir, Path(a.out), a.version)
    print(f"{out.relative_to(ROOT)}: {n} modules, version {a.version}, {out.stat().st_size} bytes")
