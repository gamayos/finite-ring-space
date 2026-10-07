#!/usr/bin/env python3
"""ci/release.py — the framework's dated releases (ledger migration, task LM33, 7 October 2026; decision Q06).

A release is dated, cut at a paper milestone and pinned by every published paper; never on a timer. Its record is the
manifest releases/<release>.json: the tag and commit of finite-ring-space, the Lean pins, and one entry per posted paper
(its package, the package's git tree, its sdist, whether it is pinned). The site keeps what every pinned release needs:

    python3 -B ci/release.py serve frc-20261004     docs/releases/<release>/: the framework archive <release>.tar.gz
                                                    (lean/ without the web copies, frc/, ci/), the Lean web copies
                                                    (lean/web/**), the pinned papers' sdists (pkg/), all read from the
                                                    tag; and each paper's checks at the tag recorded in the manifest
    python3 -B ci/release.py cut frc-YYYYMMDD [--pin KEY ...]
                                                    at a paper milestone: an annotated tag at HEAD and its manifest,
                                                    the earlier release's papers carried over and KEY pinned anew

The pages (docs/releases/index.html, docs/releases/<release>/index.html) are written by the site build from the
manifests. Gate G15 (ci/gates.py) checks the pins. Needs git and the tag; standard library only.
"""
import datetime, hashlib, io, json, subprocess, sys, tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REL = ROOT / "releases"


def git(*args, binary=False):
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, env={"GIT_OPTIONAL_LOCKS": "0", "PATH": "/usr/bin:/bin:/usr/local/bin"})
    if r.returncode: raise SystemExit(f"git {' '.join(args)}: {r.stderr.decode().strip()}")
    return r.stdout if binary else r.stdout.decode().strip()


def tree_files(tag, prefix):
    out = git("ls-tree", "-r", "--name-only", tag, "--", prefix)
    return [l for l in out.splitlines() if l]


def archive(tag, dest):
    """<release>.tar.gz: the framework at the tag — lean/ without lean/web, frc/, ci/, the licence — under <release>/,
    with the tag's commit time on every member (reproducible from the tag)."""
    when = int(git("log", "-1", "--format=%ct", tag))
    files = [f for f in tree_files(tag, "lean") if not f.startswith("lean/web/")] + tree_files(tag, "frc") + tree_files(tag, "ci") + tree_files(tag, "LICENSE")
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tf:
        for f in sorted(files):
            data = git("show", f"{tag}:{f}", binary=True)
            ti = tarfile.TarInfo(f"{tag}/{f}"); ti.size = len(data); ti.mtime = when; ti.mode = 0o644
            tf.addfile(ti, io.BytesIO(data))
    import gzip
    raw = io.BytesIO()
    with gzip.GzipFile(fileobj=raw, mode="wb", mtime=when) as gz: gz.write(buf.getvalue())
    dest.write_bytes(raw.getvalue())
    return len(files)


def results_at(tag, package):
    """(passed, checks) of a package's results.json at the tag, or None."""
    try: recs = json.loads(git("show", f"{tag}:{package}/results.json"))
    except SystemExit: return None
    return [sum(1 for r in recs if r.get("ok")), len(recs)]


def serve(rel):
    man_path = REL / f"{rel}.json"
    man = json.loads(man_path.read_text(encoding="utf-8"))
    tag = man["tag"]
    if git("rev-parse", f"{tag}^{{commit}}") != man["commit"]: raise SystemExit(f"{tag} does not point to {man['commit']}")
    out = ROOT / "docs" / "releases" / rel
    (out / "pkg").mkdir(parents=True, exist_ok=True)
    n = archive(tag, out / f"{rel}.tar.gz")
    web = [f for f in tree_files(tag, "lean/web") if "/_to_delete/" not in f]
    for f in web:
        d = out / f; d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(git("show", f"{tag}:{f}", binary=True))
    for p in man["papers"]:
        if not p.get("pinned") or p.get("pinned_release", rel) != rel: continue      # a paper pinned to an earlier release is served there
        if p.get("package"):
            got = git("rev-parse", f"{tag}:{p['package']}")
            if got != p.get("package_tree"): raise SystemExit(f"{p['key']}: {p['package']} at {tag} is {got}, the manifest pins {p.get('package_tree')}")
            p["results"] = results_at(tag, p["package"])
        if p.get("sdist"):
            data = git("show", f"{tag}:docs/pkg/{p['sdist']}", binary=True)
            if hashlib.sha256(data).hexdigest() != p["sdist_sha256"]: raise SystemExit(f"{p['key']}: {p['sdist']} at {tag} differs from the manifest")
            (out / "pkg" / p["sdist"]).write_bytes(data)
    man["served"] = {"archive": f"docs/releases/{rel}/{rel}.tar.gz", "archive_sha256": hashlib.sha256((out / f"{rel}.tar.gz").read_bytes()).hexdigest(),
                     "archive_files": n, "web_copies": len(web),
                     "sdists": sorted(p["sdist"] for p in man["papers"] if p.get("pinned") and p.get("sdist") and p.get("pinned_release", rel) == rel)}
    man_path.write_text(json.dumps(man, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    green = sum(1 for p in man["papers"] if p.get("results") and p["results"][0] == p["results"][1])
    print(f"{rel}: {n} framework files in {rel}.tar.gz, {len(web)} web copies, {len(man['served']['sdists'])} sdists; "
          f"{green} of {sum(1 for p in man['papers'] if p.get('results'))} pinned packages green at the tag")


def cut(rel, pins):
    if (REL / f"{rel}.json").exists(): raise SystemExit(f"{rel} exists")
    prev = sorted(REL.glob("frc-*.json"))
    man = json.loads(prev[-1].read_text(encoding="utf-8")) if prev else {"papers": []}
    head = git("rev-parse", "HEAD")
    git("-c", "user.name=Yosef Akhtman", "-c", "user.email=ya@gamma.earth", "tag", "-a", rel, "-m", f"{rel}: framework release (Q06)" + (f", pinned by {', '.join(pins)}" if pins else ""), head)
    lean = json.loads((ROOT / "lean" / "lake-manifest.json").read_text(encoding="utf-8"))
    papers, before = [], man.get("release")
    for p in man.get("papers", []):
        p = dict(p, pinned_release=p.get("pinned_release", before))                 # carried over: still pinned to its own release
        if p["key"] in pins and p.get("package"):
            p.pop("results", None)
            p["package_tree"] = git("rev-parse", f"{rel}:{p['package']}"); p["pinned_release"] = rel
            sd = sorted((ROOT / "docs" / "pkg").glob(f"frc-{p['package'].split('/')[-1]}-*.tar.gz"))
            p["sdist"] = sd[-1].name if sd else None
            p["sdist_sha256"] = hashlib.sha256(sd[-1].read_bytes()).hexdigest() if sd else None
        papers.append(p)
    new = {"release": rel, "date": datetime.date.today().isoformat(), "kind": "framework release at a paper milestone (Q06)", "repository": "finite-ring-space",
           "tag": rel, "commit": head, "pushed": False,
           "lean": {"toolchain": (ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
                    "mathlib": next(p["rev"] for p in lean["packages"] if p["name"] == "mathlib")},
           "papers": papers}
    (REL / f"{rel}.json").write_text(json.dumps(new, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{rel}: tagged {head[:8]}; {len(pins)} paper(s) pinned anew; run `ci/release.py serve {rel}` and the site build")


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) >= 2 and a[0] == "serve": serve(a[1])
    elif len(a) >= 2 and a[0] == "cut": cut(a[1], [x for x in a[2:] if x != "--pin"])
    else: raise SystemExit(__doc__)
