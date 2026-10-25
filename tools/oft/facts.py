"""Load the facts of a tree and derive what follows from them.

The facts are release.yaml, projects/*/project.yaml, projects/*/*/harness.yaml,
the proof directories under proofs/ and the counterexamples under
counterexamples/.  Everything `oft generate` writes is a function of these
(plus theories/Shapes.v and theories/Images.v, whose digests enter each
statement's fingerprint).

`load(root)` never raises on bad data: it records problems in `tree.errors`
so that `oft lint` can report all of them at once.
"""
import hashlib
import os
import re

from . import names, render, schema, shapes, yamlio

PHRASEBOOK = yamlio.load_file(os.path.join(os.path.dirname(os.path.abspath(__file__)), "phrasebook.yaml"))
FINGERPRINT_TAG = "oss-fuzz-theorems/statement/1"


class Tree:
    def __init__(self, root):
        self.root = os.path.abspath(root)
        self.release = None
        self.projects = {}
        self.proofs = {}           # statement id -> ProofDir
        self.proof_libs = []       # "<project>/<harness>" of every proofs/<p>/<h>/lib/
        self.shared_proof_lib = False  # proofs/lib/ exists
        self.counterexamples = {}  # statement id -> CounterexampleDir
        self.errors = []

    def path(self, *parts):
        return os.path.join(self.root, *parts)

    def err(self, where, msg):
        self.errors.append("%s: %s" % (where, msg))

    def available(self):
        return [p for p in self.projects.values() if p.data.get("status") == "available"]

    def harnesses(self):
        for p in sorted(self.projects.values(), key=lambda p: p.name):
            for h in sorted(p.harnesses.values(), key=lambda h: h.name):
                yield h

    def statements(self):
        for h in self.harnesses():
            for s in h.statements.values():
                yield s


class Project:
    def __init__(self, tree, name, data):
        self.tree, self.name, self.data = tree, name, data
        self.harnesses = {}
        notes = tree.path("notes", name + ".md")
        self.notes = read(notes).strip() if os.path.isfile(notes) else None

    @property
    def dir(self):
        return os.path.join("projects", self.name)

    def entries(self):
        return self.data.get("harnesses") or []


class Harness:
    def __init__(self, project, name, data):
        self.project, self.name, self.data = project, name, data
        self.statements = {}

    @property
    def tree(self):
        return self.project.tree

    @property
    def dir(self):
        return os.path.join("projects", self.project.name, self.name)

    def builds(self, published_only=True):
        """[(build, record)] in the fixed order plain, ubsan, asan, asan-ubsan."""
        b = self.data.get("builds") or {}
        return [(k, b[k]) for k in schema.BUILDS
                if k in b and not (published_only and b[k].get("withheld"))]

    def elf_path(self, build):
        rec = self.data["builds"][build]
        return os.path.join("projects", self.project.name, "bin", self.name, rec["file"])

    def distribution_body(self):
        p = self.tree.path(self.dir, "Distribution.v")
        if not os.path.isfile(p):
            return None
        return split_distribution(read(p))[1]


class Statement:
    def __init__(self, harness, name, data):
        self.harness, self.name, self.data = harness, name, data
        self.status = data.get("status")
        self.proof = None
        self.counterexample = None
        self.derived_counterexample = False   # refuted by another statement's counterexample run
        self.fingerprint = None

    @property
    def id(self):
        return names.statement_id(self.harness.project.name, self.harness.name, self.name)

    @property
    def kind(self):
        return self.data.get("kind")

    @property
    def revision(self):
        return self.data.get("revision", 1)

    def rendered(self):
        """True if Statements.v carries this statement's Definition."""
        return self.data.get("status") not in ("withheld", "withdrawn")


class ProofDir:
    def __init__(self, path, data, refutes):
        self.path, self.data, self.refutes = path, data, refutes


class CounterexampleDir:
    def __init__(self, path, data):
        self.path, self.data = path, data


def split_distribution(text):
    """(header, body) of a Distribution.v: the header is its first comment."""
    if not text.startswith("(** "):
        return None, text
    end = text.find("*)")
    if end < 0:
        return None, text
    end += 2
    body = text[end:]
    return text[:end], body[1:] if body.startswith("\n") else body


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _yaml(tree, rel, kind):
    try:
        data = yamlio.load_file(tree.path(rel))
    except (OSError, yamlio.YamlError) as e:
        tree.err(rel, str(e))
        return None
    problems = schema.validate(kind, data)
    for p in problems:
        tree.err(rel, p)
    return None if problems else data


def load(root):
    tree = Tree(root)
    if os.path.isfile(tree.path("release.yaml")):
        tree.release = _yaml(tree, "release.yaml", "release")
    else:
        tree.err("release.yaml", "missing")
    pdir = tree.path("projects")
    for name in sorted(os.listdir(pdir)) if os.path.isdir(pdir) else []:
        if not os.path.isdir(os.path.join(pdir, name)):
            continue
        rel = os.path.join("projects", name, "project.yaml")
        if not os.path.isfile(tree.path(rel)):
            tree.err(os.path.join("projects", name), "a project directory without project.yaml")
            continue
        data = _yaml(tree, rel, "project")
        if data is None:
            continue
        proj = Project(tree, name, data)
        tree.projects[name] = proj
        for h in sorted(os.listdir(os.path.join(pdir, name))):
            hrel = os.path.join("projects", name, h, "harness.yaml")
            if h == "bin" or not os.path.isfile(tree.path(hrel)):
                continue
            hdata = _yaml(tree, hrel, "harness")
            if hdata is None:
                continue
            har = Harness(proj, h, hdata)
            proj.harnesses[h] = har
            for sname, sdata in (hdata.get("statements") or {}).items():
                if isinstance(sdata, dict):
                    har.statements[sname] = Statement(har, sname, sdata)
    _load_contrib(tree)
    _derive(tree)
    return tree


# Directories beside the statement directories of proofs/<p>/<h>/: the harness's proof library and its build record.
PROOF_HARNESS_DIRS = ("lib", "provenance")


def _walk3(tree, top):
    base = tree.path(top)
    if not os.path.isdir(base):
        return
    for p in sorted(os.listdir(base)):
        if top == "proofs" and p == "lib":
            continue  # proofs/lib/: the library shared by every proof
        for h in sorted(os.listdir(os.path.join(base, p))) if os.path.isdir(os.path.join(base, p)) else []:
            hd = os.path.join(base, p, h)
            for s in sorted(os.listdir(hd)) if os.path.isdir(hd) else []:
                if top == "proofs" and s in PROOF_HARNESS_DIRS:
                    continue
                if os.path.isdir(os.path.join(hd, s)):
                    yield p, h, s, os.path.join(top, p, h, s)


def _load_contrib(tree):
    tree.shared_proof_lib = os.path.isdir(tree.path("proofs", "lib"))
    for p, h, s, rel in _walk3(tree, "proofs"):
        y = os.path.join(rel, "proof.yaml")
        if not os.path.isfile(tree.path(y)):
            tree.err(rel, "a proof directory without proof.yaml")
            continue
        data = _yaml(tree, y, "proof")
        if data is None:
            continue
        sid = names.statement_id(p, h, s)
        if ("proves" in data) == ("refutes" in data):
            tree.err(y, "exactly one of proves and refutes")
            continue
        refutes = "refutes" in data
        if data.get("refutes", data.get("proves")) != sid:
            tree.err(y, "names %r but lives under %s" % (data.get("refutes", data.get("proves")), sid))
        main = "Refutation.v" if refutes else "Proof.v"
        if not os.path.isfile(tree.path(rel, main)):
            tree.err(rel, "missing %s" % main)
        tree.proofs[sid] = ProofDir(rel, data, refutes)
    for p, h, s, rel in _walk3(tree, "counterexamples"):
        y = os.path.join(rel, "expect.yaml")
        if not os.path.isfile(tree.path(y)):
            tree.err(rel, "a counterexample directory without expect.yaml")
            continue
        data = _yaml(tree, y, "counterexample")
        if data is None:
            continue
        sid = names.statement_id(p, h, s)
        if data.get("statement") != sid:
            tree.err(y, "names %r but lives under %s" % (data.get("statement"), sid))
        for f in ("input.bin", "control.bin"):
            if not os.path.isfile(tree.path(rel, f)):
                tree.err(rel, "missing " + f)
        tree.counterexamples[sid] = CounterexampleDir(rel, data)
    base = tree.path("proofs")
    for p in sorted(os.listdir(base)) if os.path.isdir(base) else []:
        for h in sorted(os.listdir(os.path.join(base, p))) if p != "lib" and os.path.isdir(os.path.join(base, p)) else []:
            if os.path.isdir(os.path.join(base, p, h, "lib")):
                tree.proof_libs.append("%s/%s" % (p, h))


def _derive(tree):
    """Derived statuses and fingerprints."""
    by_id = {s.id: s for s in tree.statements()}
    for sid, pd in tree.proofs.items():
        st = by_id.get(sid)
        if st is None:
            tree.err(pd.path, "no statement %s in this release" % sid)
            continue
        st.proof = pd
    for sid, cx in tree.counterexamples.items():
        st = by_id.get(sid)
        if st is None:
            tree.err(cx.path, "no statement %s in this release" % sid)
            continue
        st.counterexample = cx
    digests = {}
    for f in ("theories/Shapes.v", "theories/Images.v"):
        digests[f] = sha256_file(tree.path(f)) if os.path.isfile(tree.path(f)) else None
    lps = ((tree.release or {}).get("semantics") or {}).get("version")
    _refute_agreements(tree)
    for st in by_id.values():
        exported = st.data.get("status")
        if st.proof and st.counterexample:
            tree.err(st.id, "has both a proof and a counterexample: the model and the runner disagree")
        if st.proof or (st.counterexample and not st.derived_counterexample):
            if exported in ("withheld", "withdrawn", "model-gap"):
                tree.err(st.id, "a %s statement cannot carry a proof or a counterexample" % exported)
        if st.proof:
            st.status = "refuted" if st.proof.refutes else "proved"
        elif st.counterexample:
            st.status = "counterexample"
        if exported == "withheld":
            continue                # no fingerprint: it would let anyone test a guess at a withheld binary
        try:
            st.fingerprint = fingerprint(st, digests, lps)
        except (shapes.ShapeError, KeyError, TypeError) as e:
            tree.err(st.id, "cannot be stated: %s" % e)


def _refute_agreements(tree):
    """A counterexample to a halts statement in which the build is killed by a
    signal (an abort, a fault, a trap) is an execution that reaches an error,
    with nothing refused.  Every agreement statement of the same harness that
    names that build forbids exactly that (both builds error-free on every
    input it covers), so the same run refutes it: its status is derived as a
    counterexample too, pointing at the same directory."""
    for h in tree.harnesses():
        deaths = [s.counterexample for s in sorted(h.statements.values(), key=lambda s: s.name)
                  if s.counterexample and not s.derived_counterexample
                  and "signal" in s.counterexample.data["observed"]]
        if not deaths:
            continue
        for st in sorted(h.statements.values(), key=lambda s: s.name):
            if st.kind != "agreement" or st.counterexample or st.data.get("status") in ("withheld", "withdrawn",
                                                                                     "model-gap"):
                continue
            for b in st.data["builds"]:
                cx = next((c for c in deaths if c.data["observed"]["build"] == b), None)
                if cx is not None:
                    st.counterexample, st.derived_counterexample = cx, True
                    break


def fingerprint(st, digests, lps):
    """SHA-256 over what fixes the statement's meaning, and nothing else:
    no docstring, no image, .hex or .vo digest."""
    if digests["theories/Shapes.v"] is None or digests["theories/Images.v"] is None:
        raise KeyError("theories/Shapes.v and theories/Images.v")
    params, body = shapes.term(st.data)
    builds = st.harness.data["builds"]
    lines = [FINGERPRINT_TAG, st.id, "Definition %s%s : Prop := %s." % (st.name, params, body)]
    for b in sorted(set(st.data["builds"])):
        lines.append("build %s %s" % (b, builds[b]["sha256"]))
    lines += ["shapes %s" % digests["theories/Shapes.v"], "images %s" % digests["theories/Images.v"],
              "semantics %s" % lps]
    if st.kind == "bound":
        dist = st.harness.distribution_body()
        if dist is None:
            raise KeyError("Distribution.v")
        lines.append("distribution %s" % hashlib.sha256(dist.encode()).hexdigest())
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


# ---------------------------------------------------------------- licences

_SPDX_TOKEN = re.compile(r"\(|\)|[A-Za-z0-9.+-]+")
_GPL_ID = re.compile(r"(A|L)?GPL-[0-9]")


def gpl_binds(expr):
    """True if every way to comply with the SPDX expression takes a GPL-family licence: AND binds when one operand
    does, OR only when every alternative does (a licensee may pick any), and `X WITH exception` binds as X does.  An
    expression this cannot parse binds if it names a GPL at all."""
    toks = _SPDX_TOKEN.findall(expr or "")
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def take():
        nonlocal pos
        if pos >= len(toks):
            raise ValueError("unexpected end")
        pos += 1
        return toks[pos - 1]

    def primary():
        t = take()
        if t == "(":
            v = disjunction()
            if take() != ")":
                raise ValueError("unbalanced")
            return v
        if t in ("AND", "OR", "WITH", ")"):
            raise ValueError("operator where a licence belongs")
        if peek() == "WITH":
            take()
            take()
        return bool(_GPL_ID.match(t))

    def conjunction():
        v = primary()
        while peek() == "AND":
            take()
            w = primary()
            v = v or w
        return v

    def disjunction():
        v = conjunction()
        while peek() == "OR":
            take()
            w = conjunction()
            v = v and w
        return v

    try:
        v = disjunction()
        if pos != len(toks):
            raise ValueError("trailing tokens")
        return v
    except ValueError:
        return bool(_GPL_ID.search(expr or ""))


def image_libraries(h):
    """The archives from the build image that any build of the harness links, by file name."""
    return sorted({u["name"] for _b, r in h.builds(published_only=False) for u in r.get("uninstrumented") or []
                   if u["kind"] == "image-library"})


def copyleft(tree, h):
    """True if the harness's binaries are bound by a GPL-family licence: by their own expression, the harness source's,
    the library's (the harness's view of it or project.yaml's), or a library they link from the build image that
    release.yaml's image_libraries marks copyleft."""
    lib = h.project.data["library"]
    if any(gpl_binds(x) for x in (h.data["licence"], h.data["library"]["licence"], h.data["source"]["licence"],
                                  lib.get("licence", ""))):
        return True
    known = (tree.release or {}).get("image_libraries") or {}
    return any((known.get(n) or {}).get("copyleft") for n in image_libraries(h))


# ---------------------------------------------------------------- sentences

def feature_words(codes):
    return render.join_words(PHRASEBOOK["features"][c] for c in codes)


def _args(project, args):
    a = dict(args or {})
    a["project"] = project
    if "features" in a:
        a["features"] = feature_words(a["features"])
    if "commit" in a:
        a["commit8"] = a["commit"][:8]
    return a


def project_sentence(proj):
    """The reason sentence for a project that is not available."""
    status, reason = proj.data.get("status"), proj.data.get("reason")
    shape = PHRASEBOOK["projects"][status]["reasons"][reason]
    args = _args(proj.name, proj.data.get("reason_args"))
    if status == "no-harness" and "commit8" not in args:
        args["commit8"] = proj.data["oss_fuzz"]["commit"][:8]
    return shape.format_map(args)


def harness_reason(proj, entry):
    shape = PHRASEBOOK["harnesses"][entry["reason"]]
    return shape.format_map(_args(proj.name, entry.get("reason_args")))


def repo_label(url):
    """'https://github.com/madler/zlib' -> 'madler/zlib'."""
    m = re.match(r"https://(?:www\.)?github\.com/([^/]+/[^/.]+)", url)
    if m:
        return m.group(1)
    return re.sub(r"^https://(www\.)?", "", url).rstrip("/")
