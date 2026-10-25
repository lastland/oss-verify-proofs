"""oft check and oft plan.

`check PROJECT/HARNESS` does what CI does for one harness:

  statements       verify every published ELF's SHA-256; `dune build` the
                   images (elf-snapshot, at build time), Images.v,
                   Statements.v, Characterise.v
  proofs           each proofs/<p>/<h>/<s>/: compile it against the statements
                   (from --base, when given: the base branch's build) and the
                   shared library proofs/lib/ and harness's proof library
                   proofs/<p>/<h>/lib/ if present (each compiled once), then
                   compile a wrapper this tool writes,
                   which ascribes the proof's theorem to the statement and
                   prints its assumptions; every assumption must be in
                   toolchain/allowed-axioms.txt.  The kernel checks every term
                   as it compiles.
  counterexamples  run the binary on input.bin and on control.bin under
                   qemu-user and compare with expect.yaml

--rocqchk adds rocqchk, an independent re-check of the compiled libraries:
over the statements, and once per harness over the wrappers of all its proofs.
Off by default: without its bytecode machine (see _rocqchk) it re-checks every
vm_compute certificate by reduction, which takes hours for one proof.

Each part fails when it examined nothing it was asked to examine.

`plan --changed FILE` maps a change to the harnesses it affects, for CI's
job matrix.
"""
import concurrent.futures
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile

from . import facts, fetch, names, rules

WRAPPER = """(* written by oft check; never supplied by a pull request *)
Require {stmt_mod}.
Require {proof_mod}.
Definition certified : {neg}{stmt_mod}.{stmt}{args} := {proof_mod}.{theorem}.
Set Printing Fully Qualified.
Print Assumptions certified.
"""

# What Print Assumptions prints (Rocq 9.2.0, printing/printer.ml, pr_assumptionset): "Closed under the global
# context", or sections with no blank line between them, each a heading and then one entry per line at column 0 (a long
# entry continues on indented lines).  Under "Axioms:" an axiom is "<name> : <type>"; a construct the kernel took on
# trust is a sentence instead: "<inductive> is assumed to be positive.", "<name> is assumed to be guarded.", "<name>
# relies on an unsafe hierarchy.", "<inductive> relies on definitional UIP.".  "Theory:" lists changes to the logic
# itself (type in type, impredicative Set, rewrite rules).
SECTIONS = ("Transparent constants:", "Section Variables:", "Axioms:", "Opaque constants:", "Theory:")


def wrapper_assumptions(text):
    """The axioms the wrapper's Print Assumptions lists (Set Printing Fully Qualified).  Raises CheckError on every
    entry that is not an axiom and its type (a construct taken on trust, a change to the logic, an axiom whose type did
    not print), and when the output holds neither "Closed under the global context" nor a list of assumptions: nothing
    parsed is not nothing assumed."""
    lines = text.splitlines()
    if "Closed under the global context" in lines:
        return set()
    first = next((i for i, l in enumerate(lines) if l in SECTIONS), None)
    if first is None:
        raise CheckError("Print Assumptions printed neither 'Closed under the global context' nor a list of assumptions")
    axioms, other, section = set(), [], None
    for l in lines[first:]:
        if not l.strip():
            break
        if l[0].isspace():
            continue
        if l in SECTIONS:
            section = l
            continue
        m = re.match(r"(\S+) :( |$)", l)
        if section == "Axioms:" and m:
            axioms.add(m.group(1))
        else:
            other.append(l if section == "Axioms:" else "%s %s" % (section, l))
    if other:
        raise CheckError("the proof relies on what the kernel did not check: %s" % "; ".join(other))
    if not axioms:
        raise CheckError("Print Assumptions printed an empty list of assumptions")
    return axioms


class CheckError(RuntimeError):
    pass


def _run(cmd, cwd, log, timeout=None, env=None):
    """Run cmd, appending its output to log; its return code."""
    with open(log, "a", encoding="utf-8") as f:
        f.write("$ %s\n" % " ".join(cmd))
        f.flush()
        r = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, timeout=timeout, env=env)
    return r.returncode


def allowed_axioms(root, path):
    p = os.path.join(root, path)
    if not os.path.isfile(p):
        raise CheckError("%s is missing" % path)
    out = {l.strip() for l in facts.read(p).splitlines() if l.strip() and not l.startswith("#")}
    if not out:
        raise CheckError("%s is empty" % path)
    return out


UNSAFE = ("relying on type-in-type", "relying on unsafe (co)fixpoints", "whose positivity is assumed")


def rocqchk_axioms(text):
    """(finished, axioms) from rocqchk -o's CONTEXT SUMMARY.  `finished` is
    False unless every module checked and nothing relies on type-in-type,
    unsafe fixpoints or assumed positivity."""
    ok = "Modules were successfully checked" in text and "CONTEXT SUMMARY" in text
    axioms, inside = set(), False
    for line in text.split("CONTEXT SUMMARY", 1)[-1].splitlines():
        s = line.strip()
        if s.startswith("*"):
            inside = s.startswith("* Axioms:")
            if any(u in s for u in UNSAFE) and not s.endswith("<none>"):
                ok = False
            continue
        if inside and s and s != "<none>":
            axioms.add(s)
    return ok, axioms


def _loadpath(build, h=None):
    """-Q mappings for the core and, when given, one harness, from a _build/default tree."""
    q = ["-Q", os.path.join(build, "theories"), "OssFuzzTheorems.Core"]
    return q + ["-Q", os.path.join(build, h.dir), h.data["rocq"]] if h else q


def _rocqchk(root, qargs, modules, allowed, log):
    open(log, "w").close()
    # without its bytecode machine: stock rocqchk 9.2.0 refuses every library that
    # holds a primitive string with it on (tests/check.sh says more)
    rc = _run(["rocqchk", "-o", "-bytecode-compiler", "no"] + qargs + modules, root, log)
    ok, axioms = rocqchk_axioms(facts.read(log))
    if rc != 0 or not ok:
        raise CheckError("rocqchk failed (see %s)" % log)
    if not axioms:
        raise CheckError("rocqchk reported no axioms at all: its summary was not read (see %s)" % log)
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("axioms outside the allowlist: %s" % ", ".join(outside))
    return len(axioms)


def check_statements(root, h, allowed, work, out, rocqchk=False):
    if not h.builds():
        raise CheckError("every build is withheld: nothing to check")
    if fetch.verify_sha(root, [h.project.name], harness=h.name, out=out) != 0:
        raise CheckError("the binaries are missing or do not match (run ./oft fetch %s)" % h.project.name)
    targets = [os.path.join(h.dir, f[:-2] + ".vo") for f in ("Images.v", "Statements.v", "Characterise.v")
               if os.path.isfile(os.path.join(root, h.dir, f))]
    log = os.path.join(work, "dune.log")
    if _run(["dune", "build", "--root", root] + targets, root, log) != 0:
        raise CheckError("dune build failed (see %s)" % log)
    if not rocqchk:
        print("%s: statements compiled" % h.dir, file=out)
        return
    build = os.path.join(root, "_build", "default")
    mods = [h.data["rocq"] + "." + os.path.basename(t)[:-3] for t in targets]
    n = _rocqchk(root, _loadpath(build, h), mods, allowed,
                 os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".rocqchk.log"))
    print("%s: statements compiled; rocqchk: %d axioms, all allowed" % (h.dir, n), file=out)


def compile_lib(root, h, base, work, libs, out):
    """The -Q mappings of proofs/lib/ and h's proof library, when present, in dependency order.  Each is compiled
    once per check run against `base`; `libs` caches its mapping or error by source directory."""
    sharedq = _compile_lib(root, os.path.join("proofs", "lib"), names.SHARED_PROOF_THEORY,
                           _loadpath(base), work, libs, out)
    rel = os.path.join("proofs", h.project.name, h.name, "lib")
    return sharedq + _compile_lib(root, rel, names.rocq_proof(h.project.name, h.name, "lib"),
                                  _loadpath(base, h) + sharedq, work, libs, out)


def _compile_lib(root, rel, lib_mod, loadpath, work, libs, out):
    """Compile every .v below rel from source, using the same per-run cache for shared and harness libraries."""
    if rel in libs:
        if isinstance(libs[rel], (CheckError, OSError)):
            raise libs[rel]
        return libs[rel]
    src = os.path.join(root, rel)
    if not os.path.isdir(src):
        libs[rel] = []
        return []
    try:
        d = tempfile.mkdtemp(prefix="lib-", dir=work)
        files = []
        for dp, _dn, fn in os.walk(src):
            for f in fn:
                if f.endswith(".v"):
                    dst = os.path.join(d, os.path.relpath(os.path.join(dp, f), src))
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copy(os.path.join(dp, f), dst)
                    files.append(dst)
        if not files:
            raise CheckError("%s: holds no .v file" % rel)
        _compile_in_parallel(rel, files, d, loadpath + ["-Q", d, lib_mod])
    except (CheckError, OSError) as e:
        libs[rel] = e
        raise
    libs[rel] = ["-Q", d, lib_mod]
    print("%s: %d files compiled" % (rel, len(files)), file=out)
    return libs[rel]


def _compile_in_parallel(rel, files, d, q):
    """`rocq compile` every file of `files` (all under d) with load path q, each as soon as the files it requires are
    compiled, as many at once as there are CPUs this process may run on (a container's --cpuset-cpus, not the host's
    count).  Each file's output goes to its own log under d/logs/."""
    r = subprocess.run(["rocq", "dep"] + q + sorted(files), capture_output=True, text=True)
    if r.returncode != 0:
        raise CheckError("%s: rocq dep failed: %s" % (rel, r.stderr.strip()))
    deps = {f: set() for f in files}
    for line in r.stdout.splitlines():
        targets, colon, prereqs = line.partition(":")
        vo = next((t for t in targets.split() if t.endswith(".vo")), None) if colon else None
        if vo is None or vo[:-3] + ".v" not in deps:
            continue
        deps[vo[:-3] + ".v"] |= {p[:-3] + ".v" for p in prereqs.split()
                                 if p.endswith(".vo") and p[:-3] + ".v" in deps and p != vo}
    logs = os.path.join(d, "logs")
    os.makedirs(logs)
    log_of = {f: os.path.join(logs, os.path.relpath(f, d).replace(os.sep, "__") + ".log") for f in files}
    pending, done, running, failed = set(files), set(), {}, None
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
    with concurrent.futures.ThreadPoolExecutor(cpus) as ex:
        while pending or running:
            if failed is None:
                for f in sorted(x for x in pending if deps[x] <= done):
                    pending.discard(f)
                    running[ex.submit(_run, ["rocq", "compile"] + q + [f], d, log_of[f])] = f
            if not running:
                raise CheckError("%s: the files %s require each other" % (rel, ", ".join(
                    os.path.relpath(f, d) for f in sorted(pending))))
            finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for fut in finished:
                f = running.pop(fut)
                if fut.result() == 0:
                    done.add(f)
                elif failed is None:
                    failed = f
            if failed is not None and not running:
                raise CheckError("%s: does not compile: %s (see %s)" % (rel, os.path.relpath(failed, d), log_of[failed]))


def check_proof(root, st, pd, base, allowed, work, out, libs, rocqchk=False):
    """Compile one proof directory against the statements in `base` (a _build/default tree), shared and harness proof
    libraries, then the wrapper, and audit the wrapper's assumptions.  With rocqchk, return what rocqchk_proofs needs."""
    h = st.harness
    p, hn, s = st.id.split("/")
    proof_mod = names.rocq_proof(p, hn, s)
    main = "Refutation" if pd.refutes else "Proof"
    libq = compile_lib(root, h, base, work, libs, out)
    d = tempfile.mkdtemp(prefix="proof-", dir=work)
    src = os.path.join(root, pd.path)
    for f in os.listdir(src):
        if f.endswith(".v"):
            shutil.copy(os.path.join(src, f), os.path.join(d, f))
    q = _loadpath(base, h) + libq + ["-Q", d, proof_mod]
    log = os.path.join(d, "compile.log")
    deps = subprocess.run(["rocq", "dep", "-sort"] + libq + ["-Q", d, proof_mod] + sorted(
        os.path.join(d, f) for f in os.listdir(d) if f.endswith(".v")), capture_output=True, text=True)
    if deps.returncode != 0:
        raise CheckError("%s: rocq dep failed: %s" % (pd.path, deps.stderr.strip()))
    # rocq dep -sort lists the whole closure in order, the library's files included: those are compiled already.
    own = [f for f in deps.stdout.split() if os.path.dirname(os.path.abspath(f)) == d]
    if not own:
        raise CheckError("%s: rocq dep listed none of its .v files" % pd.path)
    for f in own:
        if _run(["rocq", "compile"] + q + [f], d, log) != 0:
            raise CheckError("%s: does not compile (see %s)" % (pd.path, log))
    args = ""
    if st.kind == "bound" and not pd.refutes:
        n_, _, d_ = pd.data["bound"].partition("/")
        args = " (%s # %s)" % (n_, d_ or "1")
    theorem = "%s_%s" % (s, "refuted" if pd.refutes else "holds")
    wdir = os.path.join(d, "wrap")
    os.makedirs(wdir)
    with open(os.path.join(wdir, "Wrapper.v"), "w", encoding="utf-8") as f:
        f.write(WRAPPER.format(stmt_mod=h.data["rocq"] + ".Statements", proof_mod=proof_mod + "." + main,
                               neg="~ " if pd.refutes else "", stmt=s, args=args, theorem=theorem))
    wrap = "Wrap." + names.ident(s)
    wq = q + ["-Q", wdir, wrap]
    wlog = os.path.join(d, "wrapper.log")
    if _run(["rocq", "compile"] + wq + [os.path.join(wdir, "Wrapper.v")], d, wlog) != 0:
        raise CheckError("%s: the wrapper does not type-check: the proof is not of this statement (see %s)"
                         % (pd.path, wlog))
    axioms = wrapper_assumptions(facts.read(wlog))
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s: axioms outside the allowlist: %s" % (pd.path, ", ".join(outside)))
    print("%s: %s %s; assumptions: %d axioms, all allowed" % (pd.path, "refutes" if pd.refutes else "proves",
                                                               st.id + args, len(axioms)), file=out)
    if not rocqchk:
        return None
    # rocqchk runs once per harness, over the wrappers of all its proofs (rocqchk_proofs): their closures share the
    # harness's library, which one run checks once.
    return {"base": _loadpath(base, h) + libq, "own": ["-Q", d, proof_mod, "-Q", wdir, wrap],
            "module": wrap + ".Wrapper"}


def rocqchk_proofs(root, h, checked, allowed, work, out):
    """rocqchk over the wrappers of the proofs `checked` (what check_proof returned) of harness h, in one run, and
    every assumption of their closures against the allowlist."""
    q = list(checked[0]["base"])
    for c in checked:
        q += c["own"]
    log = os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".proofs.rocqchk.log")
    n = _rocqchk(root, q, [c["module"] for c in checked], allowed, log)
    print("%s: rocqchk over the wrappers of %d proof(s): %d axioms, all allowed"
          % (os.path.join("proofs", h.project.name, h.name), len(checked), n), file=out)


def _outcome(rc):
    """(exit status as a shell reports it, signal name or None) of a run."""
    if rc < 0:
        return 128 - rc, signal.Signals(-rc).name
    return rc, None


def _no_core_file():
    """Run in the child before qemu starts.  A program that dies of a signal
    still dies of it, but no core file is written: the kernel's core of qemu
    covers the whole guest address space qemu reserved, 17 TB for an
    AddressSanitizer build, and writing it took about 150 s per run."""
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def check_counterexample(root, st, cx, qemu, timeout, work, out):
    h = st.harness
    exp = cx.data
    elf = os.path.join(root, h.elf_path(exp["observed"]["build"]))
    if not os.path.isfile(elf):
        raise CheckError("%s: %s is not fetched" % (cx.path, h.elf_path(exp["observed"]["build"])))
    qemu_path = shutil.which(qemu)
    if qemu_path is None:
        raise CheckError("%s: %s is not installed (the runner image has it)" % (cx.path, qemu))
    results = {}
    for which in ("input", "control"):
        d = tempfile.mkdtemp(prefix=which + "-", dir=work)
        shutil.copy(os.path.join(root, cx.path, which + ".bin"), os.path.join(d, "input.bin"))
        # an empty environment: the binaries read none, and the model gives them none
        r = subprocess.run([qemu_path, elf, "input.bin"], cwd=d, capture_output=True, timeout=timeout, env={},
                           preexec_fn=_no_core_file)
        results[which] = _outcome(r.returncode)
    want = exp["observed"]
    got_exit, got_sig = results["input"]
    if got_exit != want["exit"] or got_sig != want.get("signal"):
        raise CheckError("%s: the input no longer reproduces: exit %s signal %s, expected exit %s signal %s"
                         % (cx.path, got_exit, got_sig, want["exit"], want.get("signal")))
    if results["control"][0] != exp["control"]["exit"]:
        raise CheckError("%s: the control input exited %s, expected %s"
                         % (cx.path, results["control"][0], exp["control"]["exit"]))
    print("%s: reproduces (exit %d%s); control exits %d" % (
        cx.path, got_exit, " " + got_sig if got_sig else "", exp["control"]["exit"]), file=out)


STACK_NEEDED = 1 << 30


def raise_stack_limit():
    """Give every rocq, rocqchk and dune this process starts the largest stack the hard limit allows.  Rocq recurses on
    the system stack, and large proof terms overflow the usual 8 MiB; tests/check.sh runs `ulimit -s unlimited` for
    the same reason.  This changes where the kernel runs, not what it checks."""
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if hard != resource.RLIM_INFINITY and hard < STACK_NEEDED:
        raise CheckError("the stack's hard limit is %d bytes; Rocq needs at least %d (docker run --ulimit stack=-1:-1)"
                         % (hard, STACK_NEEDED))
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))



def run(root, units, base=None, parts="statements,proofs,counterexamples", allowed="toolchain/allowed-axioms.txt",
        qemu="qemu-riscv64", timeout=600, rocqchk=False, out=sys.stdout):
    tree = facts.load(root)
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        return 1
    want = set(parts.split(","))
    work = tempfile.mkdtemp(prefix="oft-check-")
    bad = examined = 0
    libs = {}  # proof library source dir -> its -Q mapping, or the error compiling it
    try:
        allow = allowed_axioms(root, allowed) if want & {"statements", "proofs"} else set()
        if want & {"statements", "proofs"}:
            raise_stack_limit()
    except CheckError as e:
        print("FAIL %s" % e, file=out)
        return 1
    for unit in units:
        p, _, hn = unit.partition("/")
        h = tree.projects.get(p) and tree.projects[p].harnesses.get(hn)
        if not h:
            print("%s: no such harness" % unit, file=out)
            bad += 1
            continue
        steps = []    # (label, step, whether its success alone passes it)
        checked = []  # (label, what check_proof returned) of the proofs whose compile and audit passed
        if "statements" in want:
            steps.append(("statements", lambda h=h: check_statements(root, h, allow, work, out, rocqchk), True))
        for st in h.statements.values():
            if st.proof and "proofs" in want:
                steps.append((st.proof.path, lambda st=st: checked.append((st.proof.path, check_proof(
                    root, st, st.proof, base or os.path.join(root, "_build", "default"), allow, work, out, libs,
                    rocqchk))), not rocqchk))
            if st.counterexample and "counterexamples" in want:
                steps.append((st.counterexample.path, lambda st=st: check_counterexample(
                    root, st, st.counterexample, qemu, timeout, work, out), True))
        if not steps:
            print("%s: nothing to check for parts %s" % (unit, parts), file=out)
            bad += 1
            continue
        for label, step, passes in steps:
            try:
                step()
                examined += 1 if passes else 0
            except (CheckError, subprocess.TimeoutExpired, OSError) as e:
                print("FAIL %s: %s" % (label, e), file=out)
                bad += 1
        if rocqchk and checked:
            # With rocqchk, a proof passes only when the one rocqchk over every compiled wrapper of this harness passes.
            try:
                rocqchk_proofs(root, h, [c for _, c in checked], allow, work, out)
                examined += len(checked)
            except (CheckError, subprocess.TimeoutExpired, OSError) as e:
                for label, _ in checked:
                    print("FAIL %s: %s" % (label, e), file=out)
                bad += len(checked)
    print("oft check: %d step(s) passed, %d failed; work files in %s" % (examined, bad, work), file=out)
    return 1 if bad or not examined else 0


# ------------------------------------------------------------------ segments

def snapshot_segments(elf, tool="elf-snapshot"):
    """The `segments` field of a build: how many .hex chunks elf-snapshot
    writes for each LOAD segment of `elf`.  Measured by running the tool,
    so images/dune lists exactly the files the rule will produce."""
    with tempfile.TemporaryDirectory() as d:
        r = subprocess.run([tool, elf, os.path.join(d, "Plain.v"), "--prefix", "Plain", "--module-name", "M",
                            "--namespace", "X"], capture_output=True, text=True)
        if r.returncode != 0:
            raise CheckError("%s failed on %s: %s" % (tool, elf, r.stderr.strip()))
        counts = {}
        for f in os.listdir(d):
            m = re.fullmatch(r"Plain_seg_(\d{3})(?:_chunk_(\d{3}))?\.hex", f)
            if m:
                counts[int(m.group(1))] = counts.get(int(m.group(1)), 0) + 1
    if not counts or sorted(counts) != list(range(len(counts))):
        raise CheckError("%s wrote no segments, or not segments 0..n-1, for %s" % (tool, elf))
    return [counts[i] for i in range(len(counts))]


# ---------------------------------------------------------------------- plan

def plan(root, changed_file, max_jobs=20, out=sys.stdout):
    """The harness units a change affects, as {"units": [...], "all": bool, "jobs": [[...], ...]}.

    A changed harness directory, proof or counterexample marks its harness; a
    change under theories/ or toolchain/ marks every harness; anything else
    (docs, notes, tools, workflows) marks none.  The controls run on every
    pull request regardless."""
    tree = facts.load(root)
    with open(changed_file, encoding="utf-8") as f:
        changed = [l.strip() for l in f if l.strip()]
    every = sorted("%s/%s" % (h.project.name, h.name) for h in tree.harnesses() if h.builds())
    units, full = set(), False
    for rel in changed:
        if rel.startswith(("theories/", "toolchain/")) or rel == "dune-project":
            full = True
            continue
        m = re.match(r"(projects|proofs|counterexamples)/([^/]+)/([^/]+)/", rel)
        if m and m.group(2) != "lib":
            unit = "%s/%s" % (m.group(2), m.group(3))
            if unit in every:
                units.add(unit)
        elif rel.startswith("proofs/lib/"):
            units.update(sid.rsplit("/", 1)[0] for sid in tree.proofs)
    chosen = every if full else sorted(units)
    n = max(1, min(max_jobs, len(chosen)))
    shards = [chosen[i::n] for i in range(n)] if chosen else []
    with_cx = {sid.rsplit("/", 1)[0] for sid in tree.counterexamples}
    jobs = [{"index": i, "units": " ".join(j), "projects": " ".join(sorted({u.split("/")[0] for u in j})),
             "counterexamples": " ".join(u for u in j if u in with_cx)} for i, j in enumerate(shards)]
    json.dump({"all": full, "units": chosen, "jobs": jobs}, out, indent=None)
    out.write("\n")
    return 0
