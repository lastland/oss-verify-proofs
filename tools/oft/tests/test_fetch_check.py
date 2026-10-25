"""oft fetch, verify-sha, check and plan, against stand-in archives and tools."""
import hashlib
import io
import json
import os
import re
import resource
import shutil
import stat
import subprocess
import tarfile
import tempfile
import unittest
from unittest import mock

from oft import check, facts, fetch
from oft.tests.helpers import tree

HAVE_ZSTD = shutil.which("zstd") is not None


def make_release(t, assets, members=None, tamper=None, padding=0):
    """Give zlib's published builds stand-in bytes, pack them as the release
    asset in `assets`, and record both levels of SHA-256 in the facts.
    `padding` zero bytes follow the tar's end-of-archive blocks, as a tar
    written with a large blocking factor has."""
    proj = facts.load(t.root).projects["zlib"]
    files = {}
    for h in proj.harnesses.values():
        y = t.yaml(os.path.join(h.dir, "harness.yaml"))
        for b, rec in h.builds():
            data = b"\x7fELF stand-in for " + rec["file"].encode()
            files["%s/%s" % (h.name, rec["file"])] = data
            y["builds"][b]["bytes"] = len(data)
            y["builds"][b]["sha256"] = hashlib.sha256(data).hexdigest()
        t.put_yaml(os.path.join(h.dir, "harness.yaml"), y)
    if tamper:
        files = tamper(files)
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w") as tf:
        for name, data in (members or files).items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    tar = os.path.join(assets, "zlib-bin.tar")
    with open(tar, "wb") as f:
        f.write(raw.getvalue() + b"\0" * padding)
    subprocess.run(["zstd", "-q", "-f", "--rm", tar], check=True)
    arc = tar + ".zst"
    p = t.yaml("projects/zlib/project.yaml")
    p["assets"]["bin"]["bytes"] = os.path.getsize(arc)
    p["assets"]["bin"]["sha256"] = facts.sha256_file(arc)
    t.put_yaml("projects/zlib/project.yaml", p)
    assert t.generate() == 0, t.last_output
    return files


def run(fn, *a, **kw):
    buf = io.StringIO()
    rc = fn(*a, out=buf, **kw)
    return rc, buf.getvalue()


@unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
class Fetch(unittest.TestCase):
    def test_fetch_and_verify(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            files = make_release(t, a)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked", out)
            for name, data in files.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertEqual(run(fetch.verify_sha, t.root, ["zlib"])[0], 0)

    def test_an_archive_that_is_not_the_pinned_one(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            with open(os.path.join(a, "zlib-bin.tar.zst"), "ab") as f:
                f.write(b"x")
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("project.yaml pins", out)

    def test_an_archive_with_padding_after_its_last_member(self):
        """tarfile stops at the end-of-archive blocks while zstd still has the
        padding after them to write; 4 MiB of it, more than a pipe holds, keeps
        zstd writing, so a fetch that closed the pipe early would kill it."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, padding=4 << 20)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked", out)

    def test_a_member_that_is_not_a_harness_file(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **{"../escape": b"x"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("unexpected member", out)
            self.assertFalse(os.path.exists(t.path("projects/zlib/escape")))

    def test_the_licence_files_of_the_copyleft_components(self):
        lic = {"LICENSES/zlib/LICENSE": b"zlib licence\n", "LICENSES/glib/COPYING": b"LGPL text\n"}
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **lic))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 2 licence files", out)
            for name, data in lic.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            # a later archive without them leaves none behind
            make_release(t, a)
            self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=a)[0], 0)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin/LICENSES")))

    def test_a_licence_member_outside_licenses_component_file(self):
        for bad in ("LICENSES/COPYING", "LICENSES/zlib/doc/COPYING", "LICENSES/../escape", "LICENSES/.hidden/x"):
            with self.subTest(bad), tree() as t, tempfile.TemporaryDirectory() as a:
                make_release(t, a, tamper=lambda f: dict(f, **{bad: b"x"}))
                rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
                self.assertEqual(rc, 1, out)
                self.assertIn("unexpected member", out)

    def test_a_member_whose_bytes_are_not_pinned(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **{"checksum_fuzzer/checksum_fuzzer.asan": b"\x7fELF other"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("does not match its harness.yaml SHA-256", out)

    def test_verify_sha_notices_a_changed_or_missing_file(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=a)[0], 0)
            with open(t.path("projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain"), "ab") as f:
                f.write(b"!")
            rc, out = run(fetch.verify_sha, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("does not match", out)

    def test_a_project_without_binaries(self):
        with tree() as t:
            rc, out = run(fetch.fetch, t.root, ["imagemagick"])
            self.assertEqual(rc, 1)
            self.assertIn("no binaries in this release", out)


class Listing(unittest.TestCase):
    """`oft fetch --release TAG --list`, what release.yml compares a draft with: each tag lists exactly the files the
    facts attach to it, and the recipe goes with the source assets."""

    def listed(self, t, release):
        rc, out = run(fetch.fetch, t.root, [], release=release, listing=True)
        return rc, sorted(line.split()[1] for line in out.splitlines() if line.startswith(release + " "))

    def test_one_release_lists_every_file(self):
        with tree() as t:
            rc, files = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertIn("zlib-bin.tar.zst", files)
            self.assertIn("zlib-src.tar.zst", files)
            self.assertIn("zlib-src.MANIFEST.tsv", files)
            self.assertIn("recipe.tar.zst", files)

    def test_a_source_release_lists_the_source_assets_and_the_recipe_and_the_release_the_binaries(self):
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            for k in ("src", "src_manifest"):
                p["assets"][k]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/zlib/project.yaml", p)
            r = t.yaml("release.yaml")
            r["recipe"]["release"] = "v2026.11.0-src"
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            rc, main = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertNotIn("zlib-src.tar.zst", main)
            self.assertNotIn("recipe.tar.zst", main)
            self.assertIn("zlib-bin.tar.zst", main)
            self.assertTrue(all(f.endswith("-bin.tar.zst") for f in main), main)
            rc, src = self.listed(t, "v2026.11.0-src")
            self.assertEqual(rc, 0)
            self.assertEqual(src, ["recipe.tar.zst", "zlib-src.MANIFEST.tsv", "zlib-src.tar.zst"])


ROCQCHK_OK = """Checking library: X
CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Axioms:
    Corelib.Init.Something.prim
%s
* Constants/Inductives relying on type-in-type: <none>

* Constants/Inductives relying on unsafe (co)fixpoints: %s

* Inductives whose positivity is assumed: <none>

Modules were successfully checked
"""


class Tools:
    """Stand-ins for dune, rocq, rocqchk and qemu-riscv64 on PATH."""

    def __init__(self, d, extra_axiom="", unsafe="<none>", wrapper_fails=False, compile_fails_on=None):
        self.bin = os.path.join(d, "stub-bin")
        self.log = os.path.join(d, "calls.log")
        os.makedirs(self.bin)
        self.put("dune", 'echo "dune $*" >> "%s"\nexit 0\n' % self.log)
        body = ROCQCHK_OK % (("    " + extra_axiom + "\n") if extra_axiom else "", unsafe)
        with open(os.path.join(d, "rocqchk.out"), "w") as f:
            f.write(body)
        self.put("rocqchk", 'echo "rocqchk $*" >> "%s"\ncat "%s"\n' % (self.log, os.path.join(d, "rocqchk.out")))
        # what the wrapper's Print Assumptions prints (Set Printing Fully Qualified; Rocq 9.2.0's pr_assumptionset)
        wrapper = "Axioms:\nCorelib.Init.Something.prim : Prop\n"
        if extra_axiom:
            wrapper += extra_axiom + ("" if " : " in extra_axiom else " : False") + "\n"
        if unsafe != "<none>":
            wrapper += "%s is assumed to be guarded.\n" % unsafe
        with open(os.path.join(d, "wrapper.out"), "w") as f:
            f.write(wrapper)
        # `rocq dep -sort` prints, in order, the whole closure of the .v files it is given: the files of a library on its
        # -Q path (a ...lib or Shared logical name) first, as the real one does, then the files given.  `rocq dep` prints make
        # rules, in which Sub/Deep.v requires Base.v beside Sub/, so a test can see that a library is compiled in
        # dependency order.
        self.put("rocq", 'echo "rocq $*" >> "%s"\nulimit -s >> "%s"\n'
                         'if [ "$1" = dep ] && [ "$2" = -sort ]; then\n'
                         '  prev=""; for a in "$@"; do\n'
                         '    case "$a" in *.lib|OssFuzzTheorems.Proofs.Shared) find "$prev" -name "*.v" | sort ;; esac; prev="$a"; done\n'
                         '  for f in "$@"; do case "$f" in *.v) echo "$f" ;; esac; done; exit 0; fi\n'
                         'if [ "$1" = dep ]; then\n'
                         '  for f in "$@"; do case "$f" in *.v) x=""\n'
                         '    case "$f" in */Sub/Deep.v) x=" $(dirname "$(dirname "$f")")/Base.vo" ;; esac\n'
                         '    echo "${f%%.v}.vo ${f%%.v}.glob: $f$x" ;; esac; done; exit 0; fi\n'
                         'case "$*" in *Wrapper.v*) cat "%s"; %s ;; esac\n'
                         '%s'
                         'case "$*" in "compile "*/Base.v) sleep 0.5; echo "finished Base.v" >> "%s" ;; esac\n'
                         'exit 0\n'
                 % (self.log, self.log, os.path.join(d, "wrapper.out"), "exit 1" if wrapper_fails else "exit 0",
                    ('case "$*" in *%s*) exit 1 ;; esac\n' % compile_fails_on) if compile_fails_on else "", self.log))
        # aborts on the 13-byte counterexample input, exits 0 on the 8-byte control
        # and records the core file limit it was started with
        self.put("qemu-riscv64", 'ulimit -c >> "%s"\n'
                                 'if [ "$(wc -c < "$2")" -gt 8 ]; then kill -ABRT $$; fi\nexit 0\n'
                 % os.path.join(d, "qemu-core-limit.log"))

    def put(self, name, body):
        p = os.path.join(self.bin, name)
        with open(p, "w") as f:
            f.write("#!/bin/sh\n" + body)
        os.chmod(p, os.stat(p).st_mode | stat.S_IEXEC)

    def calls(self):
        with open(self.log) as f:
            return f.read()


class Check(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.old_path = os.environ["PATH"]

    def tearDown(self):
        os.environ["PATH"] = self.old_path
        self.d.cleanup()

    def tools(self, **kw):
        tl = Tools(self.d.name, **kw)
        os.environ["PATH"] = tl.bin + os.pathsep + self.old_path
        return tl

    def ready(self, t):
        assets = os.path.join(self.d.name, "assets")
        os.makedirs(assets)
        make_release(t, assets)
        self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=assets)[0], 0)
        t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 0, out)
            self.assertIn("projects/zlib/checksum_fuzzer/Statements.vo", tl.calls())
            self.assertIn("projects/zlib/checksum_fuzzer: statements compiled\n", out)
            self.assertNotIn("rocqchk", tl.calls(), "rocqchk runs only when asked")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements_with_rocqchk(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("OssFuzzTheorems.zlib.checksum_fuzzer.Characterise", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_an_axiom_outside_the_allowlist(self):
        with tree() as t:
            self.ready(t)
            self.tools(extra_axiom="Top.cheat")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertIn("axioms outside the allowlist: Top.cheat", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_unsafe_fixpoints(self):
        with tree() as t:
            self.ready(t)
            self.tools(unsafe="Top.loop")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertIn("rocqchk failed", out)

    def test_binaries_not_fetched(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1)
            self.assertIn("run ./oft fetch zlib", out)

    def _proof(self, t, body="Theorem plain_halts_holds : True. Proof. exact I. Qed.\n", s="plain_halts",
               unit="zlib/checksum_fuzzer"):
        st = next(x for x in facts.load(t.root).statements() if x.id == unit + "/" + s)
        t.put_yaml("proofs/%s/%s/proof.yaml" % (unit, s), {
            "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
        t.write("proofs/%s/%s/Proof.v" % (unit, s), body)
        self.assertEqual(t.generate(), 0, t.last_output)

    LIB_MOD = "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib"
    SHARED_MOD = "OssFuzzTheorems.Proofs.Shared"

    def _two_proofs_and_a_library(self, t):
        t.write("proofs/zlib/checksum_fuzzer/lib/Base.v", "Definition one := 1.\n")
        t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 2.\n")
        self._proof(t)
        self._proof(t, "Theorem plain_halts_may_fail_holds : True. Proof. exact I. Qed.\n", s="plain_halts_may_fail")

    def test_shared_sources_compile_once_before_harness_libraries_and_are_on_every_load_path(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/lib/Base.v", "Definition one := 1.\n")
            t.write("proofs/lib/Sub/Deep.v", "Definition two := 2.\n")
            self._two_proofs_and_a_library(t)
            self._proof(t, "Theorem asan_agrees_holds : True. Proof. exact I. Qed.\n",
                        s="asan_agrees", unit="zlib/api-driver")
            tl = self.tools()
            base = t.path("base-statement-build")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer", "zlib/api-driver"],
                          parts="proofs", base=base, rocqchk=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(out.count("proofs/lib: 2 files compiled"), 1, out)
            self.assertIn("3 step(s) passed, 0 failed", out)
            calls = tl.calls().splitlines()
            compiles = [c for c in calls if c.startswith("rocq compile")]
            shared_dir = re.search(r"-Q (\S+) " + re.escape(self.SHARED_MOD) + r"\s", compiles[0]).group(1)
            sharedq = "-Q %s %s" % (shared_dir, self.SHARED_MOD)
            shared = [c for c in compiles if c.split()[-1].startswith(shared_dir + os.sep)]
            self.assertEqual(len(shared), 2, "shared sources are not recompiled by either proof closure")
            self.assertTrue(shared[0].endswith("/Base.v"))
            self.assertTrue(shared[1].endswith("/Sub/Deep.v"))
            self.assertLess(calls.index("finished Base.v"), calls.index(shared[1]))
            coreq = "-Q %s/theories OssFuzzTheorems.Core" % base
            for c in shared:
                self.assertIn(coreq, c)
                self.assertNotIn("OssFuzzTheorems.zlib.", c, "shared sources must not depend on one harness")
                self.assertNotIn(self.LIB_MOD, c)
            harness = [c for c in compiles if c.endswith(("/Base.v", "/Sub/Deep.v")) and c not in shared]
            self.assertEqual(len(harness), 2)
            self.assertLess(calls.index(shared[-1]), calls.index(harness[0]))
            users = [c for c in compiles if c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 6, "three direct proofs and three wrappers compile")
            for c in harness + users:
                self.assertIn(coreq, c)
                self.assertIn(sharedq, c)
            dep_sorts = [c for c in calls if c.startswith("rocq dep -sort")]
            self.assertEqual(len(dep_sorts), 3)
            for c in dep_sorts:
                self.assertIn(sharedq, c)
            chks = [c for c in calls if c.startswith("rocqchk")]
            self.assertEqual(len(chks), 2, "rocqchk runs once per harness")
            for c in chks:
                self.assertIn(sharedq, c)
            self.assertIn(self.LIB_MOD, chks[0])
            self.assertNotIn(self.LIB_MOD, chks[1], "direct proofs need no harness library")

    def test_a_shared_library_failure_is_cached_for_every_proof_and_harness(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/lib/Shared.v", "Definition one := 1.\n")
            self._two_proofs_and_a_library(t)
            self._proof(t, "Theorem asan_agrees_holds : True. Proof. exact I. Qed.\n",
                        s="asan_agrees", unit="zlib/api-driver")
            tl = self.tools(compile_fails_on="Shared.v")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer", "zlib/api-driver"],
                          parts="proofs", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertEqual(out.count("proofs/lib: does not compile: Shared.v"), 3, out)
            compiles = [c for c in tl.calls().splitlines() if c.startswith("rocq compile")]
            self.assertEqual(len(compiles), 1, "a shared failure stops every dependent library and proof")
            self.assertTrue(compiles[0].endswith("/Shared.v"))
            self.assertNotIn("Wrapper.v", tl.calls())
            self.assertNotIn("rocqchk", tl.calls())
            self.assertIn("0 step(s) passed, 3 failed", out)

    def test_shared_library_assumptions_still_fail_both_audits(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/lib/Shared.v", "Definition one := 1.\n")
            self._proof(t)
            cheat = self.SHARED_MOD + ".Shared.cheat"
            tl = self.tools(extra_axiom=cheat)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("axioms outside the allowlist: " + cheat, out)
            self.assertNotIn("rocqchk", tl.calls())
            with open(os.path.join(self.d.name, "wrapper.out"), "w") as f:
                f.write("Axioms:\nCorelib.Init.Something.prim : Prop\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertIn("axioms outside the allowlist: " + cheat, out)
            self.assertIn("0 step(s) passed, 1 failed", out)
            self.assertEqual(len([c for c in tl.calls().splitlines() if c.startswith("rocqchk")]), 1)

    def test_empty_shared_library_and_library_io_failures_are_cached(self):
        for rel in ("proofs/lib", "proofs/zlib/checksum_fuzzer/lib"):
            for problem in ("empty", "io", "dep"):
                with self.subTest(rel=rel, problem=problem), tree() as t:
                    t.write(rel + "/Untrusted.vo", "a prebuilt library must not be used\n")
                    if problem != "empty":
                        t.write(rel + "/Base.v", "Definition one := 1.\n")
                    h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
                    error = OSError("cannot read source") if problem == "io" else check.CheckError("rocq dep failed")
                    libs = {}
                    with mock.patch.object(check, "_compile_in_parallel", side_effect=error) as compile_, \
                            mock.patch.object(check.shutil, "copy", wraps=shutil.copy) as copy_:
                        if problem == "io":
                            copy_.side_effect = error
                        for _ in range(2):
                            with self.assertRaises((check.CheckError, OSError)) as cm:
                                check.compile_lib(t.root, h, t.path("_build/default"), self.d.name, libs, io.StringIO())
                            self.assertIs(cm.exception, libs[rel])
                            self.assertIn("holds no .v file" if problem == "empty" else str(error), str(cm.exception))
                        self.assertEqual(compile_.call_count, 1 if problem == "dep" else 0)
                        self.assertEqual(copy_.call_count, 0 if problem == "empty" else 1)
                        if rel != "proofs/lib":
                            self.assertEqual(libs["proofs/lib"], [], "an absent shared library has no mapping")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_is_compiled_once_and_is_on_every_load_path(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("proofs/zlib/checksum_fuzzer/lib: 2 files compiled", out)
            calls = tl.calls().splitlines()
            deep = [c for c in calls if c.startswith("rocq compile") and c.endswith("/Sub/Deep.v")]
            self.assertEqual(len(deep), 1, "the library is compiled once for two proofs, never again by a proof")
            libdir = re.search(r"-Q (\S+) " + re.escape(self.LIB_MOD) + r"(\s|$)", deep[0]).group(1)
            mapping = "-Q %s %s" % (libdir, self.LIB_MOD)
            users = [c for c in calls if c.startswith("rocq compile") and c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 4, "two proofs and two wrappers compiled")
            for c in users:
                self.assertIn(mapping, c)
            self.assertNotIn("rocqchk", tl.calls(), "rocqchk runs only when asked")
            self.assertLess(calls.index("finished Base.v"), calls.index(deep[0]),
                            "Sub/Deep.v, which requires Base.v, starts only after Base.v is compiled")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_with_rocqchk_one_run_checks_every_proof_of_a_harness(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 0, out)
            chk = [c for c in tl.calls().splitlines() if c.startswith("rocqchk")]
            self.assertEqual(len(chk), 1)
            self.assertIn("-Q", chk[0])
            self.assertIn(self.LIB_MOD, chk[0])
            self.assertEqual(sorted(re.findall(r"(Wrap\.\w+\.Wrapper)\b", chk[0])),
                             ["Wrap.plain_halts.Wrapper", "Wrap.plain_halts_may_fail.Wrapper"])
            self.assertIn("proofs/zlib/checksum_fuzzer: rocqchk over the wrappers of 2 proof(s)", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_that_does_not_compile_fails_each_proof(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools(compile_fails_on="Deep.v")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertEqual(out.count("proofs/zlib/checksum_fuzzer/lib: does not compile"), 2, out)
            self.assertEqual(len([c for c in tl.calls().splitlines()
                                  if c.startswith("rocq compile") and c.endswith("/Sub/Deep.v")]), 1)
            self.assertNotIn("Wrapper.v", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_proof_goes_through_the_wrapper(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("proofs/zlib/checksum_fuzzer/plain_halts: proves zlib/checksum_fuzzer/plain_halts; "
                          "assumptions: 1 axioms, all allowed", out)
            wrapper = [l for l in tl.calls().splitlines() if "Wrapper.v" in l][0].split()[-1]
            with open(wrapper) as f:
                text = f.read()
            self.assertIn("Definition certified : OssFuzzTheorems.zlib.checksum_fuzzer.Statements.plain_halts := "
                          "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.\n"
                          "Set Printing Fully Qualified.\nPrint Assumptions certified.\n", text)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_rocq_runs_with_the_largest_stack_allowed(self):
        # large proof terms overflow the usual 8 MiB stack in the release checker image
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
            try:
                resource.setrlimit(resource.RLIMIT_STACK, (8 << 20, hard))
                rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            finally:
                resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
            self.assertEqual(rc, 0, out)
            want = "unlimited" if hard == resource.RLIM_INFINITY else str(hard // 1024)
            seen = {l for l in tl.calls().splitlines() if l == "unlimited" or l.isdigit()}
            self.assertEqual(seen, {want})

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_proof_of_another_statement(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools(wrapper_fails=True)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("the proof is not of this statement", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_an_axiom_outside_the_allowlist_fails_the_proof(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self.tools(extra_axiom="Top.cheat : False")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertIn("axioms outside the allowlist: Top.cheat", out)
                self.assertIn("FAIL proofs/zlib/checksum_fuzzer/%s:" % s, out)
            self.assertIn("0 step(s) passed, 2 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_unsafe_fixpoints_in_the_assumptions_fail_the_proof(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools(unsafe="Top.loop")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("the proof relies on what the kernel did not check: Top.loop is assumed to be guarded.", out)

    def test_print_assumptions_is_parsed_or_refused(self):
        # the forms Rocq 9.2.0 prints (printing/printer.ml, pr_assumptionset)
        self.assertEqual(check.wrapper_assumptions("$ rocq compile x\nClosed under the global context\n"), set())
        self.assertEqual(check.wrapper_assumptions(
            "$ rocq compile x\nAxioms:\nA.b : forall P : Prop,\n  P\nC.d :\n  nat\n\nWarning: unrelated\n"),
            {"A.b", "C.d"})
        refused = {
            "Axioms:\nA.b : Prop\nTop.T is assumed to be positive.\n": "Top.T is assumed to be positive.",
            "Axioms:\nTop.f is assumed to be guarded.\n": "Top.f is assumed to be guarded.",
            "Axioms:\nTop.f relies on an unsafe hierarchy.\n": "Top.f relies on an unsafe hierarchy.",
            "Axioms:\nTop.eq relies on definitional UIP.\n": "Top.eq relies on definitional UIP.",
            "Axioms:\nA.b : Prop\nTheory:\nSet is impredicative\n": "Theory: Set is impredicative",
            "Theory:\nType hierarchy is collapsed (logic is inconsistent)\n": "Theory: Type hierarchy is collapsed",
            "Axioms:\nA.b : Prop\nTop.untyped\n": "Top.untyped",
            "Axioms:\n\n": "empty",
            "": "neither",
            "some other output\n": "neither",
        }
        for text, why in refused.items():
            with self.assertRaises(check.CheckError, msg=text) as cm:
                check.wrapper_assumptions(text)
            self.assertIn(why, str(cm.exception))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_with_rocqchk_an_axiom_fails_every_proof_of_the_harness(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools(extra_axiom="Top.cheat : False")
            os.remove(os.path.join(self.d.name, "wrapper.out"))
            with open(os.path.join(self.d.name, "wrapper.out"), "w") as f:
                f.write("Axioms:\nCorelib.Init.Something.prim : Prop\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 1)
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertIn("FAIL proofs/zlib/checksum_fuzzer/%s: axioms outside the allowlist: Top.cheat" % s, out)
            self.assertIn("0 step(s) passed, 2 failed", out)
            self.assertEqual(len([c for c in tl.calls().splitlines() if c.startswith("rocqchk")]), 1)

    def test_nothing_to_check(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "x\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("nothing to check", out)

    def test_a_counterexample_reproduces(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            self.tools()
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 0, out)
            self.assertIn("reproduces (exit 134 SIGABRT); control exits 0", out)

    def test_qemu_runs_with_no_core_file(self):
        """With a core file limit above zero here, qemu must still start with
        none, or this test could not tell the two apart."""
        soft, hard = resource.getrlimit(resource.RLIMIT_CORE)
        raised = 1 << 20 if hard == resource.RLIM_INFINITY else hard
        if raised == 0:
            self.skipTest("the core file limit cannot be raised here, so this test could not tell")
        resource.setrlimit(resource.RLIMIT_CORE, (raised, hard))
        try:
            with tree() as t:
                t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
                self.tools()
                rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
                self.assertEqual(rc, 0, out)
        finally:
            resource.setrlimit(resource.RLIMIT_CORE, (soft, hard))
        with open(os.path.join(self.d.name, "qemu-core-limit.log")) as f:
            limits = f.read().split()
        self.assertGreaterEqual(len(limits), 2, "qemu did not run")
        self.assertEqual(set(limits), {"0"}, "qemu must start with no core file")

    def test_a_counterexample_that_stopped_reproducing(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            t.write("counterexamples/json/fuzzer-parse_bjdata/plain_halts/input.bin", "\0" * 6)
            self.tools()
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 1)
            self.assertIn("no longer reproduces", out)


class Plan(unittest.TestCase):
    def plan(self, t, changed):
        p = t.path("changed.txt")
        with open(p, "w") as f:
            f.write("\n".join(changed) + "\n")
        buf = io.StringIO()
        check.plan(t.root, p, out=buf)
        return json.loads(buf.getvalue())

    def test_units(self):
        with tree() as t:
            self.assertEqual(self.plan(t, ["docs/proving.md", "notes/zlib.md"])["units"], [])
            self.assertEqual(self.plan(t, ["proofs/zlib/checksum_fuzzer/plain_halts/Proof.v"])["units"],
                             ["zlib/checksum_fuzzer"])
            everything = self.plan(t, ["theories/Shapes.v"])
            self.assertTrue(everything["all"])
            self.assertEqual(len(everything["units"]), 3)


if __name__ == "__main__":
    unittest.main()
