"""oft generate: deterministic, complete, and checked; and the schemas under it."""
import os
import shutil
import unittest

from oft import facts, generate, schema, shapes, yamlio
from oft.tests.helpers import tree


class Rendering(unittest.TestCase):
    def test_deterministic(self):
        with tree() as a, tree() as b:
            ra = generate.render_all(facts.load(a.root))
            rb = generate.render_all(facts.load(b.root))
            self.assertEqual(ra, rb)
            self.assertEqual(generate.render_all(facts.load(a.root)), ra)

    def test_check_passes_on_a_rendered_tree(self):
        with tree() as t:
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_hand_edit_fails_the_check(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/Statements.v", "(* an edit *)\n", "a")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("differs from its rendering", t.last_output)

    def test_a_facts_change_without_its_rendering_fails(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["asan_agrees"]["budgets"] = "standard"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("projects/zlib/checksum_fuzzer/Statements.v: differs", t.last_output)

    def test_a_stale_generated_file_fails(self):
        with tree() as t:
            t.write("projects/json/fuzzer-parse_bjdata/Characterise.v", "(* left over *)\n")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("no longer produce", t.last_output)

    def test_a_distribution_header_edit_fails(self):
        with tree() as t:
            p = "projects/zlib/checksum_fuzzer/Distribution.v"
            t.write(p, t.read(p).replace("mean 4,096", "mean 4,097"))
            self.assertEqual(t.generate(check=True), 1)

    def test_bad_facts_render_nothing(self):
        with tree() as t:
            t.write("projects/zlib/project.yaml", "extra: 1\n", "a")
            self.assertEqual(t.generate(), 1)
            self.assertIn("nothing rendered", t.last_output)


class StatementText(unittest.TestCase):
    def test_zlib_checksum_fuzzer(self):
        with tree() as t:
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
        self.assertIn("Definition plain_halts : Prop :=\n  halts_within_budget Budgets.Standard.lim_source "
                      "Exits.ok_or_refused Images.plain.", s)
        self.assertIn("Definition plain_halts_may_fail : Prop :=\n  halts_may_fail Exits.any Images.plain.", s)
        self.assertIn("Definition asan_agrees : Prop :=\n  agrees Budgets.Asan.lim_source Budgets.Asan.lim_target "
                      "Images.plain Images.asan.", s)
        self.assertIn("Definition ubsan_agrees : Prop :=\n  agrees Budgets.Standard.lim_source "
                      "Budgets.Standard.lim_target Images.plain Images.ubsan.", s)
        self.assertIn("Definition asan_disagrees_at_most (b : Q) : Prop :=\n  disagrees_at_most Env.may_fail "
                      "Distribution.w Distribution.M Images.plain Images.asan b.", s)
        self.assertIn("From OssFuzzTheorems.zlib.checksum_fuzzer Require Images Distribution.", s)
        self.assertNotIn("Admitted", s)
        self.assertEqual(s.count("(*"), s.count("*)"))

    def test_characterise_and_images(self):
        with tree() as t:
            c = t.read("projects/zlib/checksum_fuzzer/Characterise.v")
            i = t.read("projects/zlib/checksum_fuzzer/Images.v")
            d = t.read("projects/zlib/checksum_fuzzer/images/dune")
        self.assertIn("Definition asan_classifies (C : Image) : Prop :=\n  classifies Env.may_fail Images.plain "
                      "Images.asan C.", c)
        self.assertIn("Lemma asan_ubsan_wf : image_wf asan_ubsan.", i)
        self.assertIn("(targets Plain.v Plain_seg_000.hex Plain_seg_001.hex Plain_seg_002.hex Plain_seg_003.hex)", d)

    def test_chunked_segments(self):
        self.assertEqual(generate.hex_targets("Plain", [1, 2]),
                         ["Plain_seg_000.hex", "Plain_seg_001_chunk_000.hex", "Plain_seg_001_chunk_001.hex"])

    def test_a_harness_name_that_is_not_an_identifier(self):
        with tree() as t:
            s = t.read("projects/json/fuzzer-parse_bjdata/Statements.v")
            dune = t.read("projects/json/fuzzer-parse_bjdata/dune")
        self.assertIn("(name OssFuzzTheorems.json.fuzzer_parse_bjdata)", dune)
        self.assertIn("agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source", s)

    def test_a_withheld_statement_is_listed_not_stated(self):
        with tree() as t:
            s = t.read("projects/zlib/api-driver/Statements.v")
            r = t.read("projects/zlib/api-driver/README.md")
        self.assertIn("(* asan_ubsan_agrees: withheld; see README.md. *)", s)
        self.assertNotIn("Definition asan_ubsan_agrees", s)
        self.assertIn("withheld: not in this release yet", r)
        self.assertNotIn("disclosure", r)

    def test_text_is_safe_inside_a_rocq_comment(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["summary"] = 'Says "hi" (* and *) leaves.'
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
        self.assertNotIn('"hi"', s)
        self.assertIn("( * and * )", s)

    def test_derived_statuses(self):
        with tree() as t:
            st = {s.id: s.status for s in facts.load(t.root).statements()}
            tsv = t.read("index/statements.tsv")
        self.assertEqual(st["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")
        # the same run (the plain build aborts) refutes the agreement statement that names the plain build
        self.assertEqual(st["json/fuzzer-parse_bjdata/asan_agrees"], "counterexample")
        self.assertIn("json/fuzzer-parse_bjdata/plain_halts\thalts\tplain\tbudget\t0,2\tcounterexample\t"
                      "counterexamples/json/fuzzer-parse_bjdata/plain_halts\t1\t", tsv)

    def test_a_counterexample_that_exits_does_not_refute_agreement(self):
        with tree() as t:
            y = t.yaml("counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml")
            y["observed"] = {"build": "plain", "exit": 77}
            t.put_yaml("counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml", y)
            st = {s.id: s.status for s in facts.load(t.root).statements()}
        self.assertEqual(st["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")
        self.assertEqual(st["json/fuzzer-parse_bjdata/asan_agrees"], "suspected-false")

    def test_a_witness_is_described_from_its_fields(self):
        with tree() as t:
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
            k = t.read("analyses/known-issues.md")
        want = ("false (witnessed): with the input file `01 00 00 00 00 00 00`, refusing the 3rd memory request "
                "(an mmap of 4,096 bytes) makes the UBSan build end in an abort (SIGABRT) on an uncaught "
                "std::bad_alloc (run under qemu-riscv64 10.0.11)")
        self.assertIn(want, r)
        self.assertIn("zlib/checksum_fuzzer/ubsan_halts_may_fail", k)

    def test_a_statement_level_model_gap(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["plain_halts"].update(status="model-gap", gap=["vector-instructions"])
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("blocked by the model: the binary runs RISC-V vector instructions", r)
        self.assertIn("Some statements are blocked by the model", r)

    def test_fingerprints_ignore_docstrings_but_not_bytes(self):
        with tree() as t:
            before = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["summary"] = "A different summary."
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(before, {s.id: s.fingerprint for s in facts.load(t.root).statements()})
            y["builds"]["plain"]["sha256"] = "0" * 63 + "a"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            after = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
        changed = sorted(k for k in before if before[k] != after[k])
        self.assertIn("zlib/checksum_fuzzer/plain_halts", changed)
        self.assertNotIn("zlib/checksum_fuzzer/ubsan_halts", changed)

    def test_the_project_pages(self):
        with tree() as t:
            z = t.read("projects/zlib/README.md")
            im = t.read("projects/imagemagick/README.md")
            top = t.read("README.md")
            status = t.read("index/STATUS.md")
        self.assertIn("1 of OSS-Fuzz's 2 fuzz targets has statements, plus an API driver", z)
        self.assertIn("**minigzip_fuzzer** (not built yet)", z)
        self.assertIn("Some builds are not in this release yet.", z)
        for word in ("disclosure", "finding", "withheld patch"):
            self.assertNotIn(word, z)
        self.assertIn("**Status: not yet built.** Needs Ghostscript in the build image. [What the statuses mean]", im)
        self.assertIn("[`zlib/checksum_fuzzer/plain_halts`]", top)
        self.assertIn("0 proved", top)
        self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 + API driver | 8 |", status)

    def test_a_rebuild_is_invited_only_beside_a_source_bundle(self):
        """A rebuild needs the build scripts, which come with the source bundle:
        a real builder digest alone must not make the page invite one."""
        digest = "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:" + "3" * 64
        invite = "A binary whose SHA-256 differs after a rebuild with it is a bug"
        with tree() as t:
            z = t.read("projects/zlib/README.md")       # has a source bundle
            j = t.read("projects/json/README.md")       # has none
            self.assertIn("Builder image: `%s`. %s" % (digest, invite), z)
            self.assertIn("Builder image: `%s`. These binaries cannot yet be rebuilt from this release" % digest, j)
            self.assertNotIn(invite, j)
            zero = digest.split("@")[0] + "@sha256:" + "0" * 64
            r = t.yaml("release.yaml")
            r["images"]["builder"].append(zero)
            t.put_yaml("release.yaml", r)
            y = t.yaml("projects/json/project.yaml")
            y["build"]["builder"] = zero
            t.put_yaml("projects/json/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            j = t.read("projects/json/README.md")
            self.assertIn("Builder image: not published yet", j)
            self.assertNotIn(invite, j)

    def test_counts_agree_everywhere(self):
        """The README's counts, STATUS.md's rows and index/statements.tsv are one set of numbers."""
        with tree() as t:
            tree_ = facts.load(t.root)
            n, by, held = generate.statement_counts(tree_)
            top = t.read("README.md")
            rows = [l.split("\t") for l in t.read("index/statements.tsv").splitlines()[1:]]
            prow = [l.split("\t") for l in t.read("index/projects.tsv").splitlines()[1:]]
        self.assertEqual(len(rows), n)
        for status, k in by.items():
            self.assertEqual(sum(1 for r in rows if r[5] == status), k, status)
        self.assertIn(generate.counts_sentence(tree_), top)
        self.assertEqual(sum(int(r[9]) for r in prow), n)
        self.assertEqual(sum(int(r[15]) for r in prow), by["withheld"])

    def test_project_page_links_resolve(self):
        with tree() as t:
            for rel in ("projects/json/README.md", "projects/json/fuzzer-parse_bjdata/README.md", "README.md",
                        "analyses/known-issues.md", "index/STATUS.md"):
                import re
                base = os.path.dirname(t.path(rel))
                for target in re.findall(r"\]\(([^)#:]+)(?:#[^)]*)?\)", t.read(rel)):
                    if not any(x in target for x in ("counterexamples/", "projects/", "index/", "analyses/")):
                        continue          # docs/ and the hand-written files are not in the fixture
                    self.assertTrue(os.path.exists(os.path.normpath(os.path.join(base, target))),
                                    "%s links to %s" % (rel, target))


class Shapes(unittest.TestCase):
    def st(self, **kw):
        base = {"kind": "agreement", "builds": ["plain", "asan"], "reading": "may-fail", "budgets": "asan"}
        base.update(kw)
        return base

    def test_every_agreement_shape(self):
        want = {("may-fail", "error", "rv64g"): "agrees", ("may-fail", "signal", "rv64g"): "agrees_abort_modelled",
                ("alloc-forced-only", "error", "rv64g"): "agrees_in",
                ("alloc-forced-only", "signal", "rv64g"): "agrees_in_abort_modelled",
                ("may-fail", "error", "rv64gc"): "agrees_rv64gc",
                ("may-fail", "signal", "rv64gc"): "agrees_abort_modelled_rv64gc",
                ("alloc-forced-only", "error", "rv64gc"): "agrees_in_rv64gc"}
        for (reading, abort, machine), name in want.items():
            self.assertEqual(shapes.shape_name(self.st(reading=reading, abort=abort, machine=machine)), name)

    def test_combinations_with_no_shape_are_refused(self):
        for bad in (self.st(reading="alloc-forced-only", abort="signal", machine="rv64gc"),
                    self.st(reading="budget"), self.st(budgets=None),
                    {"kind": "halts", "builds": ["asan"], "reading": "budget", "exits": [0, 1]},
                    {"kind": "halts", "builds": ["asan"], "reading": "alloc-forced-only", "exits": "any"},
                    {"kind": "bound", "builds": ["plain", "asan"], "reading": "may-fail", "abort": "signal"}):
            bad = {k: v for k, v in bad.items() if v is not None}
            with self.assertRaises(shapes.ShapeError):
                shapes.term(bad)

    def test_rv64gc_input_set_shapes(self):
        st = {"kind": "decidability", "builds": ["plain", "asan"], "reading": "may-fail", "machine": "rv64gc"}
        self.assertEqual(shapes.shape_name(st), "agreement_decidable_rv64gc")

    def test_binding(self):
        halts = {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2]}
        check = {"stops_with": "exit", "exit_status": 1, "live": True}
        self.assertTrue(shapes.binds(check, halts))
        self.assertFalse(shapes.binds(dict(check, exit_status=2), halts))
        self.assertFalse(shapes.binds(dict(check, live="unknown"), halts))
        self.assertFalse(shapes.binds({"stops_with": "print-only", "live": True}, halts))


class Schemas(unittest.TestCase):
    def test_the_fixture_validates(self):
        with tree(render=False) as t:
            for rel, kind in (("release.yaml", "release"), ("projects/zlib/project.yaml", "project"),
                              ("projects/zlib/checksum_fuzzer/harness.yaml", "harness")):
                self.assertEqual(schema.validate(kind, t.yaml(rel)), [], rel)

    def test_closed(self):
        with tree(render=False) as t:
            y = t.yaml("projects/zlib/project.yaml")
            y["colour"] = {"shade": "blue"}
            self.assertTrue(any("unknown key" in e for e in schema.validate("project", y)))

    def test_yaml_is_strict(self):
        self.assertEqual(yamlio.load("d: 2026-11-02\nb: yes\n"), {"d": "2026-11-02", "b": "yes"})
        with self.assertRaises(yamlio.YamlError):
            yamlio.load("a: 1\na: 2\n")

    def test_every_template_placeholder_has_a_value(self):
        """A missing value raises; rendering the fixture exercises every block used."""
        with tree() as t:
            self.assertTrue(os.path.isfile(t.path("projects/zlib/checksum_fuzzer/Characterise.v")))



class UninstrumentedWords(unittest.TestCase):
    def test_the_readme_names_what_each_build_links_uninstrumented(self):
        with tree() as t:
            h = "projects/zlib/checksum_fuzzer/harness.yaml"
            y = t.yaml(h)
            y["builds"]["asan"]["uninstrumented"] = [
                {"name": "libclang_rt.asan.a", "kind": "sanitizer-runtime"},
                {"name": "crc32_x86.S.o", "kind": "assembly", "source": "contrib/crc32_x86.S"}]
            t.put_yaml(h, y)
            self.assertEqual(t.generate(), 0)
            readme = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("- asan: `libclang_rt.asan.a` (the sanitizer runtime), `crc32_x86.S.o` from "
                          "`contrib/crc32_x86.S` (assembly)", readme)
            self.assertNotIn("is not recorded in this release", readme)

    def test_with_no_list_the_readme_says_it_is_not_recorded(self):
        with tree() as t:
            readme = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("Which other code each build links uninstrumented is not recorded in this release.", readme)
            st = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            self.assertIn("in the code it instruments", st)


class PublishedModel(unittest.TestCase):
    def test_publishing_the_model_changes_the_readme_and_no_fingerprint(self):
        """semantics.published: the model is public at its commit while its version is still unreleased."""
        with tree() as t:
            r = t.yaml("release.yaml")
            r["semantics"]["version"] = "unreleased"
            t.put_yaml("release.yaml", r)
            for p in ("proofs", "counterexamples"):         # fingerprints move with the version: no evidence here
                shutil.rmtree(t.path(p), ignore_errors=True)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("Nothing here can be checked from outside yet", t.read("README.md"))
            before = t.read("index/statements.tsv")
            r["semantics"]["published"] = True
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
            self.assertNotIn("Nothing here can be checked from outside yet", readme)
            c = r["semantics"]["commit"]
            self.assertIn("commit [`%s`](%s/commit/%s)" % (c[:12], r["semantics"]["repository"], c), readme)
            self.assertEqual(t.read("index/statements.tsv"), before)


if __name__ == "__main__":
    unittest.main()


class HeldAndExitWitness(unittest.TestCase):
    """A project or a fuzz target held from the release says only that, with no reason; a witness may end in an
    exit with a status the halts statement does not allow."""

    def test_a_held_project_page_says_only_that_it_is_held(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y.update(status="held", reason="held")
            y.pop("reason_args")
            t.put_yaml("projects/imagemagick/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/imagemagick/README.md")
            status = t.read("index/STATUS.md")
        self.assertIn("**Status: held.** Held from this release. [What the statuses mean]", page)
        self.assertNotIn("Ghostscript", page)
        self.assertIn("| [imagemagick](../projects/imagemagick/) | c++ | held |", status)

    def test_a_held_project_takes_no_reason_text(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y.update(status="held", reason="dependency")
            t.put_yaml("projects/imagemagick/project.yaml", y)
            t.generate()
            self.assertTrue(any("is not a held reason" in f.msg for f in t.lint()))

    def test_a_held_fuzz_target_is_listed_as_held(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            for e in y["harnesses"]:
                if e["name"] == "minigzip_fuzzer":
                    e["reason"] = "held"
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
        self.assertIn("**minigzip_fuzzer** (held from this release)", page)

    def hold_zlib_api_driver(self, t, origin=True):
        """zlib's API driver held: listed as not included with reason held, its directory moved out of the tree (not
        deleted), and release.yaml's counts without its harness and builds."""
        y = t.yaml("projects/zlib/project.yaml")
        for e in y["harnesses"]:
            if e["name"] == "api-driver":
                e.update(status="not-included", reason="held")
                if not origin:
                    e.pop("origin")
        y.pop("withheld")           # the fixture's only withheld statement is the API driver's
        t.put_yaml("projects/zlib/project.yaml", y)
        n_builds = len(t.yaml("projects/zlib/api-driver/harness.yaml")["builds"])
        os.rename(t.path("projects/zlib/api-driver"), t.path("..", "api-driver-aside"))
        r = t.yaml("release.yaml")
        r["counts"]["harnesses"] -= 1
        r["counts"]["binaries"] -= n_builds
        t.put_yaml("release.yaml", r)

    def test_a_held_api_driver_is_listed_as_held_and_counted_nowhere(self):
        with tree() as t:
            self.hold_zlib_api_driver(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            status = t.read("index/STATUS.md")
            row = [r for r in t.read("index/projects.tsv").splitlines() if r.startswith("zlib\t")]
        self.assertIn("**api-driver** (held from this release)", page)
        self.assertNotIn("plus an API driver", page)
        self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 |", status)
        self.assertEqual(row[0].split("\t")[6], "no")
        # control: the included API driver is counted in both
        with tree() as t:
            self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 + API driver |",
                          t.read("index/STATUS.md"))
            row = [r for r in t.read("index/projects.tsv").splitlines() if r.startswith("zlib\t")]
            self.assertEqual(row[0].split("\t")[6], "yes")

    def test_a_held_api_driver_still_has_origin_this_repository(self):
        with tree() as t:
            self.hold_zlib_api_driver(t, origin=False)
            t.generate()
            self.assertTrue(any("api-driver, and only api-driver, has origin this-repository" in f.msg
                                for f in t.lint()))

    def exit_witness(self, t, **w):
        y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
        wit = {"build": "plain", "input_hex": "01000000000000", "outcome": "exit", "exit": 78,
               "runner": "qemu-riscv64 10.0.11"}
        wit.update(w)
        y["statements"]["plain_halts"].update(status="witnessed-false", witness={k: v for k, v in wit.items()
                                                                                if v is not None})
        y["statements"]["plain_halts"].pop("binds_checks", None)
        t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)

    def test_a_witness_that_ends_in_an_exit(self):
        with tree() as t:
            self.exit_witness(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("false (witnessed): with the input file `01 00 00 00 00 00 00` and nothing refused, the plain "
                      "build ends in exit status 78 (run under qemu-riscv64 10.0.11)", r)

    def test_an_exit_witness_must_be_one_the_statement_forbids(self):
        for w, msg in (({"exit": 2}, "which the statement allows"),
                       ({"exit": None}, "exactly when it ends in an exit"),
                       ({"after": "failed-assertion"}, "`after` is for a witness that ends in a signal")):
            with tree() as t:
                self.exit_witness(t, **w)
                t.generate()
                self.assertTrue(any(msg in f.msg for f in t.lint()), (w, [str(f) for f in t.lint()]))
        with tree() as t:
            # an abort with an exit status is refused too: the status is the exit's
            self.exit_witness(t, outcome="abort")
            t.generate()
            self.assertTrue(any("exactly when it ends in an exit" in f.msg for f in t.lint()))


class ProofLibrary(unittest.TestCase):
    def proof(self, t):
        st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
        t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", {
            "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
        t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")

    def test_a_harness_library_gets_a_dune_and_its_proofs_depend_on_it(self):
        with tree() as t:
            self.proof(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertNotIn("OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib",
                             t.read("proofs/zlib/checksum_fuzzer/plain_halts/dune"))
            t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 2.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            lib = t.read("proofs/zlib/checksum_fuzzer/lib/dune")
            self.assertIn("(include_subdirs qualified)", lib)
            self.assertIn("(name OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib)", lib)
            self.assertIn("(package rocq-oss-fuzz-theorems-zlib-proofs)", lib)
            self.assertIn(" OssFuzzTheorems.zlib.checksum_fuzzer OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib)",
                          t.read("proofs/zlib/checksum_fuzzer/plain_halts/dune"))
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_without_a_shared_library_the_old_rendering_is_preserved(self):
        with tree() as t:
            self.proof(t)
            t.write("proofs/zlib/checksum_fuzzer/lib/Base.v", "Definition one := 1.\n")
            loaded = facts.load(t.root)
            self.assertFalse(loaded.shared_proof_lib)
            rendered = generate.render_all(loaded)
            deps = "Stdlib stdpp ReadFile Flocq LinuxProcessSemantics OssFuzzTheorems.Core Ltac2"
            self.assertEqual(rendered["proofs/zlib/checksum_fuzzer/lib/dune"],
                             "; generated by oft generate; do not edit.\n"
                             "; The proof library of this harness: every .v file below, at any depth.\n"
                             "(include_subdirs qualified)\n(rocq.theory\n"
                             " (name OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib)\n"
                             " (package rocq-oss-fuzz-theorems-zlib-proofs)\n"
                             " (theories " + deps + " OssFuzzTheorems.zlib.checksum_fuzzer))\n")
            self.assertEqual(rendered["proofs/zlib/checksum_fuzzer/plain_halts/dune"],
                             "; generated by oft generate; do not edit.\n(rocq.theory\n"
                             " (name OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts)\n"
                             " (package rocq-oss-fuzz-theorems-zlib-proofs)\n"
                             " (theories " + deps + " OssFuzzTheorems.zlib.checksum_fuzzer "
                             "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib))\n")
            self.assertIn(" (depends rocq-oss-fuzz-theorems-core))", rendered["dune-project"])
            self.assertNotIn("proofs-shared", rendered["dune-project"])
            self.assertNotIn("proofs/lib/dune", rendered)

    def test_a_shared_library_adds_only_proof_dependencies_and_keeps_fingerprints(self):
        with tree() as t:
            self.proof(t)
            t.write("proofs/zlib/checksum_fuzzer/lib/Base.v", "Definition one := 1.\n")
            before = facts.load(t.root)
            old = generate.render_all(before)
            t.write("proofs/lib/Base.v", "Definition shared := 1.\n")
            t.write("proofs/lib/Sub/Deep.v", "Definition two := 2.\n")
            after = facts.load(t.root)
            self.assertTrue(after.shared_proof_lib)
            self.assertEqual(after.errors, [])
            self.assertEqual(before.proof_libs, after.proof_libs)
            self.assertEqual({s.id: s.fingerprint for s in before.statements()},
                             {s.id: s.fingerprint for s in after.statements()})
            new = generate.render_all(after)
            self.assertEqual(set(new) - set(old), {"proofs/lib/dune"})
            self.assertEqual({p for p in old if old[p] != new[p]}, {
                "dune-project", "proofs/zlib/checksum_fuzzer/lib/dune",
                "proofs/zlib/checksum_fuzzer/plain_halts/dune"})
            shared = new["proofs/lib/dune"]
            self.assertIn("(include_subdirs qualified)", shared)
            self.assertIn("(name OssFuzzTheorems.Proofs.Shared)", shared)
            self.assertIn("(package rocq-oss-fuzz-theorems-proofs-shared)", shared)
            self.assertNotIn("Shared", shared.split("(theories ")[1], "the shared theory must not depend on itself")
            for p in ("proofs/zlib/checksum_fuzzer/lib/dune", "proofs/zlib/checksum_fuzzer/plain_halts/dune"):
                self.assertIn(" OssFuzzTheorems.Proofs.Shared ", new[p])
            self.assertIn(" (depends rocq-oss-fuzz-theorems-core rocq-oss-fuzz-theorems-proofs-shared))",
                          new["dune-project"])
            statement_package = next(p for p in old["dune-project"].split("\n\n")
                                     if "(name rocq-oss-fuzz-theorems-zlib)" in p)
            self.assertIn(statement_package, new["dune-project"])
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.generate(check=True), 0, t.last_output)
            t.write("proofs/lib/Base.v", "Definition shared := 2.\n")
            self.assertEqual(generate.render_all(facts.load(t.root)), new)
            shutil.rmtree(t.path("proofs/lib"))
            self.assertEqual(generate.render_all(facts.load(t.root)), old)

    def test_the_shared_directory_alone_gets_a_separate_package(self):
        with tree() as t:
            os.makedirs(t.path("proofs/lib"))
            loaded = facts.load(t.root)
            self.assertTrue(loaded.shared_proof_lib, "presence is recorded even before sources are added")
            self.assertEqual(loaded.proofs, {})
            self.assertEqual(loaded.proof_libs, [])
            rendered = generate.render_all(loaded)
            self.assertIn("proofs/lib/dune", rendered)
            self.assertIn('(name rocq-oss-fuzz-theorems-proofs-shared)\n'
                          ' (synopsis "Shared helpers for proofs of OSS-Fuzz theorem statements")\n'
                          ' (license MIT)\n (depends rocq-oss-fuzz-theorems-core))', rendered["dune-project"])
            self.proof(t)
            direct = generate.render_all(facts.load(t.root))["proofs/zlib/checksum_fuzzer/plain_halts/dune"]
            self.assertIn(" OssFuzzTheorems.Proofs.Shared ", direct)
            self.assertNotIn("OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib", direct)
