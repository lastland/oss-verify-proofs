"""Every rule of `oft lint`, each with a planted positive that must fail it,
and the clean fixture and this repository itself, which must pass."""
import hashlib
import os
import tempfile
import unittest
from unittest import mock

from oft import facts, lint, paths
from oft.tests.helpers import REPO, Tree, rules_of, tree


class Clean(unittest.TestCase):
    def test_fixture_is_clean(self):
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_this_repository_is_clean(self):
        found = lint.run(REPO, skeleton=True)
        self.assertEqual([str(f) for f in found], [])
        self.assertGreater(len(lint.walk(REPO)), 20, "examined almost nothing")

    def test_a_scan_that_examines_nothing_fails(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(rules_of(lint.run(d, skeleton=True)), ["paths"])


class Paths(unittest.TestCase):
    def test_shared_library_sources_and_generated_dune_each_have_one_owner(self):
        for rel, cls in (("proofs/lib/dune", "gen"), ("proofs/lib/Base.v", "contrib"),
                         ("proofs/lib/Sub/Deep.v", "contrib")):
            with self.subTest(rel=rel):
                matches = paths.classify(rel)
                self.assertEqual(len(matches), 1, matches)
                self.assertEqual((matches[0][0], matches[0][2]), (cls, {}))
        self.assertEqual(paths.classify("proofs/lib/Sub/dune"), [])
        self.assertEqual(paths.classify("proofs/lib/stray.txt"), [])

    def test_a_stray_path(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/scratch/x.log", "a stray file\n")
            self.assertIn("paths", rules_of(t.lint()))

    def test_a_derived_file(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/Statements.vo", "x")
            self.assertIn("paths", rules_of(t.lint()))

    def test_an_elf_file(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/source/a.out", "\x7fELF\x02\x01\x01")
            found = t.lint()
            self.assertTrue(any("an ELF file" in f.msg for f in found))

    def test_an_lfs_pointer(self):
        with tree() as t:
            t.write("notes/json.md", "version https://git-lfs.github.com/spec/v1\noid sha256:00\n")
            self.assertTrue(any("LFS" in f.msg for f in t.lint()))

    def test_a_non_release_change_to_facts(self):
        with tree() as t:
            changed = ["projects/zlib/checksum_fuzzer/harness.yaml"]
            self.assertIn("paths", rules_of(t.lint(changed=changed, pr_kind="maintainer")))
            self.assertEqual(t.lint(changed=changed, pr_kind="release"), [])

    def test_a_contributor_outside_proofs(self):
        with tree() as t:
            self.assertIn("paths", rules_of(t.lint(changed=["tools/oft/lint.py"], pr_kind="contributor")))
            self.assertEqual(t.lint(changed=["docs/proving.md"], pr_kind="contributor"), [])

    def test_a_size_cap(self):
        with tree() as t:
            t.write("notes/json.md", "x" * (lint.MAX_BYTES + 1))
            self.assertTrue(any("cap" in f.msg for f in t.lint()))


class Schemas(unittest.TestCase):
    def test_an_unknown_key(self):
        with tree() as t:
            t.write("projects/abseil-py/project.yaml", "colour: {shade: blue}\n", "a")
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_repeated_key(self):
        with tree() as t:
            t.write("projects/abseil-py/project.yaml", "status: available\n", "a")
            self.assertTrue(any("duplicate key" in f.msg for f in t.lint()))

    def test_a_bad_digest(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["builds"]["plain"]["sha256"] = "77b4a5be"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_statement_whose_name_its_fields_contradict(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["asan_agrees"]["builds"] = ["plain", "ubsan"]
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("give the name ubsan_agrees" in f.msg for f in t.lint()))

    def test_a_toolchain_lock_with_commentary_or_another_checker(self):
        with tree() as t:
            t.write("toolchain/toolchain.lock", "# the checker we used\nchecker=ghcr.io/theorem-labs/"
                    "oss-fuzz-theorems-checker@sha256:" + "4" * 64 + "\n")
            self.assertEqual(len([f for f in t.lint() if f.rule == "schema"]), 2)

    def test_a_toolchain_lock_naming_images_release_yaml_does_not_pin(self):
        with tree() as t:
            img = t.yaml("release.yaml")["images"]
            lock = "checker=%s\nrunner=%s\ntoolchain=%s\n" % (img["checker"], img["runner"], img["builder"][0])
            t.write("toolchain/toolchain.lock", lock)
            self.assertEqual([f for f in t.lint() if f.rule == "schema"], [])
            t.write("toolchain/toolchain.lock", lock.replace(img["runner"], img["checker"]).replace(
                "toolchain=" + img["builder"][0], "toolchain=" + img["runner"]))
            self.assertEqual(sorted(f.msg for f in t.lint() if f.rule == "schema"), [
                "runner differs from release.yaml's images.runner",
                "toolchain is not one of release.yaml's images.builder"])

    def test_a_project_builder_release_yaml_does_not_pin(self):
        with tree() as t:
            img = t.yaml("release.yaml")["images"]
            y = t.yaml("projects/json/project.yaml")
            self.assertEqual(y["build"]["builder"], img["builder"][0])
            self.assertEqual([f for f in t.lint() if f.rule == "schema"], [])
            y["build"]["builder"] = img["runner"]
            t.put_yaml("projects/json/project.yaml", y)
            found = [f for f in t.lint() if f.rule == "schema"]
            self.assertEqual([(f.where, f.msg) for f in found], [
                ("projects/json/project.yaml", "build.builder is not one of release.yaml's images.builder")])

    def test_counts_that_disagree_with_the_tree(self):
        with tree() as t:
            y = t.yaml("release.yaml")
            y["counts"]["binaries"] += 1
            t.put_yaml("release.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_witness_names_one_of_the_statements_builds(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["ubsan_halts_may_fail"]["witness"]["build"] = "plain"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("does not name" in f.msg for f in t.lint()))


class PrivateData(unittest.TestCase):
    def check(self, text, path="notes/zlib.md"):
        with tree() as t:
            t.write(path, text, "a")
            return [f for f in t.lint() if f.rule == "private-data"]

    def test_a_host_path(self):
        self.assertEqual(len(self.check("see /" + "data/someone/x\n")), 1)

    def test_a_private_address(self):
        self.assertEqual(len(self.check("host " + ".".join(["10", "1", "2", "3"]) + "\n")), 1)

    def test_an_email_address(self):
        self.assertEqual(len(self.check("mail someone" + "@" + "example.com\n")), 1)

    def test_an_address_shape_inside_a_proof_string_is_payload(self):
        at = "x" + "@" + "y.zz"
        lib = "proofs/zlib/checksum_fuzzer/lib/Table.v"
        self.assertEqual(self.check('Definition t : PrimString.string := "#$%s#$".\n' % at, lib), [])
        self.assertEqual(len(self.check("(* mail %s *)\nDefinition t := 0.\n" % at, lib)), 1)
        self.assertEqual(len(self.check('Definition t := "/' + 'data/someone/x".\n', lib)), 1)

    def test_a_private_key(self):
        self.assertEqual(len(self.check("-----BEGIN RSA " + "PRIVATE KEY-----\n")), 1)

    def test_an_access_token(self):
        self.assertEqual(len(self.check("ghp" + "_" + "A" * 36 + "\n")), 1)

    def test_a_pinned_copy_is_verbatim_only_while_its_bytes_are_the_pinned_ones(self):
        path = "LICENSES/anthropic-proofs-NOTICE"
        text = "Contact someone" + "@" + "example.com; see https://example.org/x\n"
        pin = {path: hashlib.sha256(text.encode()).hexdigest()}
        with mock.patch.dict(lint.PINNED_VERBATIM, pin), tree() as t:
            t.write(path, text)
            self.assertEqual([str(f) for f in t.lint() if f.rule in ("private-data", "links")], [])
            t.write(path, text.replace("x\n", "y\n"))
            self.assertEqual(sorted(f.rule for f in t.lint() if f.rule in ("private-data", "links")),
                             ["links", "private-data"])

    def test_container_home_is_not_a_host(self):
        self.assertEqual(self.check("WORKDIR /home/opam\n"), [])

    def test_upstream_copies_keep_their_authors_addresses(self):
        mail = "/* by someone" + "@" + "example.com */\n"
        self.assertEqual(self.check(mail, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"), [])
        self.assertTrue(lint.verbatim("projects/zlib/checksum_fuzzer/source/x.c"))
        self.assertFalse(lint.verbatim("projects/zlib/api-driver/source/driver.c"))

    def test_an_exception_clears_one_finding_in_an_upstream_copy(self):
        with tree() as t:
            rel = "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"
            t.write(rel, "/* built in /" + "home/someone/zlib */\n", "a")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual(len(found), 1)
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual(t.lint(), [])

    def test_an_unused_exception(self):
        with tree() as t:
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": "notes/zlib.md", "rule": "private-data", "key": "0" * 16, "count": 1,
                                "reason": "stale"}]})
            self.assertTrue(any("not used" in f.msg for f in t.lint()))


class Links(unittest.TestCase):
    def test_a_link_to_a_private_repository(self):
        with tree() as t:
            t.write("notes/zlib.md", "See https://github.com/" + "theorem-labs/some-private-repository.\n", "a")
            self.assertEqual(rules_of(t.lint()), ["links"])

    def test_a_link_to_a_public_repository(self):
        with tree() as t:
            t.write("notes/zlib.md", "Enroll at https://github.com/" + "theorem-labs/oss-verify.\n", "a")
            self.assertEqual(rules_of(t.lint()), [])

    def test_an_unknown_link_in_rendered_text(self):
        with tree() as t:
            t.write("notes/zlib.md", "See https://example.org/x and http://www.zlib.net/.\n", "a")
            self.assertEqual(len([f for f in t.lint() if f.rule == "links"]), 2)

    def test_a_link_shape_inside_a_proof_string_is_payload(self):
        lib = "proofs/zlib/checksum_fuzzer/lib/Replay.v"
        def links(text):
            with tree() as t:
                t.write(lib, text, "a")
                return [f for f in t.lint() if f.rule == "links"]
        self.assertEqual(links('Definition t : PrimString.string := "#x://%Q~z#".\n'), [])
        self.assertEqual(len(links("(* see https://example.org/x *)\nDefinition t := 0.\n")), 1)

    def test_links_the_facts_record_are_allowed(self):
        with tree() as t:
            t.write("notes/zlib.md", "See https://github.com/madler/zlib/blob/master/README.\n", "a")
            self.assertEqual(t.lint(), [])

    def test_only_the_debian_snapshot_archive_may_be_read_over_http(self):
        with tree() as t:
            t.write("notes/zlib.md", "From http://snapshot.debian.org/archive/debian/20261001T000000Z and "
                    "https://snapshot.debian.org/file/0123, not http://deb.debian.org/debian.\n", "a")
            found = [f for f in t.lint() if f.rule == "links"]
            self.assertEqual([f.msg.rsplit(" ", 1)[-1] for f in found], ["http://deb.debian.org/debian."])


class FreeText(unittest.TestCase):
    def test_text_with_no_place_in_the_rendering(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y["reason_args"]["text"] = "a note that no sentence uses"
            t.put_yaml("projects/imagemagick/project.yaml", y)
            self.assertIn("free-text", rules_of(t.lint()))


class Proofs(unittest.TestCase):
    def proof(self, body, **extra):
        with tree() as t:
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", dict({
                "schema": "oss-fuzz-theorems/proof/1", "proves": "zlib/checksum_fuzzer/plain_halts",
                "fingerprint": next(s for s in facts.load(t.root).statements()
                                    if s.id == "zlib/checksum_fuzzer/plain_halts").fingerprint}, **extra))
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", body)
            t.generate()
            return [f for f in t.lint() if f.rule == "proofs" or "proof.yaml" in str(f)]

    def test_a_proof_names_no_author(self):
        found = self.proof("Theorem plain_halts_holds : True. Proof. exact I. Qed.\n", authors=["A. Person"])
        self.assertTrue(any("unknown key 'authors'" in str(f) for f in found), found)

    def test_admitted(self):
        self.assertEqual(len(self.proof("Theorem plain_halts_holds : True.\nProof. Admitted.\n")), 1)

    def test_an_axiom(self):
        self.assertEqual(len(self.proof("Axiom cheat : False.\n")), 1)

    def test_primitive_projections_are_fine(self):
        self.assertEqual(self.proof("Set Primitive Projections.\n"), [])
        self.assertEqual(len(self.proof("Primitive cheat : False := #int63_add.\n")), 1)

    def test_comments_and_strings_do_not_count(self):
        self.assertEqual(self.proof('(* not (* Admitted *) here *)\nDefinition s := "Axiom".\n'), [])

    def test_load_and_cd_are_commands_only_where_a_sentence_starts(self):
        names = ("Lemma l : forall i, i = Load 2 \\/ i <> Load 2.\n"
                 "Proof.\n  intros [ | x ]; destruct (Some (Load 2)) as [C2 Cd];\n  | Load _ => auto\n"
                 "  end.\nQed.\n")
        self.assertEqual(self.proof(names), [])
        refused = self.proof('Load "cheat".\nLemma l : True.\nProof. Cd "/tmp".\n  exact I.\nQed.\n')
        self.assertEqual(sorted((str(f).split(": ")[0].rsplit(":", 1)[-1], "'Load'" in str(f)) for f in refused),
                         [("1", True), ("3", False)])

    def test_wall_clock_timeouts(self):
        refused = self.proof("Set Default Timeout 60.\nLemma l : True.\nProof. timeout 5 exact I.\nQed.\n"
                             "Timeout 10 Check I.\nLemma m : True.\nProof. idtac; timeout 5 exact I.\nQed.\n"
                             "Lemma k : True.\nProof. first [ exact I | timeout 5 exact I ].\nQed.\n"
                             "Lemma j : True.\nProof. try idtac; timeout 5 exact I.\nQed.\n")
        self.assertEqual(sorted(int(str(f).split(": ")[0].rsplit(":", 1)[-1]) for f in refused), [1, 3, 5, 7, 10, 13])

    def test_a_caught_timeout_and_a_commented_one_are_fine(self):
        self.assertEqual(self.proof("(* Set Default Timeout 60. timeout 5 *)\n"
                                    "Lemma l : True.\nProof. first [ timeout 5 exact I | exact I ].\nQed.\n"
                                    "Lemma m : True.\nProof. try (timeout 5 fail). exact I.\nQed.\n"
                                    "Lemma k : True.\nProof. solve [ timeout 5 exact I | exact I ].\nQed.\n"
                                    "Lemma j : True.\nProof. repeat (timeout 5 fail). exact I.\nQed.\n"), [])

    def test_the_timeout_exemption_is_one_definition_in_its_file(self):
        body = "Ltac hot2_mid := timeout 8 lia.\nLtac other := timeout 8 lia.\n"
        found = lint.scan_proof(body, "proofs/varnish/esi_parse_fuzzer/lib/D_Dir.v")
        self.assertEqual([str(f).split(": ")[0].rsplit(":", 1)[-1] for f in found], ["2"])
        self.assertEqual(len(lint.scan_proof(body, "proofs/varnish/esi_parse_fuzzer/lib/Other.v")), 2)


class ProofHarnessDirs(unittest.TestCase):
    """proofs/<p>/<h>/lib/ (the harness's proof library) and proofs/<p>/<h>/provenance/ (its build record)."""

    def tree_with(self, files):
        t = Tree()
        self.addCleanup(t.close)
        for rel, text in files.items():
            t.write(rel, text)
        t.generate()
        return t

    LIB = {"proofs/zlib/checksum_fuzzer/lib/Base.v": "Definition one := 1.\n",
           "proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v": "Definition two := 2.\n"}
    PROVENANCE = {"proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml": "schema: x\n",
                  "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md": "# Build record\n",
                  "proofs/zlib/checksum_fuzzer/provenance/recipe/targets/checksum_fuzzer/build.sh": "make\n",
                  "proofs/zlib/checksum_fuzzer/provenance/LICENSES/zlib-LICENSE": "zlib licence\n"}

    def test_a_library_and_a_build_record_are_allowed_and_are_not_proof_directories(self):
        t = self.tree_with(dict(self.LIB, **self.PROVENANCE))
        self.assertEqual([str(f) for f in t.lint()], [])
        loaded = facts.load(t.root)
        self.assertEqual(loaded.errors, [])
        self.assertEqual(loaded.proof_libs, ["zlib/checksum_fuzzer"])
        self.assertEqual(loaded.proofs, {})

    def test_another_file_in_the_build_record(self):
        t = self.tree_with(dict(self.PROVENANCE, **{"proofs/zlib/checksum_fuzzer/provenance/notes.txt": "x\n"}))
        self.assertTrue(any(f.rule == "paths" and "provenance/notes.txt" in str(f) for f in t.lint()))

    def test_a_library_is_held_to_the_proofs_rule(self):
        t = self.tree_with({"proofs/zlib/checksum_fuzzer/lib/Sub/Cheat.v": "Lemma x : False.\nProof. Admitted.\n"})
        found = [f for f in t.lint() if f.rule == "proofs"]
        self.assertEqual(len(found), 1)
        self.assertIn("lib/Sub/Cheat.v", str(found[0]))

    def test_a_shared_library_is_allowed_and_not_a_project_or_proof_directory(self):
        t = self.tree_with({"proofs/lib/Sub/Deep.v": "Definition two := 2.\n"})
        self.assertEqual([str(f) for f in t.lint(changed=["proofs/lib/Sub/Deep.v", "proofs/lib/dune"],
                                               pr_kind="contributor")], [])
        loaded = facts.load(t.root)
        self.assertEqual(loaded.errors, [])
        self.assertTrue(loaded.shared_proof_lib)
        self.assertNotIn("lib", loaded.projects)
        self.assertEqual(loaded.proof_libs, [])
        self.assertEqual(loaded.proofs, {})

    def test_a_shared_library_is_held_to_the_proofs_rule(self):
        t = self.tree_with({"proofs/lib/Sub/Cheat.v": "Lemma x : False.\nProof. Admitted.\n"})
        found = [f for f in t.lint() if f.rule == "proofs"]
        self.assertEqual(len(found), 1)
        self.assertIn("proofs/lib/Sub/Cheat.v", str(found[0]))

    def test_licence_texts_and_recipe_are_verbatim_but_the_record_is_not(self):
        t = self.tree_with(dict(self.PROVENANCE, **{
            "proofs/zlib/checksum_fuzzer/provenance/LICENSES/zlib-LICENSE": "See http://www.apache.org/licenses/\n",
            "proofs/zlib/checksum_fuzzer/provenance/recipe/targets/x/pin": "git https://example.org/x.git\n",
            "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md": "Built at https://github.com/" + "theorem-labs/internal\n"}))
        links = [str(f) for f in t.lint() if f.rule == "links"]
        self.assertEqual(len(links), 1, links)
        self.assertIn("provenance/PROVENANCE.md", links[0])


class Withheld(unittest.TestCase):
    def test_a_patch_has_no_disclosure_field(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            y["patches"].append({"id": "some-fix", "upstream": "reported", "disclosure": "withheld"})
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_withheld_items_without_the_project_saying_so(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            del y["withheld"]
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertIn("withheld", rules_of(t.lint()))

    def test_a_withheld_reason_with_nothing_withheld(self):
        with tree() as t:
            y = t.yaml("projects/json/project.yaml")
            y["withheld"] = {"unpublished": True}
            t.put_yaml("projects/json/project.yaml", y)
            self.assertTrue(any("nothing is withheld for that reason" in f.msg for f in t.lint()))

    def test_evidence_for_a_withheld_statement(self):
        with tree() as t:
            y = t.yaml("projects/json/fuzzer-parse_bjdata/harness.yaml")
            y["statements"]["plain_halts"]["status"] = "withheld"
            y["statements"]["plain_halts"]["withheld"] = "not-yet-published"
            t.put_yaml("projects/json/fuzzer-parse_bjdata/harness.yaml", y)
            self.assertTrue(any("cannot carry" in f.msg for f in t.lint()))

    def test_a_withheld_build_shows_no_detail(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["builds"]["asan"]["withheld"] = "not-yet-published"
            for s in ("asan_halts", "asan_agrees", "asan_disagrees_at_most", "asan_agreement_decidable"):
                y["statements"][s] = dict(y["statements"][s], status="withheld", withheld="not-yet-published")
                y["statements"][s].pop("binds_checks", None)
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("is withheld but shows bytes, sha256, segments" in f.msg for f in t.lint()))
            for k in ("bytes", "sha256", "segments"):
                del y["builds"]["asan"][k]
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= 1
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # Characterise.v, for the asan pair only, is now stale
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("| asan | `checksum_fuzzer.asan` | withheld: not in this release yet | |", page)
            self.assertNotIn(facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"].data["builds"]["plain"]
                             ["file"] + "` | withheld", page)

    def test_a_withheld_statement_has_no_fingerprint(self):
        with tree() as t:
            st = {s.id: s for s in facts.load(t.root).statements()}
            self.assertIsNone(st["zlib/api-driver/asan_ubsan_agrees"].fingerprint)
            self.assertIsNotNone(st["zlib/api-driver/asan_agrees"].fingerprint)
            self.assertIn("zlib/api-driver/asan_ubsan_agrees\tagreement\tplain,asan-ubsan\tmay-fail\t-\twithheld\t"
                          "not-yet-published\t1\t-\t-", t.read("index/statements.tsv"))

    def test_a_gpl_binary_without_its_source(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["licence"] = "GPL-2.0-only AND MIT"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            p = t.yaml("projects/zlib/project.yaml")
            del p["assets"]["src"], p["assets"]["src_manifest"]
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("source bundle" in f.msg for f in t.lint()))

    def test_the_source_is_three_files(self):
        """assets.src goes with assets.src_manifest and the release's recipe, each named for what it is; the fixture
        has all three (the control: it lints clean)."""
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])
            p = t.yaml("projects/zlib/project.yaml")
            man = p["assets"].pop("src_manifest")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.src and assets.src_manifest go together" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = dict(man, file="other-src.MANIFEST.tsv")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.src_manifest.file must be zlib-src.MANIFEST.tsv" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = dict(man, release="v2026.12.0")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("different releases" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = man
            t.put_yaml("projects/zlib/project.yaml", p)
            r = t.yaml("release.yaml")
            del r["recipe"]
            t.put_yaml("release.yaml", r)
            self.assertTrue(any("ships with the release's build recipe" in f.msg for f in t.lint()))

    def test_the_source_assets_and_the_recipe_in_a_second_release(self):
        """A GitHub release holds at most 1,000 files, so the source assets and the recipe may be attached to
        v<release>-src: a source asset and the recipe are in one release, and a binary archive is never in a source
        release (the control: the fixture, everything in v2026.11.0, lints clean)."""
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])
            p = t.yaml("projects/zlib/project.yaml")
            for k in ("src", "src_manifest"):
                p["assets"][k]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.src is attached to v2026.11.0-src and release.yaml's recipe to v2026.11.0: "
                                "a source asset ships with the recipe, in one release" in f.msg for f in t.lint()))
            r = t.yaml("release.yaml")
            r["recipe"]["release"] = "v2026.11.0-src"
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            self.assertIn("Corresponding source, in release [v2026.11.0-src](", page)
            self.assertIn("/releases/tag/v2026.11.0-src)", page)
            p["assets"]["bin"]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.bin is attached to v2026.11.0-src, a release of source assets" in f.msg
                                for f in t.lint()))
            p["assets"]["bin"]["release"] = "v2026.11.0-sources"
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_copyleft_library_withholds_every_binary(self):
        """A GPL or LGPL library makes every binary copyleft, whatever the
        binary's own expression says; with no source bundle every build and
        statement is withheld, and the project says why."""
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            p["library"]["licence"] = "LGPL-2.1-or-later"
            del p["assets"]["src"], p["assets"]["src_manifest"]
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("source bundle" in f.msg for f in t.lint()))
            del p["assets"]
            p["withheld"] = {"source_bundle": True}
            t.put_yaml("projects/zlib/project.yaml", p)
            n = 0
            for h in ("checksum_fuzzer", "api-driver"):
                y = t.yaml("projects/zlib/%s/harness.yaml" % h)
                for b in y["builds"].values():
                    b["withheld"] = "source-bundle"
                    for k in ("bytes", "sha256", "segments"):
                        del b[k]
                    n += 1
                for s in y["statements"].values():
                    for k in ("witness", "binds_checks"):
                        s.pop(k, None)
                    s["status"], s["withheld"] = "withheld", "source-bundle"
                t.put_yaml("projects/zlib/%s/harness.yaml" % h, y)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= n
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # the statement files it rendered before are now stale
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertIn("under a copyleft licence", t.read("projects/zlib/README.md"))
            self.assertIn("No binaries are attached", t.read("projects/zlib/README.md"))
            self.assertIn("withheld: waits for its source bundle", t.read("projects/zlib/checksum_fuzzer/README.md"))

    def test_withheld_must_say_why(self):
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            p["withheld"] = {}
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("names no reason" in f.msg for f in t.lint()))


class Pending(unittest.TestCase):
    def test_a_pending_source_lists_no_files_and_anchors_no_checks(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["source"]["pending"] = True
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            msgs = [f.msg for f in t.lint()]
            self.assertTrue(any("lists no files" in m for m in msgs))
            y["source"]["files"] = []
            y["checks"] = []
            for s in y["statements"].values():
                s.pop("binds_checks", None)
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            os.unlink(t.path("projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertIn("source not in this release yet", t.read("projects/zlib/checksum_fuzzer/README.md"))


class Placeholders(unittest.TestCase):
    def test_a_placeholder_digest_blocks_only_a_release(self):
        with tree() as t:
            r = t.yaml("release.yaml")
            r["images"]["checker"] = r["images"]["checker"].split("@")[0] + "@sha256:" + "0" * 64
            t.put_yaml("release.yaml", r)
            self.assertEqual([str(f) for f in t.lint()], [])
            found = t.lint(release=True)
            self.assertEqual([(f.rule, f.where.split(":")[0]) for f in found], [("schema", "release.yaml")])
            self.assertTrue(found[0].msg.startswith("checker is a placeholder"), found[0].msg)

    def test_each_placeholder_is_its_own_finding(self):
        """Replacing one placeholder clears its finding and no other: a file is
        not reported once for however many placeholders it holds."""
        with tree() as t:
            r = t.yaml("release.yaml")
            r["images"]["runner"] = r["images"]["runner"].split("@")[0] + "@sha256:" + "0" * 64
            r["semantics"]["commit"] = "0" * 40
            t.put_yaml("release.yaml", r)
            found = t.lint(release=True)
            self.assertEqual(sorted(f.msg.split(" ")[0] for f in found), ["commit", "runner"])
            self.assertEqual({f.where.split(":")[0] for f in found}, {"release.yaml"})
            r["images"]["runner"] = t.yaml("release.yaml")["images"]["checker"]
            t.put_yaml("release.yaml", r)
            self.assertEqual([f.msg.split(" ")[0] for f in t.lint(release=True)], ["commit"])


class DistributionBodies(unittest.TestCase):
    """The two definition forms the rendered distributions use besides a plain
    byte list: an alphabet under List.nodup, and a long header in chunks."""

    def test_an_alphabet_under_nodup(self):
        from oft import rules
        body = ("Definition alpha : list byte :=\n  List.nodup (fun x y => decide (x = y))\n"
                "    [ Z_to_bv 8 48; Z_to_bv 8 49 ].\n")
        self.assertEqual(rules._bytes_def(body, "alpha"), b"01")

    def test_a_header_in_chunks(self):
        from oft import rules
        body = ("Definition hdr_000 : list byte :=\n  [ Z_to_bv 8 1; Z_to_bv 8 2 ].\n"
                "Definition hdr_001 : list byte :=\n  [ Z_to_bv 8 3 ].\n"
                "Definition hdr : list byte :=\n  ((hdr_000 ++ hdr_001))%list.\n")
        self.assertEqual(rules._bytes_def(body, "hdr"), b"\x01\x02\x03")
        self.assertIsNone(rules._bytes_def(body.replace("hdr_001 :", "other :"), "hdr"))



class Uninstrumented(unittest.TestCase):
    """builds.<b>.uninstrumented: what a build links that no sanitizer instruments."""
    H = "projects/zlib/checksum_fuzzer/harness.yaml"
    LIST = [{"name": "libc.a", "kind": "libc", "sha256": "a" * 64},
            {"name": "crc32_x86.S.o", "kind": "assembly", "source": "contrib/crc32_x86.S"}]

    def _with(self, t, build, items):
        y = t.yaml(self.H)
        y["builds"][build]["uninstrumented"] = items
        t.put_yaml(self.H, y)

    def test_a_list_on_a_published_build_is_clean(self):
        with tree() as t:
            self._with(t, "asan", self.LIST)
            self.assertEqual(t.generate(), 0)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_an_unknown_kind_or_an_empty_list(self):
        with tree() as t:
            self._with(t, "asan", [{"name": "x.a", "kind": "mystery"}])
            self.assertIn("schema", rules_of(t.lint()))
        with tree() as t:
            self._with(t, "asan", [])
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_member_without_its_source(self):
        with tree() as t:
            self._with(t, "asan", [{"name": "crc32_x86.S.o", "kind": "assembly"}])
            self.assertTrue(any("names its source file" in f.msg for f in t.lint()))

    def test_twice(self):
        with tree() as t:
            self._with(t, "asan", [self.LIST[0], self.LIST[0]])
            self.assertTrue(any("listed twice" in f.msg for f in t.lint()))

    def test_a_withheld_build_shows_no_list(self):
        with tree() as t:
            self._with(t, "asan", self.LIST)
            y = t.yaml(self.H)
            rec = y["builds"]["asan"]
            rec["withheld"] = "not-yet-published"
            for k in ("bytes", "sha256", "segments"):
                rec.pop(k, None)
            t.put_yaml(self.H, y)
            self.assertTrue(any("no uninstrumented list" in f.msg for f in t.lint()))


class CopyleftSources(unittest.TestCase):
    """A binary bound by a GPL-family licence takes the release-wide toolchain source, and the source of every
    library it links from the build image (release.yaml sources and image_libraries)."""
    H = "projects/zlib/checksum_fuzzer/harness.yaml"

    def test_an_or_choice_does_not_bind(self):
        cases = {"GPL-2.0-only": True, "LGPL-2.1-or-later AND MIT": True, "BSD-3-Clause OR GPL-2.0-only": False,
                 "(BSD-3-Clause OR GPL-2.0-only) AND MIT": False, "GPL-2.0-only WITH Linux-syscall-note": True,
                 "(GPL-2.0-or-later OR LGPL-3.0-or-later) AND BSD-3-Clause": True, "Zlib": False, "NOASSERTION": False}
        for expr, binds in cases.items():
            self.assertEqual(facts.gpl_binds(expr), binds, expr)

    def _link(self, t, copyleft, in_sysroot_src=True, listed=True):
        y = t.yaml(self.H)
        for b in y["builds"].values():
            b["uninstrumented"] = [{"name": "libgmp.a", "kind": "image-library"}]
        t.put_yaml(self.H, y)
        r = t.yaml("release.yaml")
        r["sources"] = {"release": "sources-v1",
                        "toolchain": {"file": "toolchain-src.tar.zst", "bytes": 1, "sha256": "0" * 64},
                        "sysroot": {"file": "sysroot-src.tar.zst", "bytes": 1, "sha256": "0" * 64}}
        if listed:
            r["image_libraries"] = {"libgmp.a": {"library": "GMP", "licence": "LGPL-3.0-or-later OR GPL-2.0-or-later",
                                                 "copyleft": copyleft, "in_sysroot_src": in_sysroot_src}}
        t.put_yaml("release.yaml", r)

    def test_a_copyleft_library_from_the_image_names_both_archives(self):
        with tree() as t:
            self._link(t, copyleft=True)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            self.assertIn("The binaries of `checksum_fuzzer` are under a GPL-family licence", page)
            self.assertIn("`toolchain-src.tar.zst`", page)
            self.assertIn("`sysroot-src.tar.zst`", page)
            self.assertIn("/releases/tag/sources-v1", page)

    def test_a_permissive_library_from_the_image_names_neither(self):
        with tree() as t:
            self._link(t, copyleft=False)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertNotIn("toolchain-src.tar.zst", t.read("projects/zlib/README.md"))

    def test_a_copyleft_binary_waits_for_its_libraries_source(self):
        with tree() as t:
            self._link(t, copyleft=True, in_sysroot_src=False)
            self.assertTrue(any("whose source sources.sysroot does not hold" in f.msg for f in t.lint()))

    def test_every_library_from_the_image_is_listed(self):
        with tree() as t:
            self._link(t, copyleft=True, listed=False)
            self.assertTrue(any("image_libraries does not list" in f.msg for f in t.lint()))


if __name__ == "__main__":
    unittest.main()
