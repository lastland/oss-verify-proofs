"""Public names: Rocq identifiers, statement names, file names.

Every name is computed from typed fields; nothing parses an old name to
recover a fact.  `ident` must be injective over each population it is used
on (projects; the harnesses of one project), which `oft lint` checks.
"""
import re

ROOT = "OssFuzzTheorems"
SHARED_PROOF_THEORY = ROOT + ".Proofs.Shared"
SHARED_PROOF_PACKAGE = "rocq-oss-fuzz-theorems-proofs-shared"
RESERVED_HARNESS_NAMES = {"images", "source", "bin", "proofs"}   # plus api-driver for OSS-Fuzz targets
API_DRIVER = "api-driver"

BUILD_IDENT = {"plain": "plain", "ubsan": "ubsan", "asan": "asan", "asan-ubsan": "asan_ubsan"}
BUILD_MODULE = {"plain": "Plain", "ubsan": "Ubsan", "asan": "Asan", "asan-ubsan": "AsanUbsan"}
BUILD_WORDS = {"plain": "plain", "ubsan": "UBSan", "asan": "ASan", "asan-ubsan": "ASan+UBSan"}


def ident(name):
    """A Rocq identifier for an OSS-Fuzz project or harness name."""
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if s[:1].isdigit():
        s = "h_" + s
    return s


def rocq_harness(project, harness):
    return "%s.%s.%s" % (ROOT, ident(project), ident(harness))


def rocq_proof(project, harness, statement):
    return "%s.Proofs.%s.%s.%s" % (ROOT, ident(project), ident(harness), statement)


def opam_package(project):
    return "rocq-oss-fuzz-theorems-%s" % project


def build_file(harness, build):
    return "%s.%s" % (harness, build)


def statement_name(kind, builds, reading):
    """The one name a statement with these fields may have."""
    san = BUILD_IDENT[builds[-1]]
    if kind == "halts":
        return san + ("_halts_may_fail" if reading == "may-fail" else "_halts")
    if kind == "agreement":
        return san + "_agrees"
    if kind == "bound":
        return san + "_disagrees_at_most"
    if kind == "decidability":
        return san + "_agreement_decidable"
    raise ValueError(kind)


def statement_id(project, harness, statement):
    return "%s/%s/%s" % (project, harness, statement)
