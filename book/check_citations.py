#!/usr/bin/env python3
"""
Verify that every Lean name the book cites actually exists.

The book has two kinds of backing for a claim:

  * an elaborated ```lean block, which Verso type-checks when the book is
    built, so it cannot be wrong and cannot rot; and
  * a prose theorem citing a declaration in one of the four companion
    libraries, which nothing checks -- a rename in the library leaves a
    dangling citation in the book and no build anywhere fails.

This script closes the second gap. It harvests every declaration name from the
companion libraries and every name the book cites in prose, and reports
citations that resolve to nothing. Run from the book directory.

Exit status is 1 if any citation dangles, so it can gate the build.
"""

import os
import re
import sys
import glob
import collections

ROOT = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.normpath(os.path.join(ROOT, ".."))

LIBS = [
    "proofs/Foundation",
    "proofs/CCHProofs",
    "proofs/HallucinationProofs",
    "ManifoldProofs",
]

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|public\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)",
    re.M,
)

# Names that look like declarations but are not citations into the corpus.
# Kept explicit rather than heuristic, so that adding one is a deliberate act.
IGNORE_EXACT = {
    # Lean 4 core and Mathlib names, cited as prerequisites rather than as
    # results of this development.
    "by_cases", "by_contra", "dist_comm", "dist_triangle", "congr_arg",
    "isPreconnected_univ", "isPreconnected_Icc", "isConnected_sphere",
    "intermediate_value_Icc", "Continuous_comp", "not_not",
    # Module-name prefixes used as shorthand in prose ("as F_04 shows").
    # The full module names are checked separately.
    "F_01", "F_02", "F_03", "F_04", "F_05", "F_06", "F_07", "F_08", "F_09",
    "F_10", "F_11", "F_12", "F_13", "F_14",
    "HoF_01", "HoF_02", "HoF_03", "HoF_04", "HoF_05", "HoF_06", "HoF_07",
    "HoF_08", "HoF_09", "HoF_10", "HoF_11", "HoF_12", "HoF_13", "HoF_14",
    "HoF_15",
    "CCH_01", "CCH_02", "CCH_03", "CCH_04", "CCH_05", "CCH_06", "CCH_07",
    "CCH_08", "CCH_09", "CCH_LLM", "CCH_Master",
    "MoF_02", "MoF_11", "MoF_12", "MoF_19", "MoF_20",
    "MoF_Cost", "MoF_Cost_01", "MoF_Cost_04", "MoF_Cost_07", "MoF_Cost_08",
    "MoF_Cost_10", "MoF_Adv_01", "MoF_Adv_10", "MoF_",
    # In-book prefixes for chapter-local declarations.
    "c0_", "c1_", "c2_", "c3_", "c6_", "c8_", "c9_", "c10_", "c11_",
}

# Names an exercise asks the reader to introduce. These are deliberately not
# declarations anywhere: the exercise is to write them. Each entry names the
# exercise that introduces it, so the list cannot quietly become a dumping
# ground for citations that merely failed to resolve.
TO_BE_DEFINED_BY_READER = {
    "c3_cch_at_most_two",   # Exercise 3.10
    "C3_Faithful",          # Exercise 3.13
}

# Mathematical variables written in code spans: `q_t`, `W_U`, `d_i`. These are
# notation, not identifiers, and are recognised by shape.
VARIABLE = re.compile(r"^[A-Za-z]_(?:[A-Za-z0-9]{1,6}|\{[^}]*\})$")


def library_names():
    """Every declaration name and module name in the companion libraries."""
    decls, mods = set(), set()
    for lib in LIBS:
        base = os.path.join(CORPUS, lib)
        if not os.path.isdir(base):
            print(f"error: companion library not found: {base}", file=sys.stderr)
            sys.exit(2)
        for path in glob.glob(base + "/**/*.lean", recursive=True):
            if "/.lake/" in path:
                continue
            mods.add(os.path.basename(path)[:-5])
            with open(path, encoding="utf-8", errors="ignore") as fh:
                decls.update(DECL.findall(fh.read()))
    return decls, mods


def book_names():
    """Declarations the book itself defines in elaborated lean blocks."""
    names = set()
    for path in glob.glob(os.path.join(ROOT, "TrilemmaBook", "*.lean")):
        with open(path, encoding="utf-8") as fh:
            names.update(DECL.findall(fh.read()))
    return names


def citations():
    """Names cited in book prose, outside fenced code blocks."""
    cited = collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(ROOT, "TrilemmaBook", "Ch*.lean"))):
        chapter = os.path.basename(path)
        in_fence = False
        with open(path, encoding="utf-8") as fh:
            for lineno, line in enumerate(fh.read().split("\n"), 1):
                if line.lstrip().startswith("```"):
                    in_fence = not in_fence
                    continue
                if in_fence:
                    continue
                for span in re.findall(r"`([^`]+)`", line):
                    name = span.strip()
                    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
                        continue
                    if "_" not in name:
                        continue
                    if name in IGNORE_EXACT or name in TO_BE_DEFINED_BY_READER:
                        continue
                    if VARIABLE.match(name):
                        continue
                    cited[name].append(f"{chapter}:{lineno}")
    return cited


# A theorem stated in prose with no proof anywhere must say so, in these words.
# The phrase is deliberately blunt and deliberately the only accepted form, so
# that an unbacked claim cannot be introduced without writing the sentence.
NOT_FORMALIZED = "Not formalized."

THEOREM_HEAD = re.compile(r"^\*{1,2}(Theorem|Lemma|Proposition|Corollary) ")

# Citation-shaped names: dotted and subscripted Lean identifiers both count.
CITE_NAME = re.compile(
    r"^[A-Za-z][A-Za-z0-9_'₀-₉]*"
    r"(?:\.[A-Za-z][A-Za-z0-9_'₀-₉]*)*$"
)


def backing_report():
    """Classify every prose theorem by how it is backed."""
    proved, cited, marked, unbacked = 0, 0, 0, []
    for path in sorted(glob.glob(os.path.join(ROOT, "TrilemmaBook", "Ch*.lean"))):
        chapter = os.path.basename(path)
        lines = open(path, encoding="utf-8").read().split("\n")
        heads = [i for i, l in enumerate(lines) if THEOREM_HEAD.match(l)]
        for j, i in enumerate(heads):
            end = heads[j + 1] if j + 1 < len(heads) else len(lines)
            block = "\n".join(lines[i:min(end, i + 40)])
            if "```lean" in block:
                proved += 1
            elif NOT_FORMALIZED in block:
                marked += 1
            elif any(
                CITE_NAME.match(s) and ("_" in s or "." in s)
                for s in re.findall(r"`([^`]+)`", block)
            ):
                cited += 1
            else:
                unbacked.append(f"{chapter}:{i + 1}  {lines[i].strip()[:70]}")
    return proved, cited, marked, unbacked


def main():
    decls, mods = library_names()
    known = decls | mods | book_names()
    cited = citations()

    dangling = {n: w for n, w in cited.items() if n not in known}
    proved, cited_thms, marked, unbacked = backing_report()
    total = proved + cited_thms + marked + len(unbacked)

    print(f"companion libraries : {len(decls)} declarations, {len(mods)} modules")
    print(f"book declarations   : {len(book_names())} elaborated by Verso")
    print(f"prose citations     : {len(cited)} distinct names")
    print(f"prose theorems      : {total} total")
    print(f"  proved in-book    : {proved}")
    print(f"  cited to a library: {cited_thms}")
    print(f"  marked unformalized: {marked}")
    print(f"  unaccounted       : {len(unbacked)}")

    failed = False

    if unbacked:
        failed = True
        print(
            f"\nerror: {len(unbacked)} theorem(s) have no lean block, no citation, "
            f'and no "{NOT_FORMALIZED}" marker:',
            file=sys.stderr,
        )
        for site in unbacked:
            print(f"  {site}", file=sys.stderr)

    if not dangling:
        if not failed:
            print("\nevery prose theorem is proved, cited, or explicitly marked")
            print("every prose citation resolves to a real declaration")
        return 1 if failed else 0

    print(f"\nerror: {len(dangling)} citation(s) resolve to nothing:", file=sys.stderr)
    for name in sorted(dangling):
        sites = ", ".join(dangling[name][:3])
        print(f"  {name:<44} cited at {sites}", file=sys.stderr)
    print(
        "\n  Either the name is misspelled, or it was renamed in the library,\n"
        "  or the claim has no verified counterpart and should not be citing one.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
