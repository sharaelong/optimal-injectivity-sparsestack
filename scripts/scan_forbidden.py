#!/usr/bin/env python3
"""Static anti-cheating scan for a Lean campaign (G1, part 1).

Usage:
  scan_forbidden.py --root <project_root> --lib <LibName> [--spec <LibName>/Spec.lean]
                    [--allow <allowlist.txt>] [--whitelist-sha256 <sha256> ...]

Scans every .lean file under <root>/<LibName>/ (imported or not), after stripping comments and string literals.
Exit status 0 iff there are no FORBIDDEN hits and every RESTRICTED hit is allowlisted.

Allowlist format (one per line, '#' comments): <relative/path.lean>:<token>   e.g. QGap/Foo.lean:notation
Files whose SHA256 is given with --whitelist-sha256 (the gate file) are skipped entirely.
"""
import argparse
import hashlib
import pathlib
import re
import sys

FORBIDDEN = [
    r"\bsorry\b", r"\bsorryAx\b", r"\badmit\b", r"\baxiom\b", r"\bnative_decide\b", r"\+native\b",
    r"\bofReduceBool\b", r"\bofReduceNat\b", r"\btrustCompiler\b", r"\breduceBool\b", r"\breduceNat\b",
    r"\bimplemented_by\b", r"\bextern\b", r"\bunsafe\b", r"\bopaque\b", r"\bpartial\s+def\b",
    r"\bdebug\.", r"\bskipKernelTC\b", r"\ballowUnsafeReducibility\b", r"\bbootstrap\.",
    r"\bmacro\b", r"\bmacro_rules\b", r"\bsyntax\b", r"\belab\b", r"\belab_rules\b",
    r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b", r"\binitialize\b", r"\bbuiltin_initialize\b",
    r"\baddDecl\b", r"\baddAndCompile\b", r"\bmodifyEnv\b", r"\bsetEnv\b", r"\bcsimp\b",
    r"\bLean\.Elab\b", r"\bLean\.Meta\b", r"\bLean\.Kernel\b", r"\bIO\.", r"\bunsafeCast\b",
    # sstack: search tactics are not allowed in delivered files (strict harvester rule)
    r"\bexact\?", r"\bapply\?", r"\brw\?", r"\bsimp\?", r"\bsimp_all\?", r"\baesop\?", r"\bhint\b",
    r"\bsays\b", r"\bpolyrith\b", r"\brw_search\b", r"\bexact\?\%", r"\blibrary_search\b",
]
RESTRICTED = [
    r"\bnotation\b", r"\binfix\b", r"\binfixl\b", r"\binfixr\b", r"\bprefix\b", r"\bpostfix\b",
    r"\bset_option\s+backward\.", r"#exit\b",
]
SPEC_EXTRA = [  # additionally forbidden in Spec.lean
    r"\binstance\b", r"\battribute\b", r"\bset_option\b", r"\bopen\b[^\n]*\bin\b", r"\blocal\b", r"\bscoped\b",
    r"\bnotation\b", r"\binfix\b", r"\binfixl\b", r"\binfixr\b", r"\bprefix\b", r"\bpostfix\b", r"#exit\b",
    r"@\[[^\]]*\b(reducible|irreducible|semireducible|instance_reducible|simp|coe)\b",
]


def strip_comments_and_strings(src: str) -> str:
    """Replace comments and string/char literals by spaces, keeping newlines (so line numbers survive)."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            seg = src[i:j + 1]
            out.append("".join("\n" if ch == "\n" else " " for ch in seg)); i = j + 1; continue
        if c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == "\\" and i + 3 < n and src[i + 3] == "'")):
            j = i + (3 if src[i + 2] == "'" else 4)
            out.append(" " * (j - i)); i = j; continue
        out.append(c); i += 1
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--lib", required=True)
    ap.add_argument("--spec", default=None)
    ap.add_argument("--allow", default=None)
    ap.add_argument("--whitelist-sha256", nargs="*", default=[])
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    allow = set()
    if a.allow and pathlib.Path(a.allow).exists():
        for line in pathlib.Path(a.allow).read_text().splitlines():
            line = line.split("#", 1)[0].strip()
            if line:
                allow.add(line)
    spec = (root / a.spec).resolve() if a.spec else None
    files = sorted((root / a.lib).rglob("*.lean")) + ([root / (a.lib + ".lean")] if (root / (a.lib + ".lean")).exists() else [])
    bad = 0
    restricted_ok = 0
    for f in files:
        raw = f.read_bytes()
        if hashlib.sha256(raw).hexdigest() in a.whitelist_sha256:
            print(f"SKIP (whitelisted by sha256): {f.relative_to(root)}")
            continue
        text = strip_comments_and_strings(raw.decode("utf-8", errors="replace"))
        rel = str(f.relative_to(root))
        lines = text.splitlines()
        pats = [("FORBIDDEN", p) for p in FORBIDDEN] + [("RESTRICTED", p) for p in RESTRICTED]
        if spec is not None and f.resolve() == spec:
            pats += [("FORBIDDEN-IN-SPEC", p) for p in SPEC_EXTRA]
        for ln, line in enumerate(lines, 1):
            for kind, p in pats:
                m = re.search(p, line)
                if not m:
                    continue
                tok = m.group(0).strip()
                if kind == "RESTRICTED" and (f"{rel}:{tok}" in allow or f"{rel}:{tok.split()[0]}" in allow):
                    restricted_ok += 1
                    continue
                bad += 1
                print(f"{kind}: {rel}:{ln}: `{tok}`: {line.strip()[:160]}")
    print(f"SCAN SUMMARY: files={len(files)} violations={bad} allowlisted_restricted={restricted_ok}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
