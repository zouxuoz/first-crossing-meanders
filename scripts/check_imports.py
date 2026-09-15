#!/usr/bin/env python3
"""Enforce the Lean layer rules of ARCHITECTURE.md from source imports and imports-only umbrellas.

Run by scripts/policy.sh. Every module under Meanders/ belongs to the layer
named by its first path component; the table below says which layers it may
import from. Two extra rules: a library file never imports an umbrella, and an
algorithm never imports another algorithm.
"""
import re
import subprocess
import sys

LAYERS = ["Core", "Problems", "Models", "Theory", "Algorithms", "Verification", "Certify"]

# layer -> layers it may import from (itself always included)
ALLOWED = {
    "Core": {"Core"},
    "Problems": {"Core", "Problems"},
    "Models": {"Core", "Problems", "Models"},
    "Theory": {"Core", "Problems", "Models", "Theory"},
    "Algorithms": {"Core", "Problems", "Models", "Algorithms"},
    "Verification": {"Core", "Problems", "Verification"},
    "Certify": {"Core", "Problems", "Models", "Theory", "Algorithms", "Verification", "Certify"},
}


def module_of(path):
    return path[:-len(".lean")].replace("/", ".")


def layer_of(module):
    """('Core', 'Meanders.Core.Arch') -> 'Core'; umbrellas and roots -> None."""
    parts = module.split(".")
    if parts[0] != "Meanders" or len(parts) < 3:
        return None
    return parts[1]


def is_umbrella(module):
    parts = module.split(".")
    return parts == ["Meanders"] or (parts[0] == "Meanders" and len(parts) == 2)


def algorithm_of(module):
    parts = module.split(".")
    return parts[2] if len(parts) >= 3 and parts[1] == "Algorithms" else None


def mask_comments_and_strings(source):
    """Keep line boundaries while hiding nested comments and string contents."""
    result = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif depth:
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            result.append('"')
            i += 1
            while i < len(source) and source[i] != '"':
                if source[i] == "\\":
                    result.append("  ")
                    i += 2
                else:
                    result.append("\n" if source[i] == "\n" else " ")
                    i += 1
            result.append('"')
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def check_source(path, source):
    """Check one project file; tests can supply isolated counterexamples."""
    failures = []
    module = module_of(path)
    source = mask_comments_and_strings(source)
    import_line = re.compile(r"^\s*import\s+([\w.']+(?:[ \t]+[\w.']+)*)[ \t]*(?=\n|$)", re.M)
    imports = [name for match in import_line.finditer(source) for name in match.group(1).split()]
    if is_umbrella(module) and import_line.sub("", source).strip():
        failures.append(f"{path}: umbrella contains a command other than import")
    for imp in imports:
        if imp.startswith("MeandersTests") and not module.startswith("MeandersTests"):
            failures.append(f"{path}: imports the test library ({imp})")
        if imp != "Meanders" and not imp.startswith("Meanders."):
            continue
        if module.startswith("MeandersTests") or module in {"Verify", "ExportTheorem"}:
            continue  # tests and the executable may import anything
        if is_umbrella(module):
            # `Meanders` imports umbrellas; a layer umbrella imports its own layer.
            if module == "Meanders":
                if imp not in {f"Meanders.{layer}" for layer in LAYERS}:
                    failures.append(f"{path}: the root umbrella imports a non-umbrella ({imp})")
            elif layer_of(imp) != module.split(".")[1]:
                failures.append(f"{path}: umbrella imports outside its layer ({imp})")
            continue
        if is_umbrella(imp):
            failures.append(f"{path}: library file imports an umbrella ({imp})")
            continue
        src, dst = layer_of(module), layer_of(imp)
        if src not in ALLOWED:
            failures.append(f"{path}: unknown layer {src!r}; add it to ARCHITECTURE.md and this script")
            continue
        if dst not in ALLOWED[src]:
            failures.append(f"{path}: {src} may not import {dst} ({imp})")
        if src == "Algorithms" and dst == "Algorithms" and algorithm_of(module) != algorithm_of(imp):
            failures.append(f"{path}: an algorithm imports another algorithm ({imp})")

    return failures


def main():
    files = subprocess.run(["git", "ls-files", "*.lean"], capture_output=True, text=True,
                           check=True).stdout.splitlines()
    failures = []
    for path in files:
        with open(path, encoding="utf-8") as source:
            failures.extend(check_source(path, source.read()))
    for failure in failures:
        print(f"    FAIL: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
