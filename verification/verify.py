#!/usr/bin/env python3
"""Check the moved source inventory, full public signatures and Lean axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

from lean_source import code_only, declarations

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def records(output):
    """The greedy name match preserves Lean identifiers ending in primes."""
    result = []
    start = 0
    pattern = r"^'([^\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
    for match in re.finditer(pattern, output, re.MULTILINE):
        signature = " ".join(output[start:match.start()].split())
        axioms = []
        for raw in (match[2] or "").split(","):
            raw = raw.strip()
            if raw:
                axioms.append(raw.split(".{", 1)[0])
        check(set(axioms) <= ALLOWED,
              "Unapproved axioms for " + match[1] + ": " + str(axioms))
        result.append({"name": match[1], "signature": signature, "axioms": sorted(axioms)})
        start = match.end()
    check(not output[start:].strip(), "Unparsed compiler output: " + output[start:start+500])
    return result


def main():
    manifest = json.loads((ROOT / "SOURCE-MANIFEST.json").read_text())
    inventory = json.loads((HERE / "public-declarations.json").read_text())
    modules = manifest["modules"]
    names = []
    for item in modules:
        path = ROOT / item["target_path"]
        source = path.read_text()
        check(hashlib.sha256(source.encode()).hexdigest() == item.get("module_sha256", item["extracted_sha256"]),
              "Source fingerprint changed: " + str(path.relative_to(ROOT)))
        names.extend(x["name"] for x in declarations(source))
        masked = code_only(source)
        for line in masked.splitlines():
            match = re.match(r"^(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(.+)", line)
            if match:
                check(all(x.startswith(("HilbertMathlib.", "Mathlib", "Lean", "Init"))
                          for x in match[1].split()),
                      "Paper dependency in shared foundation: " + line)
        check(not re.search(r"\b(?:sorry|admit|axiom)\b", masked),
              "Placeholder or custom axiom in " + str(path))
    check(names == [x["name"] for x in inventory], "Public source inventory changed")
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    commands = ["import " + x["target_module"] for x in modules]
    commands += ["set_option pp.universes true", "set_option pp.fullNames true",
                 "set_option pp.notation false", "set_option format.width 160"]
    for item in inventory:
        commands += ["#check @" + item["name"], "#print axioms " + item["name"]]
    audit = scratch / "PublicSignatures.lean"
    audit.write_text("\n".join(commands) + "\n")
    run = subprocess.run(["lake", "env", "lean", str(audit)], cwd=ROOT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (scratch / "public-signatures.txt").write_text(run.stdout)
    check(run.returncode == 0, "Lean audit failed; see .scratch/public-signatures.txt")
    actual = records(run.stdout)
    expected = records((HERE / "original-signatures.txt").read_text())
    check(len(actual) == len(inventory), "Missing declaration audit records")
    for before, after in zip(expected, actual):
        check(before == after, "Signature or axiom mismatch: " + before["name"])
    check(len(expected) == len(actual), "Signature inventory length changed")
    result = {"status": "PASS", "modules": len(modules), "declarations": len(actual),
              "allowed_axioms": sorted(ALLOWED),
              "check": "Source fingerprints, unchanged full signatures, exact axiom inventories"}
    (scratch / "verification-status.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
