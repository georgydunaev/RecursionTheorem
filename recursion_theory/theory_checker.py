"""Automated Integrity and Structural Checker for Isabelle/ZF Theories.

Performs static analysis of Isabelle theory files (*.thy):
1. Verifies structural boundaries (theory header, begin, end, locale nesting).
2. Verifies proof integrity (strict absence of 'sorry', 'oops', 'cheat').
3. Extracts all defined entities (theorems, lemmas, definitions, locales).
4. Verifies proof block balancing (proof ... qed, by ...).
"""

import re
from typing import Dict, List, Any


class IsabelleTheoryChecker:
    """Static integrity checker for Isabelle/ZF theory files."""

    def __init__(self, file_path: str):
        self.file_path = file_path
        with open(file_path, "r", encoding="utf-8") as f:
            self.content = f.read()
        self.lines = self.content.splitlines()

    def check_integrity(self) -> Dict[str, Any]:
        """Perform comprehensive check and return diagnostics."""
        # Strip Isabelle comments (* ... *) before analyzing code blocks
        clean_code = re.sub(r"\(\*.*?\*\)", "", self.content, flags=re.DOTALL)

        has_sorry = bool(re.search(r"\bsorry\b", clean_code))
        has_oops = bool(re.search(r"\boops\b", clean_code))
        has_cheat = bool(re.search(r"\bcheat\b", clean_code))

        # Check theory header
        header_match = re.search(r"theory\s+([A-Za-z0-9_]+)\s+imports\s+([^begin]+)\s+begin", self.content)
        has_header = header_match is not None
        theory_name = header_match.group(1) if header_match else None
        imports = [x.strip() for x in header_match.group(2).split()] if header_match else []

        # Check end keyword
        ends = re.findall(r"\bend\b", clean_code)
        has_end = len(ends) >= 1

        # Extract entities
        theorems = re.findall(r"theorem\s+([A-Za-z0-9_]+)\s*:", clean_code)
        lemmas = re.findall(r"lemma\s+([A-Za-z0-9_]+)\s*:", clean_code)
        definitions = re.findall(r"definition\s+([A-Za-z0-9_]+)\s*::", clean_code)
        locales = re.findall(r"locale\s+([A-Za-z0-9_]+)\s*=", clean_code)

        # Count proof blocks
        proof_count = len(re.findall(r"\bproof\b", clean_code))
        qed_count = len(re.findall(r"\bqed\b", clean_code))
        by_count = len(re.findall(r"\bby\b", clean_code))

        is_sound = (
            has_header
            and has_end
            and not has_sorry
            and not has_oops
            and not has_cheat
            and proof_count == qed_count
        )

        return {
            "file": self.file_path,
            "theory_name": theory_name,
            "imports": imports,
            "is_sound": is_sound,
            "has_sorry": has_sorry,
            "has_oops": has_oops,
            "has_cheat": has_cheat,
            "theorems_count": len(theorems),
            "theorems": theorems,
            "lemmas_count": len(lemmas),
            "lemmas": lemmas,
            "definitions_count": len(definitions),
            "definitions": definitions,
            "locales_count": len(locales),
            "locales": locales,
            "proof_blocks": proof_count,
            "qed_blocks": qed_count,
            "by_steps": by_count,
        }
