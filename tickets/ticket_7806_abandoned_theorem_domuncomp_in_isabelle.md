# [RECURSIONTHEOREM] Ticket 7806 -- Abandoned Theorem domuncomp in Isabelle Theory

**Repository:** `RecursionTheorem`
**Status:** `RESOLVED`
**Created:** `2026-11-13T21:55:00Z`
**Resolved:** `2026-11-13T22:47:00Z`
**Auditor:** Epistemic Hallucination Auditor

## Hallucination Overview
- **Location:** `/botworkspace/RecursionTheorem/Recursion-Addition/recursion.thy`, lines 514-530.
- **Hallucination Type:** Proof Hallucination.

## Verifiable Evidence
In `recursion.thy`:
```isabelle
theorem domuncomp: "f \in S \Longrightarrow domain(f) \subseteq domain(\Union S)"
  apply (rule subsetI)
  apply (simp add: domain_def)
  oops
```
The proof of `domuncomp` was previously abandoned using Isabelle's `oops` keyword. In Isabelle/ZF, `oops` drops the proof obligation without registering the theorem as valid, leaving the result incomplete while presenting it as part of the formalization.

## Sound Correction
Completed the proof of `domuncomp` from first principles in Isabelle/ZF using `domainE`, `UnionI`, and `domainI`, closing with `qed`:
```isabelle
theorem domuncomp: 
  assumes W:\<open>f\<in>S\<close>
  shows \<open>domain(f)\<subseteq>domain(\<Union>S)\<close>
proof
  fix x
  assume H:\<open>x \<in> domain(f)\<close>
  show \<open>x \<in> domain(\<Union>S)\<close>
  proof(rule domainE[OF H])
    fix y
    assume K:\<open>\<langle>x, y\<rangle> \<in> f\<close>
    have \<open>\<langle>x, y\<rangle> \<in> \<Union>S\<close>
      by(rule UnionI[OF W K])
    then show \<open>x \<in> domain(\<Union>S)\<close>
      by(rule domainI)
  qed
qed
```
Verified through `IsabelleTheoryChecker` and `tests/test_recursion.py` with zero unproven obligations (`has_oops == False`, `has_sorry == False`, `has_cheat == False`, balanced `proof`/`qed` blocks).
