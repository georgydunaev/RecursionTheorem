# [RECURSIONTHEOREM] Ticket 7458 -- RecursionTheorem: Refactor Kleene S-m-n Theorem and Fixpoint Formulations

**Repository:** `RecursionTheorem`
**Status:** `RESOLVED`
**Created:** `2026-10-27T22:48:44Z`
**Resolved:** `2026-11-13T23:50:00Z`

## Task Description
Decompose Kleene recursion theorem proofs into clean computability lemmas and index mapping functions.

## Implementation Details
1. Formalized an explicit IndexMapping abstraction hierarchy in `recursion_theory/kleene.py`:
   - `IndexMapping`: Base abstraction for computable index transformations between program codes.
   - `IdentityMapping`: Identity mapping id(e) = e.
   - `ConstantMapping`: Constant mapping C_k(e) = k.
   - `ComposedMapping`: Composition of index mappings (f o g)(e) = f(g(e)).
   - `DiagonalMapping`: Diagonal mapping d(x) = s_1_1(x, x).
   - `SmnMapping`: Parameter specialization mapping e maps to s_m_n(e, vec{x}).
   - `ParametricMapping`: Deterministic parametric fixed-point index mapping.
2. Formalized modular computability lemmas in `ComputabilityLemmas`:
   - `verify_smn_currying`: Equivalence between curried program and original multi-parameter program.
   - `verify_smn_iteration`: Composition and iterated currying equivalence for multi-stage parameter specialization.
   - `verify_diagonal_computability`: Totality and computability of the diagonal mapping.
   - `verify_padding_lemma`: Effective generation of infinitely many distinct equivalent program indices.
   - `verify_composition_lemma`: Computable composition index mapping.
   - `verify_universal_function`: Universal interpreter evaluation program.
3. Decomposed Kleene's Second Recursion Theorem into modular deduction steps:
   - Step 1: Diagonal index mapping construction d(x) = s_1_1(x, x).
   - Step 2: Auxiliary kernel function registration g(x, y) = phi(f(d(x)), y) with index v.
   - Step 3: Fixed point index evaluation e = d(v) = s_1_1(v, v).
   - Step 4: Verification of extensional equivalence phi_e(y) equiv phi_{f(e)}(y).
   - Encapsulated within `KleeneProofCertificate`.
4. Formalized Smullyan's Double Recursion Theorem:
   - Simultaneous fixed-point construction for pairs of bivariate index transformations: phi_a equiv phi_{f1(a, b)} and phi_b equiv phi_{f2(a, b)}.
5. Comprehensive unit tests added to `tests/test_recursion.py` under `TestIndexMappingAndComputabilityLemmas`.
