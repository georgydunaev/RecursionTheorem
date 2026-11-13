# RecursionTheorem

Mathematical foundations and formalizations of recursion theorems across Set Theory (Zermelo-Fraenkel) and Computability Theory (Kleene recursion theorems, fixed-point combinators, and primitive recursion).

## Overview

The Recursion Theorem appears in two fundamental branches of mathematical logic:

1. **Set-Theoretic Recursion Theorem (Dedekind / Peano recursion in ZF)**:
   Given a set $A$, an initial value $a \in A$, and a step function $g : (A \times \mathbb{N}) \to A$, there exists a unique function $f : \mathbb{N} \to A$ such that:
   $$f(0) = a$$
   $$f(n + 1) = g(f(n), n) \quad \text{for all } n \in \mathbb{N}$$
   Formalized in Isabelle/ZF in `Recursion-Addition/recursion.thy`.

2. **Computability-Theoretic Recursion Theorems (Kleene)**:
   - **Kleene's First Recursion Theorem (Least Fixed Point)**:
     Every computable operator $\Phi$ on partial functions has a computable least fixed point $\Phi(f) = f$, obtained via the join of finite approximations $\bigcup_{k \ge 0} \Phi^k(\emptyset)$.
   - **Kleene's Second Recursion Theorem (The Fixed-Point Theorem)**:
     In any acceptable programming system with an $S_{1,1}$ parameter function, for every total computable function $f$, there exists an index $e$ such that:
     $$\varphi_e \simeq \varphi_{f(e)}$$
     Formalized and constructively executable in `recursion_theory/kleene.py`.
   - **Fixed-Point Combinators in Untyped Lambda Calculus**:
     Constructive reduction and fixed-point behavior of Curry's $Y$ combinator, Turing's $\Theta$ combinator, and call-by-value $Z$ combinator in `recursion_theory/combinators.py`.
   - **Primitive Recursive Functions (PRF)**:
     Composition, primitive recursion schemas, and unbounded minimalization ($\mu$-operator) in `recursion_theory/primitive_recursion.py`.

## Repository Architecture

```text
RecursionTheorem/
├── README.md
├── Recursion-Addition/
│   ├── Makefile
│   ├── ROOT
│   ├── document/
│   │   └── root.tex
│   └── recursion.thy          (Complete Isabelle/ZF formalization; zero open proofs)
├── recursion_theory/          (Computational and formalization package)
│   ├── __init__.py
│   ├── combinators.py         (Untyped lambda calculus, Y, Theta, Z combinators, Church arithmetic)
│   ├── kleene.py              (Kleene 1st & 2nd recursion theorems, S-m-n, Rice theorem, quines)
│   ├── primitive_recursion.py (PRF schema, Peano arithmetic, Mu-operator)
│   └── theory_checker.py      (Automated Isabelle/ZF structural & proof hygiene checker)
├── tests/
│   └── test_recursion.py      (Comprehensive test suite; 25 passing test cases)
└── tickets/                   (Local ticket ledger for project tracking)
```

## Key Components

### 1. Isabelle/ZF Formalization (`Recursion-Addition/recursion.thy`)
The Isabelle/ZF development formalizes:
- **Foundational Set Theory**: Properties of functions, pairs, and natural number induction.
- **Partial Computations**: `partcomp(A, t, m, a, g)` defining partial approximations on `succ(m)`.
- **Function Unions**: Compatibility of function families `pcs(A, a, g)` and the union function.
- **The Recursion Theorem**: `theorem recursionthm` proving unique existence of recursive functions.
- **Natural Number Addition**: `definition addg` and `theorem addition` proving existence and uniqueness of Peano addition in ZF.
- **Proof Completeness**: Strict absence of `sorry` or `oops`. The `domuncomp` lemma is fully proven from first principles (`UnionI`, `domainE`, `domainI`).

### 2. Computability and Lambda Calculus (`recursion_theory/`)
- **`kleene.py`**:
  - `KleeneFirstRecursion`: Fixed-point iteration, monotonicity checks, and least fixed-point derivation.
  - `ProgramSystem`: Acceptable programming system with verified $S_{1,1}$ parameter currying and diagonal $d(x) = s(x, x)$.
  - `KleeneSecondRecursion`: Diagonal fixed-point index constructor yielding $\varphi_e \simeq \varphi_{f(e)}$.
  - `ParametricRecursionTheorem`: Uniform parametric index transformer $\varphi_{h(p)} \simeq g(h(p), p, -)$.
  - `RicesTheoremVerification`: Constructive deduction showing any decider for a non-trivial semantic property yields an immediate contradiction with its fixed-point index.
  - `QuineConstructor`: Pure diagonal fixed-point self-reproducing code generator.
- **`combinators.py`**:
  - Pure Lambda Calculus AST (`Var`, `Abs`, `App`) with capture-avoiding substitution.
  - Normal-order and applicative-order reduction engines.
  - Curry's $Y$ combinator, Turing's $\Theta$ combinator, and Plotkin's $Z$ combinator.
  - Church encodings: booleans, pairs, numerals, arithmetic operations (`plus`, `times`, `pred`, `iszero`), and recursive factorial without recursive syntax.
- **`primitive_recursion.py`**:
  - Inductive schemas: `Zero`, `Succ`, `Proj`, `Comp`, `Rec`.
  - Verified Peano ring laws: addition commutativity, associativity, and distributivity.
  - Unbounded minimalization `Mu` operator for $\mu$-recursive functions.
- **`theory_checker.py`**:
  - Static AST and proof hygiene parser for Isabelle theory files (`.thy`).
  - Scans for unproven obligations (`sorry`, `oops`, `cheat`), balanced `proof`/`qed` blocks, and extracts theorems and lemmas.

## Verification & Testing

Run the full verification suite using Python's standard `unittest` runner:

```bash
python3 -m unittest discover -s tests
```

Output:
```text
Ran 25 tests in 0.050s
OK
```

## Contributing & Tickets

Issue and task tracking are managed via `tickets/` in the repository and through local GitLab tickets (`manage_tickets.py`).
All code must adhere to:
- Strict proof soundness with no open proof obligations.
- Complete unit test coverage for new constructors and algorithms.
- Full compatibility with Python 3 standard library and Isabelle/ZF conventions.

## License

MIT License. See LICENSE file for details.
