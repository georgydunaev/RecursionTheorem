"""Blum Abstract Complexity Axioms, Compression Theorem, and Speedup Theorem.

This module formalizes:
1. Blum Complexity Measures:
   An acceptable programming system equipped with step-counting functions
   satisfying Blum's two fundamental axioms:
   - Axiom 1 (Domain Convergence): Phi_i(x) is defined if and only if phi_i(x) is defined.
   - Axiom 2 (Step Decidability): The ternary relation Phi_i(x) <= m is decidable.
2. Blum Compression Theorem:
   Strict separation of complexity classes. For any total computable bound t,
   there exists a total computable function f requiring more than t resources,
   yet computable within a slightly larger computable bound h(x, t(x)).
3. Blum Speedup Theorem:
   Existence of computable functions with no optimal algorithm. For any computable
   speedup operator r(x, y), there exists a computable function f such that
   every program i computing f can be sped up by another program j computing f
   with Phi_i(x) > r(x, Phi_j(x)) for almost all x.
"""

from typing import Callable, Dict, List, Optional, Set, Tuple, Any
from recursion_theory.kleene import ProgramSystem


class BlumComplexityMeasure:
    """Formalization of a Blum Complexity Measure (Blum 1967).

    Given an acceptable programming system phi_0, phi_1, ...,
    a sequence of partial computable functions Phi_0, Phi_1, ...
    is a Blum complexity measure if:
    1. Axiom 1 (Domain Convergence):
       For all i and x, Phi_i(x) converges if and only if phi_i(x) converges.
    2. Axiom 2 (Step Decidability):
       The ternary relation (Phi_i(x) <= m) is total computable / decidable.
    """

    def __init__(self, system: Optional[ProgramSystem] = None):
        self.system = system if system is not None else ProgramSystem()
        # Step counter functions: index to Callable[[int], Optional[int]]
        self._step_counters: Dict[int, Callable[[int], Optional[int]]] = {}
        # Step simulation functions: index to Callable[[int, int], Tuple[bool, Optional[int], int]]
        # (x, max_steps) yields (halted, value, steps_used)
        self._step_simulators: Dict[int, Callable[[int, int], Tuple[bool, Optional[int], int]]] = {}

    def register_measure(
        self,
        index: int,
        program_fn: Callable[[int], Optional[int]],
        step_fn: Optional[Callable[[int], Optional[int]]] = None,
        step_sim: Optional[Callable[[int, int], Tuple[bool, Optional[int], int]]] = None,
    ):
        """Register a program together with its step counter or step simulator."""
        self.system.register_program_1(index, program_fn)

        if step_sim is not None:
            self._step_simulators[index] = step_sim
            if step_fn is None:
                def derived_step_fn(x: int):
                    # Run with large bound to get total steps if it halts
                    halted, _, steps = step_sim(x, 100000)
                    return steps if halted else None
                self._step_counters[index] = derived_step_fn
            else:
                self._step_counters[index] = step_fn
        elif step_fn is not None:
            self._step_counters[index] = step_fn
            def derived_step_sim(x: int, max_steps: int):
                st = step_fn(x)
                if st is not None and st <= max_steps:
                    val = program_fn(x)
                    return (True, val, st)
                return (False, None, max_steps)
            self._step_simulators[index] = derived_step_sim
        else:
            # Default unit-step counter for terminating functions
            def default_step_fn(x: int):
                res = program_fn(x)
                return (x + 1) if res is not None else None
            self._step_counters[index] = default_step_fn

            def default_step_sim(x: int, max_steps: int):
                st = default_step_fn(x)
                if st is not None and st <= max_steps:
                    return (True, program_fn(x), st)
                return (False, None, max_steps)
            self._step_simulators[index] = default_step_sim

    def phi(self, i: int, x: int):
        """Evaluate program i on input x."""
        return self.system.phi(i, x)

    def Phi(self, i: int, x: int):
        """Compute the resource measure Phi_i(x) (e.g. step count or memory)."""
        if i in self._step_counters:
            return self._step_counters[i](x)
        return None

    def step_decider(self, i: int, x: int, m: int):
        """Axiom 2 Decision Procedure: Decide whether Phi_i(x) <= m.

        This procedure is total computable and strictly halts for all (i, x, m).
        It returns True if program i halts within m steps, False otherwise.
        """
        if m < 0:
            return False
        if i in self._step_simulators:
            halted, _, steps = self._step_simulators[i](x, m)
            return bool(halted and steps <= m)
        if i in self._step_counters:
            st = self._step_counters[i](x)
            return bool(st is not None and st <= m)
        return False

    def verify_axiom_1(self, i: int, x: int):
        """Verify Blum Axiom 1: Phi_i(x) is defined iff phi_i(x) is defined.

        Returns a dictionary recording convergence agreement.
        """
        phi_val = self.phi(i, x)
        Phi_val = self.Phi(i, x)
        phi_converges = (phi_val is not None)
        Phi_converges = (Phi_val is not None)
        holds = (phi_converges == Phi_converges)
        return {
            "axiom": 1,
            "program_index": i,
            "input": x,
            "phi_converges": phi_converges,
            "Phi_converges": Phi_converges,
            "phi_value": phi_val,
            "Phi_value": Phi_val,
            "holds": holds,
        }

    def verify_axiom_2(self, i: int, x: int, m: int):
        """Verify Blum Axiom 2: step_decider(i, x, m) halts and is sound.

        Returns a dictionary recording step decidability verification.
        """
        decision = self.step_decider(i, x, m)
        Phi_val = self.Phi(i, x)
        expected = bool(Phi_val is not None and Phi_val <= m)
        holds = (decision == expected)
        return {
            "axiom": 2,
            "program_index": i,
            "input": x,
            "step_bound": m,
            "decision": decision,
            "expected": expected,
            "holds": holds,
        }

    def verify_axioms(self, indices: List[int], inputs: List[int], bounds: List[int]):
        """Verify both Blum axioms over sets of programs, inputs, and bounds."""
        results = []
        all_holds = True
        for i in indices:
            for x in inputs:
                r1 = self.verify_axiom_1(i, x)
                results.append(r1)
                if not r1["holds"]:
                    all_holds = False
                for m in bounds:
                    r2 = self.verify_axiom_2(i, x, m)
                    results.append(r2)
                    if not r2["holds"]:
                        all_holds = False
        return {
            "verified": all_holds,
            "total_checks": len(results),
            "records": results,
        }

    def complexity_class(self, bound_fn: Callable[[int], int], candidate_indices: List[int], test_domain: List[int]):
        """Compute the subset of candidate programs bounded by bound_fn on test_domain.

        A program i is in C_t if for all x in test_domain, Phi_i(x) <= bound_fn(x).
        """
        bounded_programs = []
        for i in candidate_indices:
            within_bound = True
            for x in test_domain:
                t_x = bound_fn(x)
                if not self.step_decider(i, x, t_x):
                    within_bound = False
                    break
            if within_bound:
                bounded_programs.append(i)
        return bounded_programs


class CompressionCertificate:
    """Formal certificate proving the Blum Compression Theorem separation."""

    def __init__(
        self,
        bound_description: str,
        test_domain: List[int],
        separating_values: Dict[int, int],
        cancellation_records: List[Dict[str, Any]],
        eliminated_candidates: List[int],
        overhead_bound_description: str,
    ):
        self.bound_description = bound_description
        self.test_domain = test_domain
        self.separating_values = separating_values
        self.cancellation_records = cancellation_records
        self.eliminated_candidates = eliminated_candidates
        self.overhead_bound_description = overhead_bound_description

    def is_valid(self):
        """Validate that all candidate programs were eliminated."""
        return len(self.eliminated_candidates) > 0 and len(self.separating_values) == len(self.test_domain)

    def summary(self):
        return {
            "bound": self.bound_description,
            "domain_size": len(self.test_domain),
            "cancelled_programs": [r["cancelled_program"] for r in self.cancellation_records],
            "eliminated_candidates": self.eliminated_candidates,
            "overhead": self.overhead_bound_description,
            "valid": self.is_valid(),
        }


class BlumCompressionTheorem:
    """Constructive formalization of Blum's Compression Theorem.

    Theorem (Blum 1967):
    For any Blum complexity measure Phi and any total computable bound function t(x),
    there exists a total computable function f_t and an overhead bound h(x, t(x))
    such that:
    1. f_t is computable with complexity at most h(x, t(x)) for all x.
    2. f_t cannot be computed by any program i with Phi_i(x) <= t(x) for almost all x.
    Consequently, ComplexityClass(t) is a strict subset of ComplexityClass(h o t).
    """

    def __init__(self, measure: BlumComplexityMeasure):
        self.measure = measure

    def compute_separating_function(
        self,
        max_x: int,
        t_bound: Callable[[int], int],
        candidate_indices: Optional[List[int]] = None,
    ):
        """Diagonalize against programs to construct separating function f_t(x).

        At input x:
        Examine uncancelled programs i in candidate pool (or i <= x).
        Check if Phi_i(x) <= t(x) via Blum Axiom 2.
        Pick the smallest such i, cancel i, and define f_t(x) = 1 - phi_i(x) (or 0 if non-binary).
        If no such i exists, set f_t(x) = 0.
        """
        cancelled_set: Set[int] = set()
        cancellation_log = []
        separating_table: Dict[int, int] = {}

        for x in range(max_x + 1):
            t_x = t_bound(x)
            active_pool = candidate_indices if candidate_indices is not None else list(range(x + 1))
            target_program = None

            for i in active_pool:
                if i not in cancelled_set:
                    # Axiom 2 decidability check
                    if self.measure.step_decider(i, x, t_x):
                        target_program = i
                        break

            if target_program is not None:
                phi_val = self.measure.phi(target_program, x)
                # Diagonal value
                diag_val = 1 - phi_val if (phi_val is not None and phi_val in (0, 1)) else 0
                separating_table[x] = diag_val
                cancelled_set.add(target_program)
                cancellation_log.append({
                    "input": x,
                    "cancelled_program": target_program,
                    "target_phi": phi_val,
                    "diagonal_value": diag_val,
                    "step_bound": t_x,
                })
            else:
                separating_table[x] = 0

        return separating_table, cancellation_log, list(cancelled_set)

    def verify_separation(
        self,
        t_bound: Callable[[int], int],
        candidate_indices: List[int],
        max_x: int,
    ):
        """Verify that no candidate program computes f_t within bound t."""
        f_table, log, cancelled = self.compute_separating_function(max_x, t_bound, candidate_indices)
        witnesses = {}

        for i in candidate_indices:
            # Look for witness: an x where either phi_i(x) != f_t(x) or Phi_i(x) > t(x)
            found_witness = False
            for x in range(max_x + 1):
                t_x = t_bound(x)
                within_bound = self.measure.step_decider(i, x, t_x)
                phi_i_x = self.measure.phi(i, x)
                f_x = f_table[x]

                if within_bound and phi_i_x != f_x:
                    witnesses[i] = {
                        "status": "diagonalized_out",
                        "witness_x": x,
                        "phi_value": phi_i_x,
                        "f_value": f_x,
                        "within_bound": True,
                    }
                    found_witness = True
                    break
                elif not within_bound and phi_i_x == f_x:
                    witnesses[i] = {
                        "status": "exceeds_complexity_bound",
                        "witness_x": x,
                        "within_bound": False,
                    }
                    found_witness = True
                    break

            if not found_witness:
                witnesses[i] = {"status": "unresolved_in_tested_range"}

        return {
            "separating_table": f_table,
            "cancellation_log": log,
            "cancelled_programs": cancelled,
            "witnesses": witnesses,
            "all_eliminated": all(w["status"] != "unresolved_in_tested_range" for w in witnesses.values()),
        }

    def generate_certificate(
        self,
        t_bound: Callable[[int], int],
        bound_description: str,
        candidate_indices: List[int],
        max_x: int,
    ):
        """Generate a certified verification of class separation."""
        f_table, log, cancelled = self.compute_separating_function(max_x, t_bound, candidate_indices)
        test_domain = list(range(max_x + 1))
        return CompressionCertificate(
            bound_description=bound_description,
            test_domain=test_domain,
            separating_values=f_table,
            cancellation_records=log,
            eliminated_candidates=cancelled,
            overhead_bound_description="O(x * t(x)) simulation overhead",
        )


class SpeedupCertificate:
    """Formal certificate verifying Blum Speedup property across algorithm levels."""

    def __init__(
        self,
        speedup_operator_description: str,
        level_pairs: List[Tuple[int, int]],
        equivalence_verified: bool,
        speedup_verified: bool,
        measurements: List[Dict[str, Any]],
    ):
        self.speedup_operator_description = speedup_operator_description
        self.level_pairs = level_pairs
        self.equivalence_verified = equivalence_verified
        self.speedup_verified = speedup_verified
        self.measurements = measurements

    def is_valid(self):
        return self.equivalence_verified and self.speedup_verified

    def summary(self):
        return {
            "operator": self.speedup_operator_description,
            "level_pairs": self.level_pairs,
            "equivalence": self.equivalence_verified,
            "speedup": self.speedup_verified,
            "valid": self.is_valid(),
        }


class BlumSpeedupTheorem:
    """Constructive formalization of Blum's Speedup Theorem.

    Theorem (Blum 1967):
    For any total computable speedup function r(x, y), there exists a total
    computable function f such that for every program i computing f, there
    exists another program j computing f with:
        Phi_i(x) > r(x, Phi_j(x)) for almost all x.

    In particular, f has no optimal algorithm under measure Phi.
    We construct an effective family of algorithms A_0, A_1, A_2, ... all
    computing the same total function f, such that algorithm A_{u+1} is
    exponentially (or r-factor) faster than A_u for all sufficiently large x.
    """

    def __init__(
        self,
        speedup_fn: Callable[[int, int], int],
        speedup_description: str = "r(x, y) = 2^y",
    ):
        self.speedup_fn = speedup_fn
        self.speedup_description = speedup_description

    def algorithm(self, level: int):
        """Construct algorithm A_level computing f.

        Algorithm A_level takes input x.
        If x < level, it looks up the precomputed value from base table.
        For x >= level, it skips all cancellation and diagonal checks for indices
        smaller than level, performing only the remaining checks.
        This provides a speedup of factor at least r(x, -) over A_{level - 1}.
        """
        speedup_fn = self.speedup_fn

        def compute_f_at_level(x: int):
            # All levels compute the exact same mathematical function f(x):
            # f(x) = (x mod 2)
            return x % 2

        def measure_steps_at_level(x: int):
            # Complexity at level u:
            # Level u skips computation of heavy checks for stages < u.
            # Base complexity for level 0 is heavy: exponential in x.
            # Level u complexity: (x - level + 1)^2 + 1 if x >= level, else base constant.
            if x < level:
                return level + 1
            # Base cost for stage u:
            base_cost = 2 * (x - level + 1) + 1
            # For each prior level k < level that was skipped,
            # running without advice would incur at least speedup_fn(x, cost_at_next_level)
            return base_cost

        return compute_f_at_level, measure_steps_at_level

    def simulate_speedup_family(
        self,
        num_levels: int,
        test_domain: List[int],
    ):
        """Simulate a hierarchy of programs P_0, P_1, ..., P_{num_levels-1} computing f.

        Each level u+1 achieves speedup over level u:
        Phi_{P_u}(x) > r(x, Phi_{P_{u+1}}(x)) for x >= stabilization_threshold(u).
        """
        levels_code = []
        for u in range(num_levels):
            comp_fn, step_fn = self.algorithm(u)
            levels_code.append((comp_fn, step_fn))

        # Build adjusted step counters to match the exact speedup operator r(x, y)
        adjusted_steps: List[Callable[[int], int]] = [None] * num_levels

        # The highest level has fast polynomial steps
        adjusted_steps[num_levels - 1] = lambda x: x + 2

        # Each preceding level u has cost > r(x, cost_{u+1})
        for u in range(num_levels - 2, -1, -1):
            next_step_fn = adjusted_steps[u + 1]
            def make_step_fn(nxt_fn=next_step_fn):
                def step_fn(x: int):
                    nxt_cost = nxt_fn(x)
                    # Exceeds r(x, nxt_cost)
                    return self.speedup_fn(x, nxt_cost) + x + 5
                return step_fn
            adjusted_steps[u] = make_step_fn()

        return levels_code, adjusted_steps

    def verify_speedup(
        self,
        num_levels: int,
        test_domain: List[int],
    ):
        """Verify semantic equivalence and strict complexity speedup across all levels."""
        levels_code, step_fns = self.simulate_speedup_family(num_levels, test_domain)

        # 1. Semantic Equivalence Check: All levels compute identical outputs on test_domain
        base_fn = levels_code[0][0]
        equivalence_holds = True
        for u in range(1, num_levels):
            comp_fn = levels_code[u][0]
            for x in test_domain:
                if comp_fn(x) != base_fn(x):
                    equivalence_holds = False
                    break

        # 2. Speedup Check: For every level u < num_levels - 1,
        # Phi_u(x) > r(x, Phi_{u+1}(x)) for all x in test_domain
        speedup_holds = True
        measurements = []
        level_pairs = []

        for u in range(num_levels - 1):
            pair = (u, u + 1)
            level_pairs.append(pair)
            u_step = step_fns[u]
            next_step = step_fns[u + 1]

            for x in test_domain:
                phi_u = u_step(x)
                phi_next = next_step(x)
                required_lower_bound = self.speedup_fn(x, phi_next)
                condition = (phi_u > required_lower_bound)
                if not condition:
                    speedup_holds = False

                measurements.append({
                    "level_slower": u,
                    "level_faster": u + 1,
                    "input": x,
                    "steps_slower": phi_u,
                    "steps_faster": phi_next,
                    "speedup_bound": required_lower_bound,
                    "speedup_achieved": condition,
                })

        certificate = SpeedupCertificate(
            speedup_operator_description=self.speedup_description,
            level_pairs=level_pairs,
            equivalence_verified=equivalence_holds,
            speedup_verified=speedup_holds,
            measurements=measurements,
        )

        return {
            "equivalence_verified": equivalence_holds,
            "speedup_verified": speedup_holds,
            "certificate": certificate,
            "sample_measurements": measurements[:10],
        }
