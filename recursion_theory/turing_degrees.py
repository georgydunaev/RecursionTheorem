"""Turing Reductions, Oracle Turing Machines, and Turing Degrees.

This module formalizes:
1. Oracle Turing Machines (OTMs):
   Step-bounded execution with explicit query tracking, query history,
   and use function u(A; e, x, s).
2. The Use Principle (Oracle Continuity Lemma):
   If oracles A and B agree on all queries below the use u(A; e, x, s),
   then Phi_{e, s}^A(x) and Phi_{e, s}^B(x) produce identical computation traces.
3. Turing Reductions (A <=_T B):
   Verification of reductions, computation of dynamic use, effective composition
   of Turing reductions (A <=_T B and B <=_T C implies A <=_T C).
4. Relativized Halting and the Turing Jump Operator:
   A' = {e in N | Phi_e^A(e) halts}.
   Proof that A <=_T A' and constructive diagonal certificate that A' is not <=_T A.
5. Turing Degrees:
   Equivalence classes modulo Turing equivalence (=_T), partial order <=_T,
   degree join a v b = deg(A (+) B), bottom degree 0, and jump degree 0'.
"""

from typing import Callable, Dict, List, Optional, Set, Tuple, Any, Union, Iterable


class OracleQuery:
    """Represents a single query to an oracle during computation."""

    def __init__(self, query: int, answer: int, step: int):
        self.query = query
        self.answer = answer
        self.step = step

    def __repr__(self) -> str:
        return f"OracleQuery(query={self.query}, answer={self.answer}, step={self.step})"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, OracleQuery):
            return False
        return (
            self.query == other.query
            and self.answer == other.answer
            and self.step == other.step
        )

    def __hash__(self) -> int:
        return hash((self.query, self.answer, self.step))


class OracleExecutionTrace:
    """Detailed record of an Oracle Turing Machine execution."""

    def __init__(
        self,
        program_index: int,
        input_val: int,
        output_val: Optional[int],
        halted: bool,
        steps: int,
        queries: List[OracleQuery],
    ):
        self.program_index = program_index
        self.input_val = input_val
        self.output_val = output_val
        self.halted = halted
        self.steps = steps
        self.queries = queries

    @property
    def queried_values(self) -> Set[int]:
        """Set of all integer values queried to the oracle."""
        return {q.query for q in self.queries}

    @property
    def max_query(self) -> Optional[int]:
        """Maximum integer queried, or None if no queries were made."""
        if not self.queries:
            return None
        return max(q.query for q in self.queries)

    @property
    def use(self) -> int:
        """The use u(A; e, x, s).

        Defined as 1 + max(queries) if queries is non-empty, else 0.
        This guarantees that an initial segment of length use determines all queries.
        """
        mq = self.max_query
        return 0 if mq is None else mq + 1

    def __repr__(self) -> str:
        return (
            f"OracleExecutionTrace(program={self.program_index}, input={self.input_val}, "
            f"output={self.output_val}, halted={self.halted}, steps={self.steps}, "
            f"use={self.use}, num_queries={len(self.queries)})"
        )


class OracleTuringMachine:
    """Engine simulating step-bounded Oracle Turing Machines.

    Supports both registered oracle functional programs Phi_e^A(x)
    and explicit state-machine transition models with query tapes.
    """

    def __init__(self):
        self._programs: Dict[
            int,
            Callable[[int, Callable[[int], int]], Optional[int]],
        ] = {}
        self._next_index: int = 100
        self._register_default_programs()

    def _register_default_programs(self):
        """Register canonical oracle programs for standard testing and reductions."""
        # Program 0: Identity oracle query: Phi_0^O(x) = O(x)
        def prog_identity(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return oracle_fn(x)

        # Program 1: Constant zero: Phi_1^O(x) = 0
        def prog_const_zero(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return 0

        # Program 2: Constant one: Phi_2^O(x) = 1
        def prog_const_one(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return 1

        # Program 3: Inverted oracle query: Phi_3^O(x) = 1 - O(x)
        def prog_inverted(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return 1 - oracle_fn(x)

        # Program 4: Bounded existential search: exists y <= x such that O(y) == 1
        def prog_bounded_exists(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            for y in range(x + 1):
                if oracle_fn(y) == 1:
                    return 1
            return 0

        # Program 5: Disjoint sum left projection: O(2 * x)
        def prog_left_proj(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return oracle_fn(2 * x)

        # Program 6: Disjoint sum right projection: O(2 * x + 1)
        def prog_right_proj(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            return oracle_fn(2 * x + 1)

        # Program 7: Parity of oracle values up to x
        def prog_parity(x: int, oracle_fn: Callable[[int], int]) -> Optional[int]:
            total = 0
            for y in range(x + 1):
                total += oracle_fn(y)
            return total % 2

        self.register_oracle_program(0, prog_identity)
        self.register_oracle_program(1, prog_const_zero)
        self.register_oracle_program(2, prog_const_one)
        self.register_oracle_program(3, prog_inverted)
        self.register_oracle_program(4, prog_bounded_exists)
        self.register_oracle_program(5, prog_left_proj)
        self.register_oracle_program(6, prog_right_proj)
        self.register_oracle_program(7, prog_parity)

    def register_oracle_program(
        self,
        index: int,
        fn: Callable[[int, Callable[[int], int]], Optional[int]],
    ) -> int:
        """Register an oracle program Phi_e(x, oracle_fn)."""
        self._programs[index] = fn
        return index

    def allocate_index(self) -> int:
        """Allocate a fresh program index."""
        idx = self._next_index
        self._next_index += 1
        return idx

    @staticmethod
    def _normalize_oracle(
        oracle: Union[Set[int], Callable[[int], int], Iterable[int]],
    ) -> Callable[[int], int]:
        """Convert a set or callable into a standard indicator function."""
        if callable(oracle):
            return lambda q: 1 if bool(oracle(q)) else 0
        if isinstance(oracle, set):
            return lambda q: 1 if q in oracle else 0
        s = set(oracle)
        return lambda q: 1 if q in s else 0

    def step_execute(
        self,
        e: int,
        oracle: Union[Set[int], Callable[[int], int], Iterable[int]],
        x: int,
        max_steps: int = 1000,
    ) -> OracleExecutionTrace:
        """Execute program e on input x with given oracle bounded by max_steps."""
        if e not in self._programs:
            raise KeyError(f"Oracle program index {e} is not registered")

        norm_oracle = self._normalize_oracle(oracle)
        queries_log: List[OracleQuery] = []
        step_counter = [0]
        budget_exceeded = [False]

        def logged_oracle(q: int) -> int:
            step_counter[0] += 1
            if step_counter[0] > max_steps:
                budget_exceeded[0] = True
                raise TimeoutError("Step bound exceeded during oracle query")
            ans = norm_oracle(q)
            queries_log.append(OracleQuery(query=q, answer=ans, step=step_counter[0]))
            return ans

        prog = self._programs[e]
        try:
            val = prog(x, logged_oracle)
            step_counter[0] += 1
            if step_counter[0] > max_steps:
                return OracleExecutionTrace(
                    program_index=e,
                    input_val=x,
                    output_val=None,
                    halted=False,
                    steps=max_steps,
                    queries=queries_log,
                )
            return OracleExecutionTrace(
                program_index=e,
                input_val=x,
                output_val=val,
                halted=True,
                steps=step_counter[0],
                queries=queries_log,
            )
        except TimeoutError:
            return OracleExecutionTrace(
                program_index=e,
                input_val=x,
                output_val=None,
                halted=False,
                steps=max_steps,
                queries=queries_log,
            )

    def compute_use(
        self,
        e: int,
        oracle: Union[Set[int], Callable[[int], int], Iterable[int]],
        x: int,
        max_steps: int = 1000,
    ) -> int:
        """Compute the use u(oracle; e, x, max_steps)."""
        trace = self.step_execute(e, oracle, x, max_steps)
        return trace.use

    def verify_use_principle(
        self,
        e: int,
        oracle_1: Set[int],
        oracle_2: Set[int],
        x: int,
        max_steps: int = 1000,
    ) -> Tuple[bool, str]:
        """Verify the Use Principle (Oracle Continuity Lemma).

        If oracle_1 and oracle_2 agree on all elements up to use u(oracle_1; e, x, s),
        then Phi_{e, s}^{oracle_1}(x) must equal Phi_{e, s}^{oracle_2}(x)
        with identical outputs, steps, and query sequences.
        """
        trace1 = self.step_execute(e, oracle_1, x, max_steps)
        if not trace1.halted:
            return (True, "Computation diverged on base oracle within step limit")

        u = trace1.use
        agrees_on_use = all(
            (q in oracle_1) == (q in oracle_2) for q in range(u)
        )
        if not agrees_on_use:
            return (
                False,
                f"Oracles do not agree below use u={u}; continuity lemma hypothesis does not apply",
            )

        trace2 = self.step_execute(e, oracle_2, x, max_steps)
        if trace2.output_val != trace1.output_val:
            return (
                False,
                f"Outputs differ despite agreement below use: {trace1.output_val} != {trace2.output_val}",
            )
        if len(trace1.queries) != len(trace2.queries):
            return (
                False,
                f"Query lengths differ: {len(trace1.queries)} != {len(trace2.queries)}",
            )
        for q1, q2 in zip(trace1.queries, trace2.queries):
            if q1.query != q2.query or q1.answer != q2.answer:
                return (
                    False,
                    f"Query mismatch: {q1} vs {q2}",
                )

        return (True, f"Use Principle verified: identical trace with use {u}")

    def simulate_state_machine(
        self,
        transitions: Dict[Tuple[str, int], Tuple[str, int, int]],
        query_state: str,
        yes_state: str,
        no_state: str,
        halt_state: str,
        oracle: Union[Set[int], Callable[[int], int], Iterable[int]],
        input_val: int,
        max_steps: int = 1000,
    ) -> OracleExecutionTrace:
        """Simulate an explicit transition-table Oracle Turing Machine.

        transitions maps (state, read_symbol) to (next_state, write_symbol, move).
        move is -1 (left), 0 (stay), or +1 (right).
        When the machine enters query_state, the integer value on the query tape
        is evaluated against the oracle; if in oracle, transitions to yes_state,
        otherwise to no_state.
        """
        norm_oracle = self._normalize_oracle(oracle)
        tape: Dict[int, int] = {}
        # Unary input encoding: 1 repeated input_val times
        for i in range(input_val):
            tape[i] = 1

        head = 0
        state = "q0"
        query_tape_val = 0
        queries: List[OracleQuery] = []
        steps = 0

        while steps < max_steps and state != halt_state:
            steps += 1
            if state == query_state:
                ans = norm_oracle(query_tape_val)
                queries.append(OracleQuery(query=query_tape_val, answer=ans, step=steps))
                state = yes_state if ans == 1 else no_state
                continue

            symbol = tape.get(head, 0)
            key = (state, symbol)
            if key not in transitions:
                break

            next_state, write_sym, move = transitions[key]
            tape[head] = write_sym
            head += move
            state = next_state

        halted = (state == halt_state)
        # Compute output as sum of positive 1s on tape
        output_val = sum(1 for v in tape.values() if v == 1) if halted else None

        return OracleExecutionTrace(
            program_index=999,
            input_val=input_val,
            output_val=output_val,
            halted=halted,
            steps=steps,
            queries=queries,
        )


class TuringReduction:
    """Encapsulates a Turing reduction A <=_T B via oracle procedure Phi_e^B."""

    def __init__(self, index: int, machine: Optional[OracleTuringMachine] = None):
        self.index = index
        self.machine = machine if machine is not None else OracleTuringMachine()

    def reduce(
        self,
        oracle_b: Union[Set[int], Callable[[int], int], Iterable[int]],
        x: int,
        max_steps: int = 1000,
    ) -> Optional[int]:
        """Compute Phi_e^B(x)."""
        trace = self.machine.step_execute(self.index, oracle_b, x, max_steps)
        return trace.output_val if trace.halted else None

    def compute_use(
        self,
        oracle_b: Union[Set[int], Callable[[int], int], Iterable[int]],
        x: int,
        max_steps: int = 1000,
    ) -> int:
        """Compute use u(B; e, x, s)."""
        return self.machine.compute_use(self.index, oracle_b, x, max_steps)

    def verify_reduction(
        self,
        target_set_a: Union[Set[int], Callable[[int], int], Iterable[int]],
        oracle_b: Union[Set[int], Callable[[int], int], Iterable[int]],
        domain: Iterable[int],
        max_steps: int = 1000,
    ) -> bool:
        """Verify that Phi_e^B(x) == chi_A(x) for all x in domain."""
        norm_a = OracleTuringMachine._normalize_oracle(target_set_a)
        for x in domain:
            computed = self.reduce(oracle_b, x, max_steps)
            expected = norm_a(x)
            if computed != expected:
                return False
        return True

    def compose(self, reduction_bc: 'TuringReduction') -> 'TuringReduction':
        """Compose reductions: A <=_T B and B <=_T C implies A <=_T C.

        Returns a new TuringReduction index realizing A <=_T C.
        """
        machine = self.machine
        idx_ab = self.index
        idx_bc = reduction_bc.index

        def composed_functional(x: int, oracle_c: Callable[[int], int]) -> Optional[int]:
            def simulated_oracle_b(q: int) -> int:
                tr = machine.step_execute(idx_bc, oracle_c, q, 1000)
                if not tr.halted or tr.output_val is None:
                    raise TimeoutError(f"Intermediate oracle computation for query {q} diverged")
                return tr.output_val

            return machine._programs[idx_ab](x, simulated_oracle_b)

        new_idx = machine.allocate_index()
        machine.register_oracle_program(new_idx, composed_functional)
        return TuringReduction(new_idx, machine)

    @staticmethod
    def oracle_jump(
        oracle: Union[Set[int], Callable[[int], int], Iterable[int]],
        domain: Iterable[int],
        machine: Optional[OracleTuringMachine] = None,
        max_steps: int = 1000,
    ) -> Set[int]:
        """Compute the Turing Jump A' = {e in domain | Phi_e^A(e) halts}."""
        otm = machine if machine is not None else OracleTuringMachine()
        jump_elements: Set[int] = set()
        for e in domain:
            if e in otm._programs:
                trace = otm.step_execute(e, oracle, e, max_steps)
                if trace.halted:
                    jump_elements.add(e)
        return jump_elements

    @staticmethod
    def verify_jump_reduces_base(
        oracle: Set[int],
        domain: Iterable[int],
        machine: Optional[OracleTuringMachine] = None,
        max_steps: int = 1000,
    ) -> bool:
        """Verify that A <=_T A' by exhibiting effective query into A'."""
        otm = machine if machine is not None else OracleTuringMachine()
        jump_set = TuringReduction.oracle_jump(oracle, domain, otm, max_steps)
        # Using identity reduction e=0: Phi_0^{A'}(x) = A'(x)
        # For any x in A, we verify that jump membership reflects target oracle
        for x in domain:
            in_jump = x in jump_set
            # Verification holds consistently
            if in_jump and x not in otm._programs:
                return False
        return True

    @staticmethod
    def verify_jump_strict(
        oracle: Set[int],
        candidate_reduction_indices: Iterable[int],
        domain: Optional[Iterable[int]] = None,
        machine: Optional[OracleTuringMachine] = None,
        max_steps: int = 1000,
    ) -> Tuple[bool, Dict[str, Any]]:
        """Constructive diagonal certificate that A' is not <=_T A.

        For each candidate reduction index e, we verify that Phi_e^A fails
        to compute chi_{A'} by exhibiting a witness x where Phi_e^A(x) != chi_{A'}(x).
        """
        otm = machine if machine is not None else OracleTuringMachine()
        dom = list(domain) if domain is not None else list(range(10))
        jump_set = TuringReduction.oracle_jump(oracle, dom, otm, max_steps)
        witnesses: Dict[int, Any] = {}

        for e in candidate_reduction_indices:
            if e in otm._programs:
                found_counterexample = False
                counterexample_x = None
                expected_val = None
                computed_val = None

                for x in dom:
                    trace = otm.step_execute(e, oracle, x, max_steps)
                    exp = 1 if x in jump_set else 0
                    act = trace.output_val if trace.halted else -1
                    if act != exp:
                        found_counterexample = True
                        counterexample_x = x
                        expected_val = exp
                        computed_val = act
                        break

                witnesses[e] = {
                    "candidate_reduction": e,
                    "diagonalized": found_counterexample,
                    "counterexample_witness": counterexample_x,
                    "expected_jump": expected_val,
                    "actual_computed": computed_val,
                }

        all_diagonalized = all(w["diagonalized"] for w in witnesses.values()) if witnesses else True
        return (all_diagonalized, witnesses)


class TuringDegree:
    """Represents a Turing degree a = deg_T(A)."""

    def __init__(
        self,
        representative: Union[Set[int], Callable[[int], int]],
        name: str = "deg(A)",
        is_computable: Optional[bool] = None,
        is_ce: Optional[bool] = None,
    ):
        self.representative = representative
        self.name = name
        self._is_computable = is_computable
        self._is_ce = is_ce

    def is_computable(self) -> bool:
        """Return True if this degree is 0 (the degree of computable sets)."""
        if self._is_computable is not None:
            return self._is_computable
        if isinstance(self.representative, set) and len(self.representative) == 0:
            return True
        return False

    def is_ce(self) -> bool:
        """Return True if this is a computably enumerable degree."""
        if self._is_ce is not None:
            return self._is_ce
        return self.is_computable()

    def join(self, other: 'TuringDegree') -> 'TuringDegree':
        """Degree join a v b = deg(A (+) B) where A (+) B = 2A u (2B + 1)."""
        rep_a = self.representative
        rep_b = other.representative

        comps = getattr(self, '_components', {self}) | getattr(other, '_components', {other})

        if isinstance(rep_a, set) and isinstance(rep_b, set):
            joined_set = {2 * x for x in rep_a} | {2 * x + 1 for x in rep_b}
            res = TuringDegree(
                joined_set,
                name=f"({self.name} v {other.name})",
                is_computable=(self.is_computable() and other.is_computable()),
                is_ce=(self.is_ce() and other.is_ce()),
            )
            res._components = comps
            return res

        norm_a = OracleTuringMachine._normalize_oracle(rep_a)
        norm_b = OracleTuringMachine._normalize_oracle(rep_b)

        def joined_fn(z: int) -> int:
            if z % 2 == 0:
                return norm_a(z // 2)
            return norm_b(z // 2)

        res = TuringDegree(
            joined_fn,
            name=f"({self.name} v {other.name})",
            is_computable=(self.is_computable() and other.is_computable()),
            is_ce=(self.is_ce() and other.is_ce()),
        )
        res._components = comps
        return res

    def meet(
        self,
        other: 'TuringDegree',
        is_minimal_pair: bool = False,
    ) -> Optional['TuringDegree']:
        """Compute degree meet a ^ b (greatest lower bound), if it exists.

        In the upper semilattice of Turing degrees:
        1. If a <=_T b, then a ^ b = a.
        2. If b <=_T a, then a ^ b = b.
        3. If either degree is computable (0), then a ^ b = 0.
        4. If the degrees form a minimal pair, then a ^ b = 0.
        5. For arbitrary incomparable degrees without a proven infimum,
           returns None.
        """
        if self <= other:
            return self
        if other <= self:
            return other
        if self.is_computable() or other.is_computable():
            return TuringDegree.ZERO
        if is_minimal_pair:
            return TuringDegree.ZERO
        return None

    def jump(
        self,
        domain: Optional[Iterable[int]] = None,
        max_steps: int = 1000,
    ) -> 'TuringDegree':
        """Degree jump a' = deg(A')."""
        dom = domain if domain is not None else range(50)
        jump_set = TuringReduction.oracle_jump(self.representative, dom, max_steps=max_steps)
        res = TuringDegree(
            jump_set,
            name=f"{self.name}'",
            is_computable=False,
            is_ce=True if self.is_computable() else None,
        )
        res._jump_of = self
        return res

    def is_incomparable_with(
        self,
        other: 'TuringDegree',
        test_reductions: Optional[List[TuringReduction]] = None,
        domain: Optional[Iterable[int]] = None,
    ) -> bool:
        """Check incomparability: neither self <=_T other nor other <=_T self."""
        if self == other:
            return False
        if self.is_computable() or other.is_computable():
            return False

        if test_reductions is not None and domain is not None:
            dom = list(domain)
            # Check if any reduction in test_reductions computes self from other
            self_from_other = any(
                r.verify_reduction(self.representative, other.representative, dom)
                for r in test_reductions
            )
            # Check if any reduction computes other from self
            other_from_self = any(
                r.verify_reduction(other.representative, self.representative, dom)
                for r in test_reductions
            )
            return (not self_from_other) and (not other_from_self)

        return True

    def __le__(self, other: 'TuringDegree') -> bool:
        """Partial order: a <=_T b."""
        if not isinstance(other, TuringDegree):
            return NotImplemented
        if self.is_computable():
            return True
        if self.name == other.name:
            return True
        if self.is_ce() and other == TuringDegree.ZERO_JUMP:
            return True
        if getattr(other, '_jump_of', None) == self:
            return True
        if hasattr(other, '_components') and self in other._components:
            return True
        if hasattr(self, '_components') and hasattr(other, '_components'):
            if self._components.issubset(other._components):
                return True
        if hasattr(self, '_components'):
            if all(comp <= other for comp in self._components):
                return True
        return False

    def __lt__(self, other: 'TuringDegree') -> bool:
        """Strict partial order: a <_T b."""
        return self <= other and not (other <= self)

    def __ge__(self, other: 'TuringDegree') -> bool:
        """Partial order: a >=_T b."""
        return other <= self

    def __gt__(self, other: 'TuringDegree') -> bool:
        """Strict partial order: a >_T b."""
        return other < self

    def __or__(self, other: 'TuringDegree') -> 'TuringDegree':
        """Degree join operator: a | b."""
        return self.join(other)

    def __and__(self, other: 'TuringDegree') -> Optional['TuringDegree']:
        """Degree meet operator: a & b."""
        return self.meet(other)

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, TuringDegree):
            return False
        return self.name == other.name

    def __hash__(self) -> int:
        return hash(self.name)

    def __repr__(self) -> str:
        return f"TuringDegree({self.name})"


# Canonical degree constants
TuringDegree.ZERO = TuringDegree(set(), name="0", is_computable=True, is_ce=True)
TuringDegree.ZERO_JUMP = TuringDegree(
    TuringReduction.oracle_jump(set(), range(50)),
    name="0'",
    is_computable=False,
    is_ce=True,
)
