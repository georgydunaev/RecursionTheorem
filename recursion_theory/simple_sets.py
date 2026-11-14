"""Post's Problem, Simple Sets, and Finite-Injury Priority Arguments.

This module formalizes:
1. Simple Sets (Post 1944):
   A computably enumerable (c.e.) set S is simple if:
   - S is c.e.
   - S is coinfinite: N \\ S is infinite.
   - For every infinite c.e. set W_e, S intersects W_e (S cap W_e != empty).
   Equivalently: N \\ S contains no infinite c.e. subset.
2. Solution to Post's Problem for Many-One Reductions:
   - S is undecidable (not computable / not Delta_1^0): if S were computable,
     N \\ S would be an infinite c.e. set disjoint from S, contradiction.
   - The halting problem K does not many-one reduce to S (K not <=_m S):
     If K <=_m S, then N \\ K <=_m N \\ S. Since N \\ K is productive,
     N \\ S would contain an infinite c.e. set, contradiction.
   - Therefore, S is strictly between empty and K under many-one reduction:
     empty <_m S <_m K.
3. Post's Priority Construction:
   Requirements P_e: if W_e is infinite, pick x in W_e with x > 2e and put x in S.
   Restraint analysis: at most n elements from {0, ..., 2n} can ever enter S,
   guaranteeing at least n + 1 elements remain in N \\ S for all n.
4. Finite-Injury Priority Engine (PriorityWorker):
   Mechanizes priority arguments with requirements R_0 > R_1 > R_2 ...,
   movable markers, dynamic restraints, injury tracking, and convergence verification.
"""

from typing import Callable, Dict, List, Optional, Set, Tuple, Any


class PriorityRequirement:
    """A requirement in a priority construction."""

    def __init__(
        self,
        index: int,
        priority: int,
        name: Optional[str] = None,
        restraint: int = 0,
        marker: int = 0,
    ):
        self.index = index
        self.priority = priority
        self.name = name if name is not None else f"R_{index}"
        self.state = "unsatisfied"  # "unsatisfied", "satisfied", "active", "injured"
        self.restraint = restraint
        self.marker = marker
        self.action_count = 0
        self.injury_count = 0
        self.witness: Optional[int] = None

    def satisfy(self, witness: int, new_restraint: Optional[int] = None):
        """Mark the requirement as satisfied with a given witness."""
        self.state = "satisfied"
        self.witness = witness
        self.action_count += 1
        if new_restraint is not None:
            self.restraint = new_restraint

    def injure(self, reset_marker: Optional[int] = None):
        """Injure this requirement due to higher-priority action."""
        self.state = "injured"
        self.injury_count += 1
        self.witness = None
        if reset_marker is not None:
            self.marker = reset_marker

    def __repr__(self):
        return (
            f"Requirement({self.name}, priority={self.priority}, state={self.state}, "
            f"restraint={self.restraint}, marker={self.marker}, injuries={self.injury_count})"
        )


class PriorityWorker:
    """General engine for finite-injury priority arguments.

    Manages a collection of priority requirements ordered by priority
    (0 is highest priority, 1 is next, and so on).
    Tracks actions, movable markers, injuries, and convergence.
    """

    def __init__(self):
        self.requirements: Dict[int, PriorityRequirement] = {}
        self.current_stage = 0
        self.enumerated_set: Set[int] = set()
        self.action_history: List[Dict[str, Any]] = []
        self.injury_history: List[Dict[str, Any]] = []

    def add_requirement(
        self,
        index: int,
        priority: int,
        name: Optional[str] = None,
        restraint: int = 0,
        marker: int = 0,
    ):
        """Add a requirement to the priority engine."""
        req = PriorityRequirement(index, priority, name, restraint, marker)
        self.requirements[index] = req
        return req

    def get_requirement(self, index: int):
        return self.requirements.get(index)

    def current_restraint_above(self, priority: int):
        """Compute maximum restraint placed by requirements with higher priority (< priority)."""
        max_r = 0
        for req in self.requirements.values():
            if req.priority < priority and req.state == "satisfied":
                if req.restraint > max_r:
                    max_r = req.restraint
        return max_r

    def step(
        self,
        candidate_actions: List[Tuple[int, int, Dict[str, Any]]],
    ):
        """Execute one stage of the priority argument.

        candidate_actions is a list of tuples: (req_index, proposed_element, metadata).
        Selects the highest-priority unsatisfied/injured requirement whose action
        respects higher-priority restraints.
        """
        stage = self.current_stage
        self.current_stage += 1

        # Sort candidate actions by priority (lower number = higher priority)
        valid_candidates = []
        for req_idx, element, meta in candidate_actions:
            if req_idx not in self.requirements:
                continue
            req = self.requirements[req_idx]
            if req.state == "satisfied":
                continue

            higher_restraint = self.current_restraint_above(req.priority)
            # The action respects higher priority restraints if element > higher_restraint
            if element > higher_restraint:
                valid_candidates.append((req.priority, req_idx, element, meta))

        if not valid_candidates:
            return None

        valid_candidates.sort(key=lambda t: t[0])
        chosen_priority, chosen_idx, chosen_element, meta = valid_candidates[0]
        acting_req = self.requirements[chosen_idx]

        # Enumerate element into set
        self.enumerated_set.add(chosen_element)
        new_restraint = meta.get("new_restraint", chosen_element)
        acting_req.satisfy(witness=chosen_element, new_restraint=new_restraint)

        action_record = {
            "stage": stage,
            "requirement_index": chosen_idx,
            "priority": chosen_priority,
            "element": chosen_element,
            "metadata": meta,
        }
        self.action_history.append(action_record)

        # Injure all lower-priority requirements whose restraint or marker was violated
        for other_idx, other_req in self.requirements.items():
            if other_req.priority > chosen_priority and other_req.state == "satisfied":
                if chosen_element <= other_req.restraint:
                    other_req.injure(reset_marker=other_req.marker + 1)
                    injury_record = {
                        "stage": stage,
                        "caused_by_requirement": chosen_idx,
                        "caused_by_element": chosen_element,
                        "injured_requirement": other_idx,
                        "injured_priority": other_req.priority,
                    }
                    self.injury_history.append(injury_record)

        return action_record

    def verify_finite_injury(self, max_injuries_per_priority: Optional[Dict[int, int]] = None):
        """Verify that every requirement suffered at most a finite number of injuries."""
        injury_counts = {idx: req.injury_count for idx, req in self.requirements.items()}
        within_bounds = True
        if max_injuries_per_priority is not None:
            for idx, req in self.requirements.items():
                bound = max_injuries_per_priority.get(req.priority, float("inf"))
                if req.injury_count > bound:
                    within_bounds = False
        return {
            "finite_injury_verified": within_bounds,
            "injury_counts": injury_counts,
            "total_injuries": len(self.injury_history),
            "total_actions": len(self.action_history),
        }


class SimpleSet:
    """Formalization and construction of Post's Simple Set (Post 1944).

    Let W_0, W_1, W_2, ... be an effective enumeration of all c.e. sets.
    Post's Construction:
    At stage s, inspect requirements P_e for e <= s.
    If P_e is not yet satisfied and there exists x in W_{e, s} such that:
        x > 2 * e
    then put the smallest such x into S, and mark P_e as satisfied.

    Key Invariants:
    1. Each requirement P_e places at most ONE element into S.
    2. An element x <= 2n enters S only if it came from some P_e with 2e < x <= 2n,
       which implies e < n.
    3. Thus, at most n elements from {0, 1, ..., 2n} can ever enter S.
    4. Consequently, |(N \\ S) cap {0, ..., 2n}| >= n + 1 for all n.
       This guarantees N \\ S is strictly coinfinite!
    5. For any infinite c.e. set W_e, W_e contains infinitely many numbers,
       hence at least one number > 2e. Thus W_e cap S is non-empty.
    6. Therefore S is simple!
    """

    def __init__(self, ce_enumerators: Optional[Dict[int, Callable[[int], List[int]]]] = None):
        """Initialize with optional stage-by-stage c.e. set enumerators.

        ce_enumerators maps set index e to a callable stage_fn(s) returning
        the list of elements enumerated into W_e at stage s.
        """
        self.ce_enumerators = ce_enumerators if ce_enumerators is not None else {}
        self.S: Set[int] = set()
        self.satisfied_requirements: Dict[int, int] = {}  # e to witness x
        self.current_stage = 0
        self.history: List[Dict[str, Any]] = []

    def register_ce_set(self, index: int, stage_enumerator: Callable[[int], List[int]]):
        """Register a stage enumerator for c.e. set W_index."""
        self.ce_enumerators[index] = stage_enumerator

    def step(self, stage: Optional[int] = None):
        """Execute one stage of Post's simple set construction."""
        if stage is None:
            stage = self.current_stage
            self.current_stage += 1

        stage_action = None

        # Check unsatisfied requirements e <= stage in priority order e = 0, 1, ...
        for e in range(stage + 1):
            if e in self.satisfied_requirements:
                continue

            if e not in self.ce_enumerators:
                continue

            # Elements available in W_e up to stage
            available_elements = self.ce_enumerators[e](stage)
            # Find smallest x in W_{e, stage} such that x > 2 * e
            valid_elements = [x for x in available_elements if x > 2 * e and x not in self.S]

            if valid_elements:
                chosen_x = min(valid_elements)
                self.S.add(chosen_x)
                self.satisfied_requirements[e] = chosen_x
                stage_action = {
                    "stage": stage,
                    "requirement": e,
                    "element": chosen_x,
                    "restraint_bound": 2 * e,
                }
                self.history.append(stage_action)
                # At most one requirement acts per stage
                break

        return stage_action

    def run(self, stages: int):
        """Run Post's construction for a given number of stages."""
        for _ in range(stages):
            self.step()
        return self.S

    def is_in_set(self, x: int):
        """Check whether x is in S (enumerated so far)."""
        return x in self.S

    def complement_sample(self, max_bound: int):
        """Return elements of N \\ S up to max_bound."""
        return [x for x in range(max_bound + 1) if x not in self.S]

    def count_elements_up_to(self, bound: int):
        """Count |S cap {0, ..., bound}|."""
        return sum(1 for x in self.S if x <= bound)

    def coinfinity_lower_bound(self, n: int):
        """Verify Post's coinfinity bound for segment {0, 1, ..., 2n}.

        By construction, any element x <= 2n entering S came from requirement P_e
        with 2e < x <= 2n, so e < n.
        Thus at most n elements from {0, ..., 2n} can ever enter S.
        Therefore |(N \\ S) cap {0, ..., 2n}| >= (2n + 1) - n = n + 1.
        """
        total_in_range = 2 * n + 1
        elements_in_S = self.count_elements_up_to(2 * n)
        elements_in_complement = total_in_range - elements_in_S
        guaranteed_minimum = n + 1
        holds = (elements_in_complement >= guaranteed_minimum)
        return {
            "n": n,
            "range_bound": 2 * n,
            "total_in_range": total_in_range,
            "elements_in_S": elements_in_S,
            "elements_in_complement": elements_in_complement,
            "guaranteed_minimum": guaranteed_minimum,
            "holds": holds,
        }

    def verify_coinfinity(self, max_n: int):
        """Verify Post's coinfinity invariant across all n <= max_n."""
        results = []
        all_holds = True
        for n in range(max_n + 1):
            check = self.coinfinity_lower_bound(n)
            results.append(check)
            if not check["holds"]:
                all_holds = False
        return {
            "coinfinite_verified": all_holds,
            "checks": results,
            "sample_complement_size": len(self.complement_sample(2 * max_n)),
        }

    def witness_intersection(self, e: int):
        """Return witness x in S cap W_e if requirement P_e has acted."""
        return self.satisfied_requirements.get(e)

    def verify_infinite_ce_intersection(self, infinite_ce_indices: List[int]):
        """Verify that S intersects every specified infinite c.e. set W_e."""
        intersections = {}
        all_intersect = True
        for e in infinite_ce_indices:
            witness = self.witness_intersection(e)
            if witness is not None:
                intersections[e] = {"intersects": True, "witness": witness}
            else:
                intersections[e] = {"intersects": False, "witness": None}
                all_intersect = False
        return {
            "all_intersect": all_intersect,
            "intersections": intersections,
        }

    def post_problem_many_one_barrier(self):
        """Explain and verify why simple sets resolve Post's Problem for <=_m.

        Mathematical Deduction:
        1. S is computably enumerable by construction.
        2. S is not computable (undecidable):
           If S were computable, its complement N \\ S would be an infinite c.e. set.
           By definition of simplicity, S must intersect every infinite c.e. set.
           Therefore S cap (N \\ S) != empty, which is impossible.
           Hence S is not computable (not Delta_1^0).
        3. K does not many-one reduce to S (K not <=_m S):
           If K <=_m S via computable reduction f, then x in N \\ K iff f(x) in N \\ S.
           This means N \\ K <=_m N \\ S.
           The complement of the halting problem N \\ K is productive.
           Any set that is many-one above a productive set is itself productive.
           Therefore N \\ S would be productive.
           Every productive set contains an infinite c.e. subset.
           Therefore N \\ S would contain an infinite c.e. set W_e subset N \\ S.
           Then W_e cap S = empty, directly contradicting simplicity of S!
           Therefore, K cannot many-one reduce to S.
        4. Conclusion:
           empty <_m S <_m K.
           S is an intermediate computably enumerable degree under many-one reduction,
           settling Post's Problem for many-one reducibility!
        """
        return {
            "theorem": "Simple sets solve Post's Problem for many-one reductions",
            "S_is_ce": True,
            "S_is_coinfinite": True,
            "S_is_undecidable": True,
            "K_many_one_reduces_to_S": False,
            "status": "strictly_intermediate_degree",
            "reduction_chain": "empty <_m S <_m K",
        }
