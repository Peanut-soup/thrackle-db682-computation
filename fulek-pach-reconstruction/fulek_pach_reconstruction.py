"""Independent reconstruction of Fulek--Pach (2011), Section 4 and Appendix A.

This is NOT the authors' original software or a reproduction of its runtime.
See README.md for the precise fidelity limits and prefix-minor invariant.
Python >=3.10; NetworkX >=3.3. No precomputed crossing-order languages.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from decimal import Decimal, localcontext
import json
from math import factorial, prod
from pathlib import Path
import sys
import time

import networkx as nx

VERSION = "fp-published-method-1.0.0"


class Problem:
    """A connected, nonempty simple graph admitting an Euler trail.

    Edge IDs follow input order. Vertices are internally relabeled to prevent
    collisions between original vertices and crossing/gadget vertices.
    """
    def __init__(self, edges):
        self.labels = []
        ids = {}
        self.edges = []
        seen = set()
        for pair in edges:
            if len(pair) != 2:
                raise ValueError("Each edge must contain exactly two vertices.")
            u, v = pair
            if u == v:
                raise ValueError("Loops are not supported.")
            for vertex in pair:
                if vertex not in ids:
                    ids[vertex] = len(ids)
                    self.labels.append(vertex)
            a, b = ids[u], ids[v]
            key = frozenset((a, b))
            if key in seen:
                raise ValueError("Parallel/duplicate edges are not supported.")
            seen.add(key)
            self.edges.append((a, b))
        if not self.edges:
            raise ValueError("Supply at least one edge.")
        self.graph = nx.Graph()
        self.graph.add_edges_from(self.edges)
        if not nx.is_connected(self.graph):
            raise ValueError("This published-method baseline requires a connected graph.")
        odd = [v for v, degree in self.graph.degree() if degree % 2]
        if len(odd) not in (0, 2):
            raise ValueError("Appendix A uses an Euler trail; this graph has more than two odd-degree vertices.")
        self.lookup = {frozenset(edge): i for i, edge in enumerate(self.edges)}
        walk = (nx.eulerian_path(self.graph, source=odd[0]) if odd else
                nx.eulerian_circuit(self.graph, source=0))
        walk = list(walk)
        self.order = [self.lookup[frozenset(edge)] for edge in walk]
        self.oriented = {e: edge for e, edge in zip(self.order, walk)}
        self.nonincident = [tuple(f for f, pair in enumerate(self.edges)
                                  if not set(edge).intersection(pair))
                            for edge in self.edges]
        self.total = prod(factorial(len(row)) for row in self.nonincident)


def cycle(n):
    if n < 3:
        raise ValueError("A simple cycle needs at least three vertices.")
    return [(i, (i + 1) % n) for i in range(n)]


def dumbbell(a, b, length):
    """Two cycles joined by a length-l path; l<0 means a shared -l-edge path."""
    if min(a, b) < 3:
        raise ValueError("Cycle lengths must be at least three.")
    edges = cycle(a)
    if length < 0:
        shared = -length
        if shared >= min(a, b) - 1:
            raise ValueError("The common path must leave at least two edges on each cycle.")
        path = [shared] + list(range(a, a + b - shared - 1)) + [0]
        edges.extend(zip(path, path[1:]))
    elif length == 0:
        path = [0] + list(range(a, a + b - 1)) + [0]
        edges.extend(zip(path, path[1:]))
    else:
        edges.extend((a + i, a + (i + 1) % b) for i in range(b))
        path = [0] + list(range(a + b, a + b + length - 1)) + [a]
        edges.extend(zip(path, path[1:]))
    return edges


def crossing(e, f):
    return ("x", min(e, f), max(e, f))


def augmented_prefix(problem, pi, stage, complete):
    """Existing path portions plus only locking edges supported by those arms.

    Earlier edges have both endpoints; the current edge has its terminal
    endpoint ONLY when complete relative to the active edge set. Future edges
    are absent. At the final complete stage this is the full Section 4 graph.
    """
    graph = nx.Graph()
    graph.add_nodes_from(("v", i) for i in range(len(problem.labels)))
    arms = {}
    for e in problem.order[:stage + 1]:
        u, v = problem.oriented[e]
        path = [("v", u)] + [crossing(e, f) for f in pi[e]]
        if e != problem.order[stage] or complete:
            path.append(("v", v))
        expanded = [path[0]]
        for i, (left, right) in enumerate(zip(path, path[1:])):
            if left[0] == right[0] == "x":
                expanded.append(("s", e, i))
            expanded.append(right)
        graph.add_nodes_from(expanded)
        graph.add_edges_from(zip(expanded, expanded[1:]))
        for i, node in enumerate(expanded):
            if node[0] == "x":
                neighbors = []
                if i:
                    neighbors.append(expanded[i - 1])
                if i + 1 < len(expanded):
                    neighbors.append(expanded[i + 1])
                arms[(node, e)] = neighbors
    for node in tuple(graph):
        if node[0] == "x":
            _, e, f = node
            graph.add_edges_from((u, v) for u in arms.get((node, e), ())
                                 for v in arms.get((node, f), ()))
    return graph


def validate_complete(problem, pi):
    if len(pi) != len(problem.edges):
        raise ValueError("Witness has the wrong number of rows.")
    for e, required in enumerate(problem.nonincident):
        if len(pi[e]) != len(required) or set(pi[e]) != set(required):
            raise ValueError(f"Invalid complete crossing row {e}.")
    return nx.is_planar(augmented_prefix(problem, pi, len(problem.order) - 1, True))


def six_cycles(problem):
    """All simple six-cycles, including cycles with chords; one direction each."""
    found = set()
    def extend(path):
        if len(path) == 6:
            if problem.graph.has_edge(path[-1], path[0]):
                rev = (path[0], *reversed(path[1:]))
                found.add(min(tuple(path), rev))
            return
        for v in sorted(problem.graph[path[-1]]):
            if v > path[0] and v not in path:
                extend(path + [v])
    for v in sorted(problem.graph):
        extend([v])
    return sorted(found)


def c6_constraints(problem):
    constraints = []
    for vertices in six_cycles(problem):
        directed = [(vertices[i], vertices[(i + 1) % 6]) for i in range(6)]
        ids = [problem.lookup[frozenset(edge)] for edge in directed]
        tests = []
        for i in range(6):
            e1, e2, e3, e4 = [ids[(i + j) % 6] for j in range(4)]
            for host_index, before, after in ((i, e4, e3), ((i + 3) % 6, e1, e2)):
                host = ids[host_index]
                if problem.oriented[host] != directed[host_index]:
                    before, after = after, before
                tests.append((host, before, after))
        constraints.append(tests)
    return constraints


def c6_consistent(pi, constraints):
    positions = [{f: i for i, f in enumerate(row)} for row in pi]
    for tests in constraints:
        possible = [True, True]
        for host, before, after in tests:
            if before in positions[host] and after in positions[host]:
                forward = positions[host][before] < positions[host][after]
                possible[0] &= forward
                possible[1] &= not forward
        if not any(possible):
            return False
    return True


@dataclass
class Statistics:
    calls: int = 0
    prefix_tests: int = 0
    prefix_prunes: int = 0
    c6_prunes: int = 0
    complete_tests: int = 0
    valid_systems: int = 0
    resolved: int = 0


class SearchStopped(Exception):
    pass


class Search:
    def __init__(self, problem, *, use_c6=True, prefix_pruning=True,
                 enumerate_all=False, seconds=None, max_calls=None, progress=0):
        if seconds is not None and seconds < 0:
            raise ValueError("seconds must be nonnegative")
        if max_calls is not None and max_calls < 0:
            raise ValueError("max_calls must be nonnegative")
        self.problem = problem
        self.pi = [[] for _ in problem.edges]
        self.constraints = c6_constraints(problem) if use_c6 else []
        self.prefix_pruning = prefix_pruning
        self.enumerate_all = enumerate_all
        self.seconds, self.max_calls, self.progress = seconds, max_calls, progress
        self.stats = Statistics()
        self.witnesses = []
        self.started = self.last_progress = 0.0
        self.older = []
        factors = []
        for stage, e in enumerate(problem.order):
            prior = set(problem.order[:stage])
            partners = tuple(f for f in problem.order[:stage] if f in problem.nonincident[e])
            self.older.append(partners)
            factors.append(factorial(len(partners)) * prod(
                1 + len(prior.intersection(problem.nonincident[f])) for f in partners))
        self.suffix = [1] * (len(factors) + 1)
        for i in range(len(factors) - 1, -1, -1):
            self.suffix[i] = self.suffix[i + 1] * factors[i]
        if self.suffix[0] != problem.total:
            raise AssertionError("Stage factors do not equal the complete-system count.")
        self._has_run = False

    def _check(self):
        now = time.perf_counter()
        if self.seconds is not None and now - self.started >= self.seconds:
            raise SearchStopped("Time limit reached.")
        if self.max_calls is not None and self.stats.calls >= self.max_calls:
            raise SearchStopped("Call limit reached.")
        if self.progress and now - self.last_progress >= self.progress:
            with localcontext() as ctx:
                ctx.prec = 45
                percent = Decimal(self.stats.resolved) * 100 / self.problem.total
                print(f"{percent:.20f}% resolved; calls={self.stats.calls}; "
                      f"planarity tests={self.stats.prefix_tests + self.stats.complete_tests}",
                      file=sys.stderr, flush=True)
            self.last_progress = now

    def _weight(self, stage, remaining):
        return (factorial(len(remaining)) * prod(len(self.pi[f]) + 1 for f in remaining)
                * self.suffix[stage + 1])

    def _visit(self, stage, remaining):
        self._check()
        self.stats.calls += 1
        if not c6_consistent(self.pi, self.constraints):
            self.stats.c6_prunes += 1
            self.stats.resolved += self._weight(stage, remaining)
            return False
        complete = not remaining
        last = stage == len(self.problem.order) - 1
        if last and complete:
            self.stats.complete_tests += 1
            good = validate_complete(self.problem, self.pi)
            self.stats.resolved += 1
            if good:
                self.stats.valid_systems += 1
                self.witnesses.append([row.copy() for row in self.pi])
                return not self.enumerate_all
            return False
        if self.prefix_pruning:
            self.stats.prefix_tests += 1
            if not nx.is_planar(augmented_prefix(self.problem, self.pi, stage, complete)):
                self.stats.prefix_prunes += 1
                self.stats.resolved += self._weight(stage, remaining)
                return False
        if complete:
            return self._visit(stage + 1, self.older[stage + 1])
        current = self.problem.order[stage]
        for f in remaining:
            rest = tuple(g for g in remaining if g != f)
            for pos in range(len(self.pi[f]) + 1):
                self.pi[f].insert(pos, current)
                self.pi[current].append(f)
                try:
                    if self._visit(stage, rest):
                        return True
                finally:
                    if self.pi[current].pop() != f or self.pi[f].pop(pos) != current:
                        raise AssertionError("Backtracking failed to restore a row.")
        return False

    def run(self):
        if self._has_run:
            raise ValueError("Use a new Search object for each run.")
        self._has_run = True
        self.started = self.last_progress = time.perf_counter()
        exhausted = False
        reason = ""
        try:
            stopped_on_witness = self._visit(0, self.older[0])
            exhausted = not stopped_on_witness
            if exhausted and self.stats.resolved != self.problem.total:
                raise AssertionError("Exhausted search does not cover all complete systems.")
            status = "THRACKLEABLE" if self.witnesses else "NONTHRACKLEABLE"
            reason = "Verified complete witness." if self.witnesses else "Exhausted the search with exact accounting."
        except (SearchStopped, KeyboardInterrupt) as exc:
            status = "THRACKLEABLE" if self.witnesses else "INCONCLUSIVE"
            reason = str(exc) or "Interrupted."
        except Exception as exc:
            status = "INCONCLUSIVE"
            reason = f"Internal failure: {type(exc).__name__}: {exc}"
        return {"version": VERSION, "status": status, "reason": reason,
                "exhausted": exhausted, "seconds": time.perf_counter() - self.started,
                "statistics": asdict(self.stats), "total_systems": self.problem.total,
                "edge_ids": [list(edge) for edge in self.problem.edges],
                "vertex_labels": [repr(v) for v in self.problem.labels],
                "activation_order": self.problem.order, "orientation": self.problem.oriented,
                "witnesses": self.witnesses, "networkx_version": nx.__version__,
                "options": {"c6_rule": bool(self.constraints),
                            "prefix_pruning": self.prefix_pruning,
                            "enumerate_all": self.enumerate_all}}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--cycle", type=int, metavar="N")
    inputs.add_argument("--db", type=int, nargs=3, metavar=("A", "B", "L"))
    inputs.add_argument("--edges", type=Path, help="JSON array of [u,v] pairs (string/integer labels)")
    parser.add_argument("--seconds", type=float, default=None)
    parser.add_argument("--max-calls", type=int, default=None)
    parser.add_argument("--progress", type=float, default=5)
    parser.add_argument("--no-c6-rule", action="store_true")
    parser.add_argument("--no-prefix-pruning", action="store_true")
    parser.add_argument("--enumerate-all", action="store_true", help="Store every witness; use only for small tests")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        edges = (cycle(args.cycle) if args.cycle is not None else
                 dumbbell(*args.db) if args.db is not None else
                 json.loads(args.edges.read_text(encoding="utf-8")))
        search = Search(Problem(edges), use_c6=not args.no_c6_rule,
                        prefix_pruning=not args.no_prefix_pruning,
                        enumerate_all=args.enumerate_all, seconds=args.seconds,
                        max_calls=args.max_calls, progress=args.progress)
    except (ValueError, TypeError, OSError) as exc:
        parser.error(str(exc))
    result = search.run()
    content = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(content + "\n", encoding="utf-8")
    print(content)
    return 0 if result["status"] != "INCONCLUSIVE" else 2


if __name__ == "__main__":
    raise SystemExit(main())
