#!/usr/bin/env python3
"""Regenerate the fixed-label C8 crossing-order language from three seeds.

New companion implementation, 2026-09-10; not the historical discovery code.
See README.md for conventions, provenance, and the conditional completeness
argument. Generation never reads the frozen 2,544-entry language. An optional
comparison with that language happens only after generation has finished.
"""
from __future__ import annotations

import argparse
import ast
import base64
from collections import deque
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import platform
import sys
import time
import zlib

import networkx as nx

VERSION = "1.0.0"
N = 8
EDGES = tuple(range(N))
PARTNERS = tuple(frozenset(j for j in EDGES if (j-i) % N not in (0, 1, 7)) for i in EDGES)
PAIRS = tuple((i, j) for i, j in combinations(EDGES, 2) if j in PARTNERS[i])
TRIPLES = tuple(t for t in combinations(EDGES, 3) if all(j in PARTNERS[i] for i, j in combinations(t, 2)))
DB_ORDER = (0, 1, 11, 10, 9, 8, 7, 6)
EXPECTED_RELEASE_SHA256 = "23ae908626820dd3afaf1dbbc180619186e8bfcb417bf8a2bbcac2bb76369632"
EXPECTED_RAW_SHA256 = "8e260f0471170ffad6490fa6debdfd06c52f153a67d9079525511c63df7c907e"
EXPECTED_SIZES = [656, 896, 992]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def validate(system):
    """Each row is exactly the five nonincident edge labels, in some order."""
    if len(system) != N:
        raise ValueError("A C8 system must have eight rows.")
    result = []
    for e, row in enumerate(system):
        if any(type(x) is not int for x in row):
            raise ValueError(f"Row {e} has a noninteger label.")
        if len(row) != 5 or set(row) != PARTNERS[e]:
            raise ValueError(f"Row {e} must contain exactly {sorted(PARTNERS[e])}.")
        result.append(tuple(row))
    return tuple(result)


def dihedral(system, shift: int, reflection: bool):
    """Vertex i -> shift+i, or i -> shift-i; all e_i point i -> i+1."""
    mapping = tuple((shift-i-1) % N if reflection else (shift+i) % N for i in EDGES)
    out = [None] * N
    for e, row in enumerate(system):
        source_row = reversed(row) if reflection else row
        out[mapping[e]] = tuple(mapping[x] for x in source_row)
    return tuple(out)


def adjacent_triple_flip(system, triple):
    """A combinatorial superset of genuine empty-triangle RIII transitions.

    The two crossings must be consecutive on each of three pairwise
    nonincident edges. The resulting complete augmentation is tested for
    planarity separately; this function does not claim geometric legality.
    """
    indices = []
    for e in triple:
        a, b = (x for x in triple if x != e)
        p, q = system[e].index(a), system[e].index(b)
        if abs(p-q) != 1:
            return None
        indices.append((e, p, q))
    out = list(system)
    for e, p, q in indices:
        row = list(out[e])
        row[p], row[q] = row[q], row[p]
        out[e] = tuple(row)
    return tuple(out)


def neighbors(system):
    for reflection in (False, True):
        for shift in EDGES:
            yield dihedral(system, shift, reflection)
    for triple in TRIPLES:
        image = adjacent_triple_flip(system, triple)
        if image is not None:
            yield image


def augmented_graph(system):
    """Complete Fulek-Pach augmentation; no partial-system pruning.

    Original vertices are 0..7, crossing vertices are 8..27, and the
    32 crossing-to-crossing subdivision vertices are 28..59. Each crossing
    gets four locking edges joining the two arms of one edge to both arms
    of the other. These form the required four-cycle around the crossing.
    """
    system = validate(system)
    crossing = {pair: N+i for i, pair in enumerate(PAIRS)}
    graph = nx.Graph()
    graph.add_nodes_from(EDGES)
    arms = {}
    next_vertex = N + len(PAIRS)
    for e, row in enumerate(system):
        path = [e]
        for position, f in enumerate(row):
            if position:
                path.append(next_vertex)
                next_vertex += 1
            path.append(crossing[tuple(sorted((e, f)))])
        path.append((e+1) % N)
        graph.add_edges_from(zip(path, path[1:]))
        for position in range(1, len(path)-1, 2):
            arms[e, path[position]] = (path[position-1], path[position+1])
    for e, f in PAIRS:
        x = crossing[e, f]
        for a in arms[e, x]:
            for b in arms[f, x]:
                graph.add_edge(a, b)
    return graph


def is_realizable(system):
    graph = augmented_graph(system)
    planar, embedding = nx.check_planarity(graph)
    if planar:
        # Validate the returned embedding, including its Euler condition.
        embedding.check_structure()
        if set(embedding) != set(graph) or {
            frozenset(edge) for edge in embedding.edges()
        } != {frozenset(edge) for edge in graph.edges()}:
            raise RuntimeError("Planarity embedding does not represent the input graph.")
    return planar


def regenerate(seeds, max_systems=10000):
    """Explore to queue exhaustion, never stopping at an expected count.

    max_systems is an abort guard, not a pruning rule. An abort produces no
    successful report. Exceptions from the planarity engine propagate.
    """
    seeds = [validate(seed) for seed in seeds]
    if len(seeds) != 3 or len(set(seeds)) != 3:
        raise ValueError("Exactly three distinct seeds are required.")
    decisions = {}
    owner = {}
    components = []
    for component_id, seed in enumerate(seeds):
        if seed in owner:
            raise ValueError("Two supplied seeds belong to the same generated component.")
        component = set()
        queue = deque([seed])
        while queue:
            system = queue.popleft()
            if system in component:
                continue
            if system in owner:
                raise ValueError("The generated seed components overlap.")
            if system not in decisions:
                if len(decisions) >= max_systems:
                    raise RuntimeError("Candidate limit reached: no completeness report produced.")
                decisions[system] = is_realizable(system)
            if not decisions[system]:
                if system == seed:
                    raise ValueError("A supplied seed is not realizable.")
                continue
            component.add(system)
            owner[system] = component_id
            queue.extend(image for image in neighbors(system) if image not in component)
        components.append(component)
        print(f"Seed {component_id+1}: queue exhausted; {len(component)} systems", flush=True)

    # Check closure and component separation explicitly after traversal.
    dihedral_images = 0
    directed_flips = 0
    for component_id, component in enumerate(components):
        for system in component:
            for reflection in (False, True):
                for shift in EDGES:
                    image = dihedral(system, shift, reflection)
                    if image not in component:
                        raise RuntimeError("Dihedral closure check failed.")
                    dihedral_images += 1
            for triple in TRIPLES:
                image = adjacent_triple_flip(system, triple)
                if image is not None:
                    directed_flips += 1
                    # Stronger than closure under just genuine planar moves.
                    if image not in component:
                        raise RuntimeError("Unfiltered combinatorial flip closure check failed.")
    sizes = sorted(map(len, components))
    if sizes != EXPECTED_SIZES or len(owner) != 2544:
        raise RuntimeError(f"Unexpected result: component sizes {sizes}; no success report produced.")
    if directed_flips != 10624 or dihedral_images != 40704:
        raise RuntimeError("Unexpected closure statistics; no success report produced.")
    return components, {
        "unique_candidates_planarity_tested": len(decisions),
        "planar_candidates": sum(decisions.values()),
        "nonplanar_candidates": sum(not value for value in decisions.values()),
        "dihedral_images_checked_including_duplicates": dihedral_images,
        "directed_adjacent_triple_flips_checked": directed_flips,
        "component_sizes": sizes,
        "total_systems": len(owner),
        "all_queues_exhausted": True,
        "full_combinatorial_closure_verified": True,
    }


def read_frozen_reference(path: Path):
    """Read constant literals with ast; NEVER import/execute the release."""
    source = path.read_bytes()
    if sha256(source) != EXPECTED_RELEASE_SHA256:
        raise ValueError("Reference is not the exact audited v0.15.0 release (SHA-256 mismatch).")
    wanted = {"_DB682_C8_EDGE_ORDER", "_DB682_C8_LANGUAGE_COUNT",
              "_DB682_C8_LANGUAGE_RAW_SHA256", "_DB682_C8_LANGUAGE_B85"}
    values = {}
    for node in ast.parse(source).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in wanted:
                    values[target.id] = ast.literal_eval(node.value)
    if set(values) != wanted:
        raise ValueError("Missing reference literals.")
    if tuple(values["_DB682_C8_EDGE_ORDER"]) != DB_ORDER:
        raise ValueError("Unexpected DB682 edge convention.")
    raw = zlib.decompress(base64.b85decode(values["_DB682_C8_LANGUAGE_B85"].encode("ascii")))
    if sha256(raw) != EXPECTED_RAW_SHA256 or sha256(raw) != values["_DB682_C8_LANGUAGE_RAW_SHA256"]:
        raise ValueError("Frozen data checksum failed.")
    if values["_DB682_C8_LANGUAGE_COUNT"] != 2544 or len(raw) != 2544*40:
        raise ValueError("Unexpected frozen data length.")
    local = {e: i for i, e in enumerate(DB_ORDER)}
    systems = []
    for offset in range(0, len(raw), 40):
        rows = []
        for i, e in enumerate(DB_ORDER):
            row = tuple(local[x] for x in raw[offset+5*i:offset+5*i+5])
            rows.append(row if e in (0, 1) else row[::-1])
        systems.append(validate(rows))
    if len(set(systems)) != 2544:
        raise ValueError("Duplicate frozen systems.")
    return systems, {"release_sha256": sha256(source), "frozen_raw_sha256": sha256(raw)}


def to_db682(system):
    rows = []
    for i, row in enumerate(system):
        mapped = tuple(DB_ORDER[x] for x in row)
        rows.append(mapped if i < 2 else mapped[::-1])
    return tuple(rows)


def canonical_bytes(systems):
    return bytes(value for system in sorted(systems) for row in system for value in row)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seeds", type=Path, default=Path(__file__).with_name("seeds.json"))
    parser.add_argument("--output", type=Path, default=Path("results"), help="A new, nonexisting output directory")
    parser.add_argument("--reference-release", type=Path, help="Optional exact v0.15.0 file, read only AFTER generation")
    parser.add_argument("--max-systems", type=int, default=10000, help="Abort threshold; never treated as a completed result")
    args = parser.parse_args(argv)
    if args.output.exists():
        raise FileExistsError("Output directory already exists; choose a new --output directory.")
    if args.max_systems <= 0:
        raise ValueError("--max-systems must be positive.")
    started = time.perf_counter()
    seed_bytes = args.seeds.read_bytes()
    seed_doc = json.loads(seed_bytes)
    components, stats = regenerate([entry["rows"] for entry in seed_doc["seeds"]], args.max_systems)
    systems = sorted(set().union(*components))
    reference_check = {"performed": False}
    if args.reference_release:
        reference, provenance = read_frozen_reference(args.reference_release)
        missing, extra = set(reference)-set(systems), set(systems)-set(reference)
        if missing or extra:
            raise RuntimeError(f"Reference mismatch: {len(missing)} missing, {len(extra)} extra.")
        reference_check = {"performed": True, "exact_set_equality": True,
                           "missing_systems": 0, "extra_systems": 0, **provenance}
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    components = sorted(components, key=len)
    component_id = {system: i for i, component in enumerate(components) for system in component}
    local_data = {
        "schema": "c8-crossing-orders-v1", "vertices": list(EDGES),
        "oriented_edges": [[i, (i+1) % N] for i in EDGES],
        "row_order": list(EDGES), "count": len(systems),
        "component_sizes": list(map(len, components)),
        "component_id_by_system": [component_id[s] for s in systems], "systems": systems,
    }
    write_json(out/"c8_systems.json", local_data)
    write_json(out/"c8_systems_db682.json", {
        "row_order": DB_ORDER,
        "orientation_note": "Rows for DB edges 0,1 follow the cycle; rows 11,10,9,8,7,6 oppose it.",
        "count": len(systems), "systems": [to_db682(s) for s in systems],
    })
    report = {
        "status": "PASS", "program_version": VERSION,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": round(time.perf_counter()-started, 3),
        "python": platform.python_version(), "networkx": nx.__version__,
        "platform": platform.platform(),
        "program_sha256": sha256(Path(__file__).read_bytes()), "seeds_sha256": sha256(seed_bytes),
        **stats, "reference_comparison": reference_check,
        "canonical_local_data_sha256": sha256(canonical_bytes(systems)),
        "output_files_sha256": {name: sha256((out/name).read_bytes()) for name in
                                ("c8_systems.json", "c8_systems_db682.json")},
        "completeness_scope": "Conditional on the Fulek-Pach criterion and the published upper count of three C8 isotopy/RIII classes; see README.md.",
        "not_a_fresh_global_classification": True,
        "not_the_historical_generator": True,
    }
    write_json(out/"run_report.json", report)
    print(json.dumps({"status": "PASS", **stats, "reference_comparison": reference_check,
                      "elapsed_seconds": report["elapsed_seconds"]}, indent=2), flush=True)


if __name__ == "__main__":
    try:
        main()
    except (Exception, KeyboardInterrupt) as error:
        print(f"FAILED / INCONCLUSIVE: {error}", file=sys.stderr)
        sys.exit(1)
