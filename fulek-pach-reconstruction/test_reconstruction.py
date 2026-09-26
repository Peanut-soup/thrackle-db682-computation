"""Independent complete-system oracle and regression checks. Run directly."""
import itertools
import json
from pathlib import Path
import time
from unittest.mock import patch

import networkx as nx

import fulek_pach_reconstruction as fp

ROOT = Path(__file__).resolve().parent


def independent_full_graph(problem, rows):
    """Integer-node builder, independent of the chronological prefix builder."""
    count = len(problem.labels)
    cross = {}
    for e, required in enumerate(problem.nonincident):
        for f in required:
            if e < f:
                cross[e, f] = count
                count += 1
    g = nx.Graph()
    g.add_nodes_from(range(count))
    neighbors = {}
    for e, row in enumerate(rows):
        u, v = problem.oriented[e]
        crossings = [cross[tuple(sorted((e, f)))] for f in row]
        chain = [u]
        for x in crossings:
            if len(chain) > 1:
                chain.append(count)
                count += 1
            chain.append(x)
        chain.append(v)
        g.add_edges_from(zip(chain, chain[1:]))
        for x in crossings:
            index = chain.index(x)
            neighbors[e, x] = chain[index - 1], chain[index + 1]
    for (e, f), x in cross.items():
        a, b = neighbors[e, x]
        c, d = neighbors[f, x]
        g.add_edges_from(((a, c), (c, b), (b, d), (d, a)))
    return g


def key(rows):
    return tuple(tuple(row) for row in rows)


def exhaustive_oracle(problem):
    valid = set()
    examined = 0
    for rows in itertools.product(*(itertools.permutations(p) for p in problem.nonincident)):
        examined += 1
        if nx.is_planar(independent_full_graph(problem, rows)):
            valid.add(key(rows))
    assert examined == problem.total
    return valid


def all_prefixes(problem, full):
    for stage, current in enumerate(problem.order):
        older = set(problem.order[:stage])
        sequence = [f for f in full[current] if f in older]
        for amount in range(len(sequence) + 1):
            modeled = set(sequence[:amount])
            partial = [[] for _ in problem.edges]
            for e in older:
                partial[e] = [f for f in full[e] if f in older or (f == current and e in modeled)]
            partial[current] = sequence[:amount]
            yield stage, amount == len(sequence), partial


def check_problem(edges, name, report):
    problem = fp.Problem(edges)
    started = time.perf_counter()
    expected = exhaustive_oracle(problem)
    for c6 in (False, True):
        search = fp.Search(problem, use_c6=c6, enumerate_all=True)
        result = search.run()
        assert result['exhausted'], (name, result)
        assert {key(rows) for rows in result['witnesses']} == expected, name
        assert result['statistics']['valid_systems'] == len(expected), name
        assert result['statistics']['resolved'] == problem.total, name
        assert all(not row for row in search.pi), 'State not restored'
    # Disable ALL pruning on small examples to check unique leaf enumeration.
    if problem.total <= 1000:
        result = fp.Search(problem, use_c6=False, prefix_pruning=False, enumerate_all=True).run()
        assert result['statistics']['complete_tests'] == problem.total
        assert {key(rows) for rows in result['witnesses']} == expected
    prefix_count = 0
    for witness in expected:
        for stage, complete, rows in all_prefixes(problem, witness):
            assert nx.is_planar(fp.augmented_prefix(problem, rows, stage, complete)), name
            prefix_count += 1
    report[name] = {'complete_systems_independently_tested': problem.total,
                    'valid_systems': len(expected), 'valid_prefixes_checked': prefix_count,
                    'seconds': time.perf_counter() - started}
    print(name, report[name], flush=True)


def main():
    report = {}
    for n in (3, 4, 5, 6):
        check_problem(fp.cycle(n), f'C{n}', report)
    for i, g in enumerate(nx.graph_atlas_g()):
        if 2 <= len(g) <= 4 and nx.is_connected(g) and sum(d % 2 for _, d in g.degree()) in (0, 2):
            check_problem(list(g.edges()), f'atlas_{i}', report)
    check_problem(fp.dumbbell(3, 3, 0), 'DB(3,3,0)', report)
    check_problem(fp.dumbbell(3, 3, -1), 'DB(3,3,-1)', report)
    check_problem(fp.dumbbell(3, 4, -1), 'DB(3,4,-1)', report)

    # This exact valid C6 completion was killed by both supplied older versions.
    fixture = json.loads((ROOT / 'legacy_prefix_results.json').read_text())
    for version in ('v03', 'v041'):
        for name in ('C6', 'C8'):
            case = fixture[version][name]['first_counterexample']
            p = fp.Problem(fp.cycle(int(name[1:])))
            assert p.order == case['order']
            full = [case['full_pi'][str(e)] for e in range(len(p.edges))]
            partial = [case['partial_pi'][str(e)] for e in range(len(p.edges))]
            assert nx.is_planar(independent_full_graph(p, full))
            assert nx.is_planar(fp.augmented_prefix(p, partial, case['stage'], False))
    report['legacy_counterexamples_preserved'] = 4

    # A diverse C8 witness corpus is an additional positive regression, not an
    # independent proof that the complete C8 language contains exactly 2,544.
    corpus_file = ROOT / 'c8_regression_witnesses.json'
    if corpus_file.exists():
        p = fp.Problem(fp.cycle(8))
        corpus = json.loads(corpus_file.read_text())
        prefixes = 0
        for full in corpus:
            assert nx.is_planar(independent_full_graph(p, full))
            for stage, complete, partial in all_prefixes(p, full):
                assert nx.is_planar(fp.augmented_prefix(p, partial, stage, complete))
                prefixes += 1
        report['C8_positive_regressions'] = {'witnesses': len(corpus), 'prefixes': prefixes}

    p = fp.Problem(fp.cycle(6))
    for kwargs in ({'seconds': 0}, {'max_calls': 0}, {'max_calls': 10}):
        result = fp.Search(p, **kwargs).run()
        assert result['status'] == 'INCONCLUSIVE' and not result['exhausted']
    with patch.object(fp.nx, 'is_planar', side_effect=KeyboardInterrupt):
        assert fp.Search(p).run()['status'] == 'INCONCLUSIVE'
    with patch.object(fp.nx, 'is_planar', side_effect=RuntimeError('injected backend failure')):
        assert fp.Search(p).run()['status'] == 'INCONCLUSIVE'
    report['limits_interrupts_and_backend_failure'] = 'PASS'
    for bad in ([], [(0, 0)], [(0, 1), (1, 0)], [(0, 1), (2, 3)], [(0, 1), (0, 2), (0, 3)]):
        try:
            fp.Problem(bad)
        except ValueError:
            pass
        else:
            raise AssertionError(('Input should be rejected', bad))
    labels = [('x', 0, 1), ('s', 0, 1), ('v', 0), 'other']
    odd_labels = fp.Problem([(labels[i], labels[(i + 1) % 4]) for i in range(4)])
    assert fp.Search(odd_labels).run()['status'] == 'NONTHRACKLEABLE'
    report['input_validation_and_namespace_collisions'] = 'PASS'
    report['passed'] = True
    (ROOT / 'test_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print('ALL CHECKS PASSED', flush=True)


if __name__ == '__main__':
    main()
