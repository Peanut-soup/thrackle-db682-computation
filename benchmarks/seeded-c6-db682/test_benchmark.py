"""Validate seeded enumeration, input conversion and interval accounting."""
import itertools
import json
from math import factorial, prod
from pathlib import Path
import sys
import unittest

import networkx as nx

import benchmark as b

sys.path.insert(0, str(b.ROOT / 'sources'))
import fulek_pach_reconstruction as fp
from test_reconstruction import exhaustive_oracle, key


class SeededEnumerationTests(unittest.TestCase):
    def check_partition(self, edges, prefix_size):
        template = fp.Problem(edges)
        valid = exhaustive_oracle(template)
        seed_edges = template.order[:prefix_size]
        choices = [list(itertools.permutations(sorted(set(template.nonincident[e]).intersection(seed_edges))))
                   for e in seed_edges]
        found, examined, partitions = set(), 0, 0
        for selected in itertools.product(*choices):
            core = dict(zip(seed_edges, selected))
            expected = {rows for rows in valid if all(
                tuple(f for f in rows[e] if f in core) == tuple(core[e]) for e in core)}
            for pruning in (True, False):
                problem = fp.Problem(edges)
                search = b.seeded_search(fp, problem, core, enumerate_all=True, prefix_pruning=pruning)
                result = search.run()
                self.assertTrue(result['exhausted'], result)
                self.assertEqual(result['statistics']['resolved'], problem.total)
                self.assertEqual({key(row) for row in result['witnesses']}, expected)
                for e in range(len(problem.edges)):
                    self.assertEqual(search.pi[e], list(core.get(e, [])))
                if not pruning:
                    self.assertEqual(result['statistics']['complete_tests'], problem.total)
            self.assertFalse(found.intersection(expected))
            found.update(expected)
            examined += result['statistics']['resolved']
            partitions += 1
        self.assertEqual(found, valid)
        self.assertEqual(examined, template.total)
        return partitions

    def test_all_seeded_leaves_partition_small_graphs(self):
        for edges in (fp.cycle(5), fp.dumbbell(3, 3, 0), fp.dumbbell(3, 4, -1)):
            for prefix in (2, 3, len(edges)):
                with self.subTest(edges=edges, prefix=prefix):
                    self.check_partition(edges, prefix)

    def test_invalid_seed_rejected(self):
        with self.assertRaises(ValueError):
            b.seeded_search(fp, fp.Problem(fp.cycle(5)), {0: []})

    def test_orientation_round_trip(self):
        rows = {0: [1, 2, 3], 1: [4, 5]}
        source = {0: (0, 1), 1: (2, 3)}
        target = {0: (1, 0), 1: (2, 3)}
        converted = b.translate_rows(rows, source, target)
        self.assertEqual(converted, {0: [3, 2, 1], 1: [4, 5]})
        self.assertEqual(b.translate_rows(converted, target, source), rows)


class RealCoreTests(unittest.TestCase):
    def test_all_eight_real_inputs_and_denominators(self):
        data = json.loads(b.FIXTURE.read_text())
        b.validate_fixture(data)
        v = b.load('v0150')
        graph = v.DB(6, 8, -2)
        self.assertEqual(len(data['cores']), 8)
        self.assertEqual(data['representatives'], [0, 1, 3, 5])
        for index in range(8):
            with self.subTest(core=index):
                p, core = b.baseline_core(fp, data, index)
                s = b.seeded_search(fp, p, core)
                self.assertEqual(s.stats.resolved, 0)
                self.assertEqual(p.total, data['core_total'])
                full = {int(e): row for e, row in data['cores'][index].items()}
                template = v.BacktrackingSearch(graph, use_c6_restriction=False, use_screening=False,
                    incremental_partial=False, progress_interval_seconds=None, planarity_backend='networkx',
                    activation_order='custom', custom_activation_order=data['v0150_order'])
                self.assertEqual(v._seed_search_with_core(template, full, data['core_edges']), p.total)
                self.assertEqual(template.stats.resolved_candidates, 0)
                # Independent count of permutations preserving each core-row order.
                count = prod(factorial(len(p.nonincident[e])) // factorial(len(core.get(e, [])))
                             for e in range(len(p.edges)))
                self.assertEqual(count, p.total)
                for e, uv in enumerate(p.edges):
                    self.assertEqual(set(uv), set(p.oriented[e]))

    def test_changed_fixture_is_rejected(self):
        data = json.loads(b.FIXTURE.read_text())
        data['cores'][0]['0'].reverse()
        with self.assertRaises(ValueError):
            b.validate_fixture(data)


class RecordingTests(unittest.TestCase):
    def test_late_prune_is_never_credited_early(self):
        now = [0.0]
        path = b.ROOT / 'validation' / 'recorder_test.json'
        rec = b.Recorder(10, [2, 5], 1000, path, 'test', clock=lambda: now[0])
        now[0] = 1
        rec.credit(10)
        now[0] = 3
        rec.credit(30)
        now[0] = 11
        with self.assertRaises(b.BenchmarkTimeout):
            rec.credit(900)
        rec.finish('TIME_LIMIT')
        self.assertEqual([float(s['elapsed_seconds']) for s in rec.samples], [0, 2, 5, 10])
        self.assertEqual([int(s['resolved_exact']) for s in rec.samples], [0, 10, 30, 30])
        intervals = b.intervals(rec.samples)
        self.assertEqual([int(r['resolved_gain_exact']) for r in intervals], [10, 20, 0])
        self.assertEqual(rec.resolved, 30)

    def test_speed_ratio_requires_completion(self):
        a = {'core': 0, 'total_exact': '100', 'status': 'TIME_LIMIT', 'time_budget_seconds': 900}
        other = dict(a)
        self.assertEqual(b.paired_comparison(a, other)['kind'], 'not_established')
        other.update(status='COMPLETE_NEGATIVE', complete_seconds=90)
        comparison = b.paired_comparison(a, other)
        self.assertEqual(comparison['kind'], 'lower_bound')
        self.assertEqual(comparison['ratio_reconstruction_over_v0150'], 10)

    def test_slow_progress_write_cannot_backdate_credit(self):
        now = [0.0]
        rec = b.Recorder(10, [2, 5], 100, b.ROOT / 'validation' / 'slow_write_test.json',
                         'slow-write', clock=lambda: now[0])
        rec.next_heartbeat = 1.5
        rec.publish = lambda: now.__setitem__(0, 2.1)
        now[0] = 1.9
        rec.credit(50)
        self.assertEqual(rec.samples[1]['elapsed_seconds'], 2)
        self.assertEqual(rec.samples[1]['resolved_exact'], '0')
        self.assertEqual(rec.resolved, 50)

    def test_crashed_job_is_explicit_in_report(self):
        import tempfile
        with tempfile.TemporaryDirectory() as location:
            folder = Path(location)
            job = {'program': 'reconstruction', 'core': 0, 'repeat': 1, 'directory': 'run'}
            b.save_unfinished_job(folder / 'run', job, 10, 100, 'FORCED_STOP', 'test watchdog')
            plan = {'jobs': [job], 'cores': [0], 'repeats': 1}
            b.make_report(folder, plan)
            self.assertIn('FORCED_STOP', (folder / 'report.txt').read_text())
            self.assertEqual(json.loads((folder / 'summary.json').read_text())['paired_comparisons'], [])

    def test_early_completion_has_only_elapsed_intervals(self):
        now = [0.0]
        rec = b.Recorder(10, [2, 5], 100, b.ROOT / 'validation' / 'early_test.json',
                         'early', clock=lambda: now[0])
        now[0] = 1
        rec.credit(100)
        now[0] = 1.1
        rec.finish('COMPLETE_NEGATIVE')
        self.assertEqual(len(rec.samples), 2)
        self.assertEqual(b.intervals(rec.samples)[0]['end_seconds'], 1.1)
        self.assertEqual(b.intervals(rec.samples)[0]['resolved_gain_exact'], '100')


if __name__ == '__main__':
    b.check_sources()
    unittest.main(verbosity=2)
