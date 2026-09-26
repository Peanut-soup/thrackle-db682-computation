"""Matched C6-extension benchmark. Run: python benchmark.py

Original search sources are bundled unchanged. This adapter fixes an input C6
restriction, translates orientations, and observes counters/deadlines only.
Each interval rate is descriptive progress, not an overall runtime speedup.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
from datetime import datetime, timezone
from decimal import Decimal, localcontext
import csv
import hashlib
import importlib.util
import json
from math import factorial, prod
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback

import networkx as nx

ROOT = Path(__file__).resolve().parent
SOURCES = {
    'reconstruction': ROOT / 'sources/fulek_pach_reconstruction.py',
    'v0150': ROOT / 'sources/fulek_pach_thrackle_v0150_FINAL_23ae90.py',
}
EXPECTED_HASHES = {
    'reconstruction': 'b5898e978269307e54affe402da81daaac75345f4d558514b92c5f2458fbfb4f',
    'v0150': '23ae908626820dd3afaf1dbbc180619186e8bfcb417bf8a2bbcac2bb76369632',
}
FIXTURE = ROOT / 'cores.json'
EXPECTED_FIXTURE_CONTENT = '0758e25e0da46f445b5dea44869b168d02b71ff6279ce6320c57094654a222c3'
DEFAULT_CHECKPOINTS = (30, 120, 300, 600, 900)
DEFAULT_CORES = (0, 1, 3, 5)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(name):
    spec = importlib.util.spec_from_file_location('seeded_benchmark_' + name, SOURCES[name])
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def check_sources():
    for name, expected in EXPECTED_HASHES.items():
        if digest(SOURCES[name]) != expected:
            raise ValueError(f'{name}: source hash differs from the validated release.')
    if nx.__version__ != '3.3':
        raise ValueError('Use the tested NetworkX version: python -m pip install -r requirements.txt')


def validate_fixture(data):
    content = dict(data)
    content.pop('preparation_seconds', None)
    signature = hashlib.sha256(json.dumps(content, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if signature != EXPECTED_FIXTURE_CONTENT:
        raise ValueError('Shared C6 fixture differs from the independently checked inputs. Use --prepare.')


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
    temp.replace(path)


def number(value, scientific=False):
    with localcontext() as ctx:
        ctx.prec = 100
        if scientific and Decimal(value) == 0:
            return '0.' + '0' * 20 + 'E+0'
        return format(Decimal(value), '.20E' if scientific else '.20f')


def percentage(count, total):
    with localcontext() as ctx:
        ctx.prec = 100
        return format(Decimal(count) * 100 / Decimal(total), '.20f')


def rate(count, seconds):
    if seconds <= 0:
        return ''
    with localcontext() as ctx:
        ctx.prec = 100
        return number(Decimal(count) / Decimal(str(seconds)), True)


def c6_first_problem(fp, edge_list, core_edges):
    """Use the same labeled graph, and a genuine C6-first Euler traversal.

    The tuned v0.15 order need not be an Euler trail. It must NOT simply be
    installed as the published-method baseline's Euler traversal.
    """
    problem = fp.Problem(edge_list)
    core_graph = nx.Graph()
    core_graph.add_edges_from(problem.edges[e] for e in core_edges)
    tail_graph = nx.Graph()
    tail_graph.add_edges_from(pair for e, pair in enumerate(problem.edges) if e not in core_edges)
    odd = sorted(v for v, d in problem.graph.degree() if d % 2)
    if len(odd) != 2 or any(v not in core_graph for v in odd):
        raise ValueError('Expected DB(6,8,-2) with its C6 and additional path.')
    start = odd[0]
    walk = list(nx.eulerian_circuit(core_graph, source=start))
    walk += list(nx.eulerian_path(tail_graph, source=start))
    if any(a[1] != b[0] for a, b in zip(walk, walk[1:])):
        raise AssertionError('Seeded reconstruction order is not a continuous Euler trail.')
    problem.order = [problem.lookup[frozenset(pair)] for pair in walk]
    if len(problem.order) != len(problem.edges) or len(set(problem.order)) != len(problem.edges):
        raise AssertionError('Euler traversal does not contain each edge exactly once.')
    if set(problem.order[:6]) != set(core_edges):
        raise AssertionError('The C6 is not the first six edges.')
    problem.oriented = dict(zip(problem.order, walk))
    return problem


def translate_rows(rows, source_orientation, target_orientation):
    """Edge IDs are identical; reverse a row iff its host orientation flips."""
    output = {}
    for e, row in rows.items():
        a, b = tuple(source_orientation[e]), tuple(target_orientation[e])
        if a == b:
            output[e] = list(row)
        elif a == tuple(reversed(b)):
            output[e] = list(reversed(row))
        else:
            raise ValueError(f'Edge {e} has mismatched endpoints.')
    return output


def baseline_core(fp, fixture, core_index):
    problem = c6_first_problem(fp, fixture['edges'], fixture['core_edges'])
    vertex_map = {label: i for i, label in enumerate(problem.labels)}
    source_orientation = {int(e): tuple(vertex_map[v] for v in uv)
                          for e, uv in fixture['orientation'].items()}
    rows = {int(e): list(row) for e, row in fixture['cores'][core_index].items()}
    converted = translate_rows(rows, source_orientation, problem.oriented)
    if translate_rows(converted, problem.oriented, source_orientation) != rows:
        raise AssertionError('Core orientation conversion is not reversible.')
    full_rows = [converted.get(e, []) for e in range(len(problem.edges))]
    if not nx.is_planar(fp.augmented_prefix(problem, full_rows, 5, True)):
        raise AssertionError('Converted seed fails the independent C6 augmentation.')
    if not fp.c6_consistent(full_rows, fp.c6_constraints(problem)):
        raise AssertionError('Converted seed violates the published C6 restriction.')
    return problem, converted


def seeded_search(fp, problem, core, *, enumerate_all=False, prefix_pruning=True):
    """Preserve Search._visit's enumeration/prunes; only seed its initial state.

    Call the inherited run() for its existing interruption, witness and exact
    coverage behavior, redirecting its first call past the supplied prefix.
    """
    k = len(core)
    if not 0 < k <= len(problem.order) or set(problem.order[:k]) != set(core):
        raise ValueError('Seed must be a complete initial set of activated edges.')
    for e in core:
        needed = set(problem.nonincident[e]).intersection(core)
        if len(core[e]) != len(needed) or set(core[e]) != needed:
            raise ValueError(f'Seed row {e} is not complete on the selected subgraph.')

    class SeededSearch(fp.Search):
        def _visit(self, stage, remaining):
            if stage == 0:
                if k == len(self.problem.order):
                    return super()._visit(k - 1, ())
                return super()._visit(k, self.older[k])
            return super()._visit(stage, remaining)

    search = SeededSearch(problem, use_c6=True, prefix_pruning=prefix_pruning,
                          enumerate_all=enumerate_all, progress=0)
    seed_patterns = prod(factorial(len(set(problem.nonincident[e]).intersection(core))) for e in core)
    if search.suffix[k] * seed_patterns != problem.total:
        raise AssertionError('Seeded extension denominator failed independent factorization.')
    problem.total = search.suffix[k]
    for e, row in core.items():
        search.pi[e] = list(row)
    return search


def prepare_fixture():
    check_sources()
    module = load('v0150')
    graph = module.DB(6, 8, -2)
    order = module.db682_candidate_activation_orders(graph, limit=1)[0]
    print('Enumerating the eight C6 seeds once; this is outside all timed runs.', flush=True)
    started = time.perf_counter()
    cores, core_edges = module.enumerate_planar_c6_cores(graph, activation_order=order, planarity='networkx')
    _, orientation = graph.euler_walk()
    representatives, orbits = module._db682_core_orbits(cores)
    data = {
        'format': 1, 'graph': 'DB(6,8,-2)', 'source_hashes': EXPECTED_HASHES,
        'edges': [[e.u, e.v] for e in graph.edges], 'v0150_order': order,
        'orientation': orientation, 'core_edges': core_edges,
        'cores': cores, 'representatives': representatives, 'reflection_orbits': orbits,
        'full_total': graph.candidate_count(), 'core_total': graph.candidate_count() // 46656,
        'raw_c6_patterns': 46656, 'preparation_seconds': time.perf_counter() - started,
    }
    fp = load('reconstruction')
    for i in range(8):
        p, core = baseline_core(fp, json.loads(json.dumps(data)), i)
        search = seeded_search(fp, p, core)
        if search.problem.total != data['core_total']:
            raise AssertionError('Denominators differ between programs.')
    validate_fixture(json.loads(json.dumps(data)))
    write_json(FIXTURE, data)
    print('Prepared all eight cores; checked planarity, directions and both denominators.', flush=True)
    return data


class BenchmarkTimeout(BaseException):
    """Escape both algorithms without their ordinary failure handlers swallowing it."""


class Recorder:
    """Commit exact counts at measured event times; never backdate a large prune.

    Every counter change is observed. When a checkpoint falls inside a long
    computation, its resolved count is the old count, because that computation
    had not yet credited any leaves. Checkpoint output may arrive late; it does
    not attribute the later result to the earlier boundary.
    """
    def __init__(self, seconds, checkpoints, total, path, label, clock=time.perf_counter):
        self.clock = clock
        self.started = clock()
        self.seconds, self.total, self.path, self.label = seconds, total, path, label
        self.checkpoints = sorted(set([0.0, seconds] + [float(t) for t in checkpoints if 0 < t < seconds]))
        self.index = 1
        self.resolved = 0
        self.planarity_calls = 0
        self.phase = 'setup'
        self.phase_times = [{'elapsed_seconds': 0.0, 'phase': self.phase}]
        self.samples = [self.sample(0.0, 0.0, 'start')]
        self.next_heartbeat = 5.0
        self.get_calls = lambda: 0
        self.publish()

    def sample(self, elapsed, observed, kind):
        return {'elapsed_seconds': elapsed, 'observed_seconds': observed,
                'recording_delay_seconds': max(0, observed - elapsed), 'kind': kind,
                'phase': self.phase, 'resolved_exact': str(self.resolved),
                'total_exact': str(self.total), 'percent_resolved': percentage(self.resolved, self.total)}

    def publish(self):
        write_json(self.path, {'label': self.label, 'phase': self.phase,
                             'elapsed_seconds': self.clock() - self.started,
                             'planarity_tests_observed': self.planarity_calls,
                             'resolved_exact': str(self.resolved), 'total_exact': str(self.total),
                             'percent_resolved': percentage(self.resolved, self.total),
                             'checkpoints': self.samples})

    def observe(self):
        elapsed = self.clock() - self.started
        changed = self.capture_checkpoints(elapsed)
        if changed or elapsed >= self.next_heartbeat:
            self.publish()
            print(f'{self.label} | {elapsed:.1f}s | {self.phase} | '
                  f'{percentage(self.resolved, self.total)}% | '
                  f'planarity tests {self.planarity_calls}', flush=True)
            self.next_heartbeat = elapsed + 5.0
        return elapsed

    def capture_checkpoints(self, elapsed):
        changed = False
        while self.index < len(self.checkpoints) and self.checkpoints[self.index] <= elapsed:
            target = self.checkpoints[self.index]
            self.samples.append(self.sample(target, elapsed, 'checkpoint'))
            self.index += 1
            changed = True
        return changed

    def guard(self):
        self.observe()
        if self.clock() - self.started >= self.seconds:
            self.capture_checkpoints(self.clock() - self.started)
            raise BenchmarkTimeout('Per-core wall-clock limit reached.')

    def credit(self, new_total):
        self.guard()
        if not self.resolved <= new_total <= self.total:
            raise AssertionError('Resolved count decreased or exceeded the seeded space.')
        # Observation can perform I/O. Check boundaries again after it, so a
        # slow progress write cannot backdate the next credit across a boundary.
        while True:
            elapsed = self.clock() - self.started
            if self.capture_checkpoints(elapsed):
                continue
            if elapsed >= self.seconds:
                raise BenchmarkTimeout('Per-core wall-clock limit reached.')
            break
        self.resolved = new_total

    def set_phase(self, phase):
        self.guard()
        self.phase = phase
        self.phase_times.append({'elapsed_seconds': self.clock() - self.started, 'phase': phase})

    def finish(self, status):
        elapsed = self.observe()
        endpoint = min(elapsed, self.seconds)
        if endpoint > self.samples[-1]['elapsed_seconds']:
            self.samples.append(self.sample(endpoint, elapsed, 'finish'))
        self.phase = status
        self.publish()
        return elapsed


def intervals(samples):
    rows = []
    for a, b in zip(samples, samples[1:]):
        duration = b['elapsed_seconds'] - a['elapsed_seconds']
        gain = int(b['resolved_exact']) - int(a['resolved_exact'])
        total = int(b['total_exact'])
        with localcontext() as ctx:
            ctx.prec = 100
            pp = Decimal(gain) * 100 / Decimal(total)
        rows.append({'start_seconds': a['elapsed_seconds'], 'end_seconds': b['elapsed_seconds'],
                     'duration_seconds': duration, 'start_percent': a['percent_resolved'],
                     'end_percent': b['percent_resolved'], 'resolved_gain_exact': str(gain),
                     'resolved_gain_scientific': number(gain, True),
                     'percentage_point_gain_scientific': number(pp, True),
                     'resolved_per_second': rate(gain, duration),
                     'end_phase': b['phase'], 'end_kind': b['kind']})
    return rows


def run_worker(program, core_index, seconds, checkpoints, output):
    check_sources()
    fixture = json.loads(FIXTURE.read_text(encoding='utf-8'))
    validate_fixture(fixture)
    module = load(program)  # imports excluded, as documented, for both methods
    total = int(fixture['core_total'])
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    recorder = Recorder(seconds, checkpoints, total, output / 'live.json', f'{program} core {core_index}')
    started_cpu = time.process_time()
    state = {'search': None}
    raw = None
    error = None
    original_nx_planar = nx.is_planar

    def guarded_planar(graph, *args, **kwargs):
        recorder.guard()
        recorder.planarity_calls += 1
        result = original_nx_planar(graph, *args, **kwargs)
        recorder.guard()
        return result

    nx.is_planar = guarded_planar
    status, reason = 'ERROR', 'Worker did not finish.'
    try:
        if program == 'reconstruction':
            problem, core = baseline_core(module, fixture, core_index)
            search = seeded_search(module, problem, core)
            if problem.total != total:
                raise AssertionError('Reconstruction denominator differs from shared core denominator.')
            state['search'] = search
            recorder.get_calls = lambda: search.stats.calls

            class ObservedStatistics(module.Statistics):
                def __setattr__(self, key, value):
                    if key == 'resolved' and hasattr(self, 'observer'):
                        self.observer.credit(value)
                    super().__setattr__(key, value)

            search.stats = ObservedStatistics(**asdict(search.stats))
            search.stats.observer = recorder
            check = search._check

            def checked():
                recorder.guard()
                check()

            search._check = checked
            recorder.set_phase('search')
            raw = search.run()
            if raw['status'] == 'NONTHRACKLEABLE' and raw['exhausted']:
                status = 'COMPLETE_NEGATIVE'
            elif raw['status'] == 'THRACKLEABLE':
                status = 'WITNESS_FOUND'
            else:
                status = 'ERROR'
            reason = raw['reason']
        else:
            init = module.DB682FactorizedSearch.__init__
            domains = module._db682_build_local_domains
            seeded = module.DB682FactorizedSearch.run_seeded_factorized
            check = module.BacktrackingSearch._check_limits
            mark = module.BacktrackingSearch._mark_resolved

            def observed_init(self, *args, **kwargs):
                recorder.set_phase('language tables and search setup')
                init(self, *args, **kwargs)
                state['search'] = self
                recorder.get_calls = lambda: self.stats.recursive_calls
                recorder.guard()

            def observed_domains(self, *args, **kwargs):
                recorder.set_phase('local-domain setup')
                return domains(self, *args, **kwargs)

            def observed_seeded(self, *args, **kwargs):
                recorder.set_phase('search')
                return seeded(self, *args, **kwargs)

            def observed_check(self):
                recorder.guard()
                check(self)

            def observed_mark(self, count, cause):
                recorder.credit(self.stats.resolved_candidates + count)
                mark(self, count, cause)

            module.DB682FactorizedSearch.__init__ = observed_init
            module._db682_build_local_domains = observed_domains
            module.DB682FactorizedSearch.run_seeded_factorized = observed_seeded
            module.BacktrackingSearch._check_limits = observed_check
            module.BacktrackingSearch._mark_resolved = observed_mark
            # Use the actual release worker and its actual production defaults.
            raw = module._db682_core_worker({
                'core_index': core_index, 'represented_cores': [core_index],
                'core_pi': fixture['cores'][core_index], 'core_edges': fixture['core_edges'],
                'order': fixture['v0150_order'], 'planarity': 'networkx', 'planarity_workers': 1,
                'max_calls': None, 'time_limit': None, 'debug': False,
            })
            status = {'NONTHRACKLEABLE': 'COMPLETE_NEGATIVE', 'THRACKLEABLE': 'WITNESS_FOUND',
                      'ERROR': 'ERROR', 'INCONCLUSIVE': 'ERROR'}[raw['status']]
            reason = raw.get('error') or raw['reason']
            if state['search'] is not None and state['search'].stats.total_candidates != total:
                raise AssertionError('v0.15.0 denominator differs from shared core denominator.')
        if status == 'COMPLETE_NEGATIVE' and recorder.resolved != total:
            raise AssertionError('Negative result without full exact seeded coverage.')
        if status == 'ERROR':
            error = reason
    except BenchmarkTimeout as exc:
        status, reason = 'TIME_LIMIT', str(exc)
    except KeyboardInterrupt:
        status, reason = 'INTERRUPTED', 'User interrupted this run.'
    except BaseException:
        status, reason = 'ERROR', 'Benchmark or program failure.'
        error = traceback.format_exc()
    finally:
        nx.is_planar = original_nx_planar
    elapsed = recorder.finish(status)
    cpu_seconds = time.process_time() - started_cpu
    search = state['search']
    order = (search.problem.order if program == 'reconstruction' else search.order) if search else None
    stats = asdict(search.stats) if search else None
    orient = ((search.problem.oriented if program == 'reconstruction' else search.oriented)
              if search else None)
    result = {
        'program': program, 'core': core_index, 'status': status, 'reason': reason, 'error': error,
        'time_budget_seconds': seconds, 'elapsed_seconds': elapsed, 'cpu_seconds': cpu_seconds,
        'planarity_tests_observed': recorder.planarity_calls,
        'complete_seconds': elapsed if status == 'COMPLETE_NEGATIVE' else None,
        'resolved_exact': str(recorder.resolved), 'total_exact': str(total),
        'percent_resolved': percentage(recorder.resolved, total),
        'samples': recorder.samples, 'intervals': intervals(recorder.samples),
        'phase_times': recorder.phase_times, 'activation_order': order, 'orientation': orient,
        'stats': stats, 'raw_result': raw, 'source_sha256': digest(SOURCES[program]),
        'fixture_sha256': digest(FIXTURE), 'harness_sha256': digest(__file__),
        'networkx': nx.__version__, 'python': sys.version, 'platform': platform.platform(),
        'workers': 1, 'reflection_credit': 1,
        'timing': 'After imports and common seed generation; includes all per-run preparation, language loading and local domains. Frozen language generation excluded.',
        'counter_meaning': 'Distinct complete extensions resolved; not physical planarity tests or time remaining.',
    }
    write_json(output / 'result.json', result)
    print(f'{program} core {core_index}: {status}, {percentage(recorder.resolved, total)}%', flush=True)
    return 0 if status in ('COMPLETE_NEGATIVE', 'TIME_LIMIT') else 2


def paired_comparison(a, b):
    """a = reconstruction, b = v0150. Never ratio unfinished coverage."""
    if a['total_exact'] != b['total_exact'] or a['core'] != b['core']:
        raise ValueError('Cannot compare mismatched seeded problems.')
    sa, sb = a['status'], b['status']
    if sa == sb == 'COMPLETE_NEGATIVE':
        ratio = a['complete_seconds'] / b['complete_seconds']
        return {'kind': 'completion_time_ratio', 'ratio_reconstruction_over_v0150': ratio,
                'description': f'{ratio:.6g}x (measured completion-time ratio)'}
    if sa == 'TIME_LIMIT' and sb == 'COMPLETE_NEGATIVE':
        ratio = a['time_budget_seconds'] / b['complete_seconds']
        return {'kind': 'lower_bound', 'ratio_reconstruction_over_v0150': ratio,
                'description': f'greater than {ratio:.6g}x (reconstruction timed out)'}
    if sa == 'COMPLETE_NEGATIVE' and sb == 'TIME_LIMIT':
        ratio = a['complete_seconds'] / b['time_budget_seconds']
        return {'kind': 'upper_bound', 'ratio_reconstruction_over_v0150': ratio,
                'description': f'less than {ratio:.6g}x (v0.15.0 timed out)'}
    return {'kind': 'not_established', 'description': 'No completion-time speedup established.'}


def save_unfinished_job(directory, job, seconds, total, status, reason):
    """A watchdog stop or crash must remain explicit, never silently omitted."""
    path = directory / 'result.json'
    if path.exists():
        return
    live = directory / 'live.json'
    snapshot = json.loads(live.read_text(encoding='utf-8')) if live.exists() else {}
    count = snapshot.get('resolved_exact', '0')
    write_json(path, {'program': job['program'], 'core': job['core'], 'status': status,
                     'reason': reason, 'error': reason, 'time_budget_seconds': seconds,
                     'elapsed_seconds': snapshot.get('elapsed_seconds', 0),
                     'complete_seconds': None, 'resolved_exact': count, 'total_exact': str(total),
                     'percent_resolved': percentage(int(count), total), 'intervals': [],
                     'samples': snapshot.get('checkpoints', []),
                     'note': 'Only the last saved observation is available; this is not a completed measurement.'})


def make_report(output, plan):
    rows, results, paired = [], [], []
    for job in plan['jobs']:
        path = output / job['directory'] / 'result.json'
        if path.exists():
            result = json.loads(path.read_text(encoding='utf-8'))
            result['repeat'] = job['repeat']
            results.append(result)
            for row in result.get('intervals', []):
                rows.append({'repeat': job['repeat'], 'core': job['core'], 'program': job['program'],
                             'run_status': result['status'], **row})
    if rows:
        with (output / 'intervals.csv').open('w', newline='', encoding='utf-8') as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    index = {(r['repeat'], r['core'], r['program']): r for r in results}
    lines = ['SEEDED C6 COMPARISON', '',
             'All percentages concern extensions of ONE fixed C6 core, starting from zero.',
             'Interval rates are observed progress. They do not estimate completion time.',
             'Both programs use NetworkX 3.3, one worker, separate sequential processes.',
             'Per-run setup is timed. Common C6 enumeration and frozen-language generation are excluded.',
             'Reflection copies are NOT credited. Source, fixture, settings and environment are recorded.', '',
             'FINAL RESULTS']
    for r in results:
        lines.append(f"repeat {r['repeat']} | core {r['core']} | {r['program']} | {r['status']} | "
                     f"{r['elapsed_seconds']:.3f}s | {r['percent_resolved']}%")
        search_start = next((p['elapsed_seconds'] for p in r.get('phase_times', []) if p['phase'] == 'search'), None)
        lines.append(f'  Setup before main search: {search_start:.3f}s' if search_start is not None
                     else '  Main search did not start, or its start time was not saved.')
    lines.extend(['', 'PAIRED COMPLETION COMPARISONS'])
    for repeat in range(1, plan['repeats'] + 1):
        for core in plan['cores']:
            a, b = (index.get((repeat, core, p)) for p in ('reconstruction', 'v0150'))
            if a and b:
                comparison = paired_comparison(a, b)
                paired.append({'repeat': repeat, 'core': core, **comparison})
                lines.append(f"repeat {repeat} | core {core}: {comparison['description']}")
    for r in results:
        lines.extend(['', f"INTERVALS: repeat {r['repeat']}, core {r['core']}, {r['program']}"])
        for row in r.get('intervals', []):
            lines.append(f"{row['start_seconds']:g}-{row['end_seconds']:g}s | "
                         f"{row['start_percent']}% -> {row['end_percent']}% | "
                         f"gain {row['percentage_point_gain_scientific']} percentage points | "
                         f"{row['resolved_per_second']} resolved systems/s | {row['end_phase']}")
    lines.extend(['', 'INTERPRETATION',
                 'The baseline is an independent reconstruction initialized with a C6 seed and a C6-first Euler trail.',
                 'These are not timings of Fulek and Pach\'s original software.',
                 'The four default cores are a specified sample of eight. Mathematical reflection symmetry does not',
                 'prove identical runtimes on their partners. Use --cores all to measure all eight.',
                 'Large later prunes can still cause jumps. Compare all interval rows, not just the best interval.',
                 'One pass is descriptive; --repeats 3 provides repeated observations if more runtime is available.',
                 'No fixed x-fold overall speedup or asymptotic complexity change follows from unfinished progress.'])
    (output / 'report.txt').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    write_json(output / 'summary.json', {'plan': plan, 'results': results, 'paired_comparisons': paired})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=900, help='Wall budget per program/core; default 900')
    parser.add_argument('--cores', default='0,1,3,5', help='Comma-separated core indices, or all')
    parser.add_argument('--repeats', type=int, default=1)
    parser.add_argument('--checkpoints', default='30,120,300,600,900')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--prepare', action='store_true', help='Regenerate and validate all eight shared C6 seeds')
    parser.add_argument('--summarize', type=Path, help='Rebuild a report from an existing run folder')
    parser.add_argument('--worker', choices=list(SOURCES), help=argparse.SUPPRESS)
    parser.add_argument('--core', type=int, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.summarize:
        folder = args.summarize.resolve()
        make_report(folder, json.loads((folder / 'run_plan.json').read_text(encoding='utf-8')))
        return 0
    check_sources()
    if args.prepare:
        prepare_fixture()
        return 0
    if not FIXTURE.exists():
        prepare_fixture()
    fixture = json.loads(FIXTURE.read_text(encoding='utf-8'))
    validate_fixture(fixture)
    if fixture['source_hashes'] != EXPECTED_HASHES:
        raise ValueError('Shared core fixture belongs to different source versions.')
    if args.seconds <= 0 or not args.seconds < float('inf') or args.repeats < 1:
        parser.error('Use positive finite seconds and at least one repeat.')
    checkpoints = [float(t) for t in args.checkpoints.split(',')]
    if any(t <= 0 or not t < float('inf') for t in checkpoints):
        parser.error('Checkpoint seconds must be positive and finite.')
    if args.worker:
        return run_worker(args.worker, args.core, args.seconds, checkpoints, args.output)
    cores = list(range(8)) if args.cores == 'all' else [int(i) for i in args.cores.split(',')]
    if not cores or len(set(cores)) != len(cores) or any(i not in range(8) for i in cores):
        parser.error('Use distinct core indices from 0 to 7, or all.')
    output = (args.output or ROOT / 'runs' / datetime.now().strftime('%Y%m%d_%H%M%S')).resolve()
    output.mkdir(parents=True, exist_ok=True)
    plan_path = output / 'run_plan.json'
    if plan_path.exists():
        parser.error('Output folder already contains a run. Choose a fresh folder to avoid overwriting measurements.')
    jobs = []
    for repeat in range(1, args.repeats + 1):
        for position, core in enumerate(cores):
            programs = ['reconstruction', 'v0150']
            if (repeat - 1 + position) % 2:
                programs.reverse()
            for program in programs:
                jobs.append({'repeat': repeat, 'core': core, 'program': program,
                             'directory': f'repeat_{repeat}_core_{core}_{program}'})
    plan = {'started_utc': datetime.now(timezone.utc).isoformat(), 'cores': cores,
            'repeats': args.repeats, 'seconds_each': args.seconds, 'checkpoints': checkpoints,
            'jobs': jobs, 'source_hashes': EXPECTED_HASHES, 'fixture_sha256': digest(FIXTURE),
            'harness_sha256': digest(__file__), 'python': sys.version, 'networkx': nx.__version__,
            'platform': platform.platform(), 'processor': platform.processor(),
            'logical_processors': os.cpu_count(), 'shared_core_total_exact': str(fixture['core_total']),
            'sequential': True, 'balanced_program_order': True, 'multiplicity': 1}
    write_json(plan_path, plan)
    print(f'{len(jobs)} sequential runs, up to {len(jobs) * args.seconds / 60:g} timed minutes.', flush=True)
    print(f'Results: {output}\nKeep the computer plugged in and awake. Ctrl+C stops the suite.', flush=True)
    process = None
    try:
        for j, job in enumerate(jobs, 1):
            directory = output / job['directory']
            print(f"\nRun {j}/{len(jobs)}: {job['program']}, core {job['core']}", flush=True)
            command = [sys.executable, '-u', str(Path(__file__).resolve()), '--worker', job['program'],
                       '--core', str(job['core']), '--seconds', str(args.seconds),
                       '--checkpoints', args.checkpoints, '--output', str(directory)]
            process = subprocess.Popen(command)
            try:
                code = process.wait(timeout=args.seconds + 60)
            except subprocess.TimeoutExpired:
                process.terminate()
                process.wait(timeout=15)
                print('Worker exceeded its deadline grace period; no negative conclusion.', flush=True)
                save_unfinished_job(directory, job, args.seconds, fixture['core_total'],
                                    'FORCED_STOP', 'Worker exceeded wall deadline plus grace period.')
                code = 2
            if code != 0:
                save_unfinished_job(directory, job, args.seconds, fixture['core_total'],
                                    'ERROR', 'Worker exited before writing a final result.')
            make_report(output, plan)
            if code != 0:
                print('Stopped after an error, interruption, or unexpected witness. See the saved report.', flush=True)
                return 2
            process = None
    except KeyboardInterrupt:
        if process is not None and process.poll() is None:
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.terminate()
                process.wait(timeout=15)
        if process is not None:
            save_unfinished_job(directory, job, args.seconds, fixture['core_total'],
                                'INTERRUPTED', 'User stopped the suite before a final result was written.')
        make_report(output, plan)
        print('\nStopped. Completed runs and live snapshots remain saved.', flush=True)
        return 130
    print(f'\nDone. Read {output / "report.txt"}', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
