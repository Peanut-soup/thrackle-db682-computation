#!/usr/bin/env python3
"""Compare native prefix graphs with a separate NetworkX construction.

Run after generation. This is a deterministic sample check, not a replacement
for the exhaustive run or a formal verification of the planarity libraries.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

import networkx as nx
import language_io as codec

DB=codec.C8+(2,)
START=(0,1,3,4,5,6,7,0,0)
END=(1,2,2,3,4,5,6,7,8)


def crossing(e,f):
    return ('cross',min(e,f),max(e,f))


def reference_prefix(rows,complete):
    """Build using tagged path nodes and neighborhoods, not native arm arrays."""
    graph=nx.Graph()
    graph.add_nodes_from(('vertex',v) for v in range(9))
    paths={}
    for e,row in enumerate(rows):
        path=[('vertex',START[e])]
        for k,f in enumerate(row):
            if k: path.append(('mid',e,k))
            path.append(crossing(e,f))
        if e!=8 or complete: path.append(('vertex',END[e]))
        paths[e]=path
        graph.add_nodes_from(path)
        graph.add_edges_from(zip(path,path[1:]))
    pairs={crossing(e,f) for e,row in enumerate(rows) for f in row}
    for x in pairs:
        e,f=x[1:]
        neighborhoods=[]
        for edge in (e,f):
            path=paths[edge]; at=path.index(x)
            neighborhoods.append(path[max(0,at-1):at]+path[at+1:at+2])
        graph.add_edges_from((a,b) for a in neighborhoods[0] for b in neighborhoods[1])
    return graph


def native_node_tags(rows):
    # The native probe numbers vertices by first crossing encounter, then by
    # subdivision encounter. This translates IDs only; reference_prefix does
    # not use those IDs or the native list of edges to construct its graph.
    tags=[('vertex',v) for v in range(9)]
    tags.extend(crossing(e,f) for e,row in enumerate(rows) for f in row if e<f)
    tags.extend(('mid',e,k) for e,row in enumerate(rows) for k in range(1,len(row)))
    return tags


def as_local(c8_system):
    return [[DB.index(f) for f in row] for row in c8_system]+[[]]


def full_augmentation(rows):
    graph=nx.Graph(); paths={}
    for e,row in rows.items():
        u,v=codec.ORIENTED[e]; path=[('vertex',u)]
        for k,f in enumerate(row):
            if k: path.append(('mid',e,k))
            path.append(crossing(e,f))
        path.append(('vertex',v)); paths[e]=path
        graph.add_edges_from(zip(path,path[1:]))
    for x in {crossing(e,f) for e,row in rows.items() for f in row}:
        e,f=x[1:]; pe,pf=paths[e],paths[f]; ie,jf=pe.index(x),pf.index(x)
        graph.add_edges_from((a,b) for a in (pe[ie-1],pe[ie+1]) for b in (pf[jf-1],pf[jf+1]))
    return graph


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results',type=Path,required=True)
    parser.add_argument('--native',type=Path,default=Path(__file__).with_name('h2_native.exe' if sys.platform=='win32' else 'h2_native'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists(): raise FileExistsError('Choose a new report filename')
    c8raw=(args.results/'c8.raw').read_bytes(); h2raw=(args.results/'h2.raw').read_bytes()
    if codec.sha(c8raw)!=codec.C8_HASH or codec.sha(h2raw)!=codec.H2_HASH:
        raise ValueError('Unexpected language data')
    c8=codec.decode_c8(c8raw); records=codec.decode_h2(h2raw,len(c8))
    rng=random.Random(20260910); cases=[]
    # Both unconstrained candidates (including nonplanar ones) and known
    # realizable full systems are checked at every possible prefix depth.
    for depth in range(7):
        for _ in range(60):
            rows=as_local(rng.choice(c8)); order=rng.sample(range(1,7),depth)
            for q in order: rows[q].insert(rng.randrange(6),8)
            rows[8]=order
            cases.append((rows,depth==6,'unconstrained'))
    for record in rng.sample(list(records),40):
        parent,stored,gaps=record
        chronological=[DB.index(f) for f in reversed(stored)]
        for depth in range(7):
            rows=as_local(c8[parent]); rows[8]=chronological[:depth]
            for q in rows[8]: rows[q].insert(gaps[q-1],8)
            cases.append((rows,depth==6,'realizable'))
    tokens=[str(len(cases))]
    for rows,complete,_ in cases:
        tokens.append(str(int(complete)))
        for row in rows: tokens.append(' '.join(map(str,[len(row)]+row)))
    with tempfile.TemporaryDirectory(prefix='thrackle-native-check-') as temporary:
        temp=Path(temporary); probe_in=temp/'input.txt'; probe_out=temp/'output.txt'
        probe_in.write_text('\n'.join(tokens)+'\n',encoding='ascii')
        subprocess.run([str(args.native.resolve()),'--probe',str(probe_in),str(probe_out)],check=True)
        native_lines=probe_out.read_text().splitlines()
        if len(native_lines)!=len(cases): raise ValueError('Wrong probe result count')
        outcomes=Counter()
        for case,line in zip(cases,native_lines):
            rows,complete,kind=case; answer,n,m,*endpoints=map(int,line.split())
            if len(endpoints)!=2*m: raise ValueError('Truncated native graph')
            tags=native_node_tags(rows); reference=reference_prefix(rows,complete)
            if len(tags)!=n or set(tags)!=set(reference): raise ValueError('Vertex set mismatch')
            actual={frozenset((tags[u],tags[v])) for u,v in zip(endpoints[::2],endpoints[1::2])}
            expected={frozenset(edge) for edge in reference.edges()}
            if actual!=expected: raise ValueError('Augmentation edge set mismatch')
            planar,embedding=nx.check_planarity(reference)
            if bool(answer)!=planar: raise ValueError('Boost/NetworkX planarity disagreement')
            if planar: embedding.check_structure()
            if kind=='realizable' and not planar: raise ValueError('Realizable system prefix rejected')
            outcomes['planar' if planar else 'nonplanar']+=1
        # Invalid row input must fail instead of returning a success result.
        probe_in.write_text('1\n0\n1 0\n'+'0\n'*8,encoding='ascii')
        bad=subprocess.run([str(args.native.resolve()),'--probe',str(probe_in),str(probe_out)],capture_output=True,text=True)
        if bad.returncode==0: raise ValueError('Malformed probe unexpectedly accepted')
    for record in rng.sample(list(records),100):
        rows=codec.complete_h2(record,c8); reflected=codec.reflect(rows)
        codec.validate_rows(reflected,codec.H5)
        for system in (rows,reflected):
            planar,embedding=nx.check_planarity(full_augmentation(system))
            if not planar: raise ValueError('Full H2/H5 realization failed independent planarity check')
            embedding.check_structure()
    if outcomes['nonplanar']==0: raise ValueError('Missing negative controls')
    report={'status':'PASS','random_seed':20260910,'prefix_graphs_compared':len(cases),
            'prefix_depths_checked':list(range(7)),'native_graph_vertex_and_edge_sets_equal':True,
            'boost_networkx_planarity_agreement':True,'outcomes':dict(outcomes),
            'malformed_probe_rejected':True,'independent_full_h2_checks':100,
            'independent_full_h5_checks':100,'source_sha256':codec.sha(Path(__file__).read_bytes()),
            'native_sha256':codec.sha(args.native.read_bytes()),'networkx':nx.__version__,
            'scope':'Deterministic differential samples and controls, not formal verification.'}
    with args.output.open('x',encoding='utf-8') as target: json.dump(report,target,indent=2); target.write('\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    try: main()
    except Exception as error:
        print(f'FAILED: {error}',file=sys.stderr); sys.exit(1)
