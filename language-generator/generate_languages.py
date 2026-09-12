#!/usr/bin/env python3
"""Generate C8 -> exhaustive H2 -> reflected H5 -> v0.15.0 data constants."""
import argparse
from datetime import datetime,timezone
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import time
import networkx as nx
import generate_c8 as c8gen
import language_io as codec

VERSION='1.1.0'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('results'))
    parser.add_argument('--seeds',type=Path,default=Path(__file__).with_name('seeds.json'))
    parser.add_argument('--native',type=Path,default=Path(__file__).with_name('h2_native.exe' if sys.platform=='win32' else 'h2_native'))
    parser.add_argument('--threads',type=int,default=4)
    parser.add_argument('--reference-release',type=Path,help='Optional frozen release, used only after generation')
    args=parser.parse_args()
    if args.output.exists(): raise FileExistsError('Choose a new output directory')
    if not args.native.is_file(): raise FileNotFoundError('Build h2_native.cpp first; see README.md')
    if not 1<=args.threads<=64: raise ValueError('threads must be between 1 and 64')
    started=time.perf_counter(); seed_bytes=args.seeds.read_bytes()
    seeds=json.loads(seed_bytes)
    components,c8stats=c8gen.regenerate([entry['rows'] for entry in seeds['seeds']])
    systems=sorted(c8gen.to_db682(s) for s in set().union(*components))
    c8raw=bytes(x for system in systems for row in system for x in row)
    if codec.sha(c8raw)!=codec.C8_HASH: raise RuntimeError('Unexpected canonical C8 bytes')
    args.output.mkdir(parents=True,exist_ok=False)
    out=args.output
    (out/'INCOMPLETE.txt').write_text('Generation is unfinished. Only run_report.json with status PASS certifies a completed run.\n',encoding='utf-8')
    (out/'c8.raw').write_bytes(c8raw)
    print('C8 complete. Generating all H2 extensions; progress follows.',flush=True)
    # stderr is inherited for live progress; stdout is a small final JSON report.
    native_source=Path(__file__).with_name('h2_native.cpp')
    native_hash=codec.sha(args.native.read_bytes())
    native_source_hash=codec.sha(native_source.read_bytes())
    process=subprocess.run([str(args.native.resolve()),str((out/'c8.raw').resolve()),
                            str((out/'h2.raw').resolve()),str(args.threads)],stdout=subprocess.PIPE,text=True)
    if process.returncode: raise RuntimeError('H2 worker failed; no successful report is produced')
    h2stats=json.loads(process.stdout)
    if h2stats['parents_completed']!=2544 or h2stats['start']!=0 or h2stats['end']!=2544:
        raise RuntimeError('H2 parent coverage incomplete')
    expected_mass=2544*math.factorial(6)*6**6
    if h2stats['raw_extensions_accounted']!=expected_mass:
        raise RuntimeError('H2 raw extension accounting failed')
    h2raw=(out/'h2.raw').read_bytes()
    if codec.sha(h2raw)!=codec.H2_HASH: raise RuntimeError('Unexpected generated H2 bytes')
    c8=codec.decode_c8(c8raw); records=codec.decode_h2(h2raw,len(c8))
    if len(records)!=60196 or h2stats['records']!=len(records): raise RuntimeError('Wrong H2 count')
    codec.validate_reflection()
    c8set=set(c8); seen_h5=set()
    with (out/'h2_records.jsonl').open('w',encoding='utf-8') as h2file, (out/'h5_systems.jsonl').open('w',encoding='utf-8') as h5file:
        for i,record in enumerate(records):
            rows=codec.complete_h2(record,c8); reflected=codec.reflect(rows)
            codec.validate_rows(reflected,codec.H5)
            if codec.reflect(reflected)!=rows: raise RuntimeError('H5 reflection is not invertible')
            projected=tuple(tuple(f for f in reflected[e] if f!=5) for e in codec.C8)
            if projected not in c8set: raise RuntimeError('Reflected H5 parent outside C8 language')
            key=tuple(reflected[e] for e in codec.H5)
            if key in seen_h5: raise RuntimeError('Duplicate H5 system')
            seen_h5.add(key)
            h2file.write(json.dumps({'parent':record[0],'edge2_row':record[1],'gaps':record[2]},separators=(',',':'))+'\n')
            h5file.write(json.dumps({'h2_record_index':i,'rows':key},separators=(',',':'))+'\n')
    text,values=codec.encode_blocks(c8raw,h2raw)
    (out/'v0150_data_blocks.py').write_text(text,encoding='utf-8',newline='\n')
    _,_,roundtrip=codec.read_literals(out/'v0150_data_blocks.py')
    if codec.unpack_values(roundtrip)!=(c8raw,h2raw): raise RuntimeError('Export round-trip failed')
    reference={'performed':False}
    if args.reference_release:
        reference=codec.compare_release(args.reference_release,c8raw,h2raw,values)
    c8gen.write_json(out/'data_schema.json',{
        'c8_row_order':codec.C8,'h2_row_order':codec.H2,'h5_row_order':codec.H5,
        'h2_gap_partner_order':codec.PARTNERS,'program_edge_orientations':codec.ORIENTED,
        'reflection_edge_map':codec.REFLECT,'reflection_vertex_map':codec.VERTEX_REFLECT,
        'c8_record_bytes':40,'h2_record_bytes':14,'h2_layout':'uint16 little-endian C8 parent; 6 edge IDs; 6 gaps',
        'h2_sort':'parent index, edge2 row, gaps','c8_sort':'lexicographic full row tuple in DB orientation',
        'h5_storage':'inspection output only; v0.15.0 pulls H5 support back to H2 by reflection',
        'encoding':'raw bytes -> zlib level 9 -> Python base85 ASCII -> adjacent string literals'})
    names=['c8.raw','h2.raw','h2_records.jsonl','h5_systems.jsonl','v0150_data_blocks.py','data_schema.json']
    report={'status':'PASS','version':VERSION,'finished_utc':datetime.now(timezone.utc).isoformat(),
            'seconds':round(time.perf_counter()-started,3),'python':platform.python_version(),
            'networkx':nx.__version__,'platform':platform.platform(),'c8':c8stats,'h2':h2stats,
            'h5':{'count':len(seen_h5),'all_rows_valid':True,'all_reflections_involutive':True,
                  'all_projected_c8_parents_present':True,'edge_and_vertex_automorphism_verified':True,
                  'independent_h5_search_needed':False},'reference_comparison':reference,
            'c8_raw_sha256':codec.sha(c8raw),'h2_raw_sha256':codec.sha(h2raw),
            'source_files_sha256':{name:codec.sha(Path(__file__).with_name(name).read_bytes()) for name in
                                    ('generate_languages.py','generate_c8.py','language_io.py','h2_native.cpp')},
            'native_executable_sha256':native_hash,'compiled_source_file_sha256':native_source_hash,
            'seeds_sha256':codec.sha(seed_bytes),'output_files_sha256':{name:codec.sha((out/name).read_bytes()) for name in names},
            'scope':'Seeded C8 regeneration conditional on the published classification; exhaustive H2 extensions with safe chronological-prefix minors; H5 by verified reflection. No DB exclusion search.'}
    c8gen.write_json(out/'run_report.json',report)
    (out/'INCOMPLETE.txt').unlink()
    print(json.dumps({'status':'PASS','c8':2544,'h2':len(records),'h5':len(seen_h5),
                      'reference':reference,'seconds':report['seconds']},indent=2),flush=True)

if __name__=='__main__':
    try: main()
    except (Exception,KeyboardInterrupt) as error:
        print(f'FAILED / INCONCLUSIVE: {error}',file=sys.stderr); sys.exit(1)
