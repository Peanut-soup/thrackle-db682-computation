"""v0.15.0 data contracts, deterministic encoders, and literal-only comparison."""
import ast
import base64
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace
import zlib

C8 = (0,1,11,10,9,8,7,6)
H2 = C8+(2,)
H5 = C8+(5,)
PARTNERS = (1,11,10,9,8,7)
REFLECT = {0:1,1:0,2:5,5:2,3:4,4:3,6:11,11:6,7:10,10:7,8:9,9:8}
ORIENTED = {0:('A','s1'),1:('s1','B'),2:('p1','A'),3:('p2','p1'),
            4:('p3','p2'),5:('B','p3'),6:('A','q1'),7:('q1','q2'),
            8:('q2','q3'),9:('q3','q4'),10:('q4','q5'),11:('q5','B')}
VERTEX_REFLECT = {'A':'B','B':'A','s1':'s1','p1':'p3','p2':'p2','p3':'p1',
                  'q1':'q5','q2':'q4','q3':'q3','q4':'q2','q5':'q1'}
EXPECTED = {e:{f for f in ORIENTED if not set(ORIENTED[e])&set(ORIENTED[f])} for e in ORIENTED}
RELEASE_HASH = '23ae908626820dd3afaf1dbbc180619186e8bfcb417bf8a2bbcac2bb76369632'
C8_HASH = '8e260f0471170ffad6490fa6debdfd06c52f153a67d9079525511c63df7c907e'
H2_HASH = '51e2f918b5749ef845d620546a66ceead75863d97061dc36ac5582e30d24590f'
NAMES = tuple('_DB682_'+kind+'_LANGUAGE_'+suffix for kind in ('C8','H2') for suffix in ('COUNT','RAW_SHA256','B85'))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def validate_rows(rows, selected):
    if set(rows)!=set(selected):
        raise ValueError('Wrong selected edge set')
    for e,row in rows.items():
        if any(type(f) is not int for f in row) or len(row)!=len(set(row)) or set(row)!=EXPECTED[e]&set(selected):
            raise ValueError(f'Incomplete or malformed row {e}')

def decode_c8(raw):
    if len(raw)%40:
        raise ValueError('C8 raw byte length is not divisible by 40')
    out=[]
    for offset in range(0,len(raw),40):
        system=tuple(tuple(raw[offset+5*i:offset+5*i+5]) for i in range(8))
        validate_rows(dict(zip(C8,system)),C8); out.append(system)
    if len(set(out))!=len(out) or out!=sorted(out):
        raise ValueError('C8 table must be distinct and lexicographically sorted in DB row convention')
    return tuple(out)

def decode_h2(raw, parent_count):
    if len(raw)%14:
        raise ValueError('H2 raw byte length is not divisible by 14')
    out=[]
    for offset in range(0,len(raw),14):
        parent=int.from_bytes(raw[offset:offset+2],'little')
        order=tuple(raw[offset+2:offset+8]); gaps=tuple(raw[offset+8:offset+14])
        if not 0<=parent<parent_count or set(order)!=set(PARTNERS) or any(g>5 for g in gaps):
            raise ValueError('Invalid H2 parent/order/gaps')
        out.append((parent,order,gaps))
    if len(set(out))!=len(out) or out!=sorted(out):
        raise ValueError('H2 records must be unique and sorted by parent, order, gaps')
    return tuple(out)

def complete_h2(record, c8):
    parent,order,gaps=record
    rows={e:list(row) for e,row in zip(C8,c8[parent])}
    for e,gap in zip(PARTNERS,gaps): rows[e].insert(gap,2)
    rows[2]=list(order)
    result={e:tuple(rows[e]) for e in H2}; validate_rows(result,H2)
    return result

def reflect(rows):
    return {REFLECT[e]:tuple(REFLECT[f] for f in reversed(row)) for e,row in rows.items()}

def validate_reflection():
    for e,(u,v) in ORIENTED.items():
        if REFLECT[REFLECT[e]]!=e or (VERTEX_REFLECT[u],VERTEX_REFLECT[v])!=ORIENTED[REFLECT[e]][::-1]:
            raise ValueError('Reflection does not preserve edges and reverse row orientations')

def encode_blocks(c8raw,h2raw):
    values={}; chunks=['# Generated from three C8 seeds and exhaustive H2 extension.\n# Replace only the six corresponding constants in v0.15.0.\n']
    for kind,raw,width in (('C8',c8raw,40),('H2',h2raw,14)):
        if len(raw)%width: raise ValueError('Malformed raw data')
        prefix='_DB682_'+kind+'_LANGUAGE_'
        blob=base64.b85encode(zlib.compress(raw,9)).decode('ascii')
        values.update({prefix+'COUNT':len(raw)//width,prefix+'RAW_SHA256':sha(raw),prefix+'B85':blob})
        chunks.append(f'{prefix}COUNT = {len(raw)//width}\n{prefix}RAW_SHA256 = "{sha(raw)}"\n{prefix}B85 = (\n')
        chunks.extend('    '+repr(blob[i:i+100])+'\n' for i in range(0,len(blob),100))
        chunks.append(')\n\n')
    return ''.join(chunks), values

def read_literals(path):
    source=Path(path).read_bytes(); tree=ast.parse(source)
    values={}
    for node in tree.body:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
            name=node.targets[0].id
            if name in NAMES: values[name]=ast.literal_eval(node.value)
    if set(values)!=set(NAMES): raise ValueError('Missing one of the six data constants')
    return source,tree,values

def unpack_values(values):
    out=[]
    for kind,width in (('C8',40),('H2',14)):
        prefix='_DB682_'+kind+'_LANGUAGE_'
        raw=zlib.decompress(base64.b85decode(values[prefix+'B85'].encode('ascii')))
        if len(raw)!=values[prefix+'COUNT']*width or sha(raw)!=values[prefix+'RAW_SHA256']:
            raise ValueError('Embedded data failed count/checksum checks')
        out.append(raw)
    return tuple(out)

def compare_release(path,c8raw,h2raw,generated_values):
    source,tree,values=read_literals(path)
    if sha(source)!=RELEASE_HASH: raise ValueError('Not the exact frozen v0.15.0 reference release')
    expected=unpack_values(values)
    if expected!=(c8raw,h2raw): raise ValueError('Regenerated raw bytes differ from frozen data')
    # Exercise only the unchanged data loader/reconstruction functions. No
    # source imports, native setup, top-level execution, or DB search occur.
    wanted={'_load_db682_c8_language','_db682_c8_language','_load_db682_h2_records',
            '_db682_h2_records','_db682_h2_complete_rows'}
    functions=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in wanted]
    if {node.name for node in functions}!=wanted: raise ValueError('Missing release data loaders')
    module=ast.Module(body=[ast.ImportFrom(module='__future__',names=[ast.alias(name='annotations')],level=0)]+functions,type_ignores=[])
    ast.fix_missing_locations(module)
    environment={'base64':base64,'zlib':zlib,'hashlib':hashlib,**generated_values,
                 '_DB682_C8_EDGE_ORDER':C8,'_DB682_H2_EDGE':2,'_DB682_H2_PARTNERS':PARTNERS,
                 '_DB682_H2_SELECTED':H2,'_DB682_C8_LANGUAGE':None,'_DB682_H2_RECORDS':None,
                 'DB':lambda *args:SimpleNamespace(_nonincident=EXPECTED)}
    exec(compile(module,'<v0150-data-loaders-only>','exec'),environment)
    c8=decode_c8(c8raw); records=decode_h2(h2raw,len(c8))
    if environment['_db682_c8_language']()!=c8 or environment['_db682_h2_records']()!=records:
        raise ValueError('Unchanged v0.15.0 loaders did not round-trip generated data')
    for record in records:
        if environment['_db682_h2_complete_rows'](record)!=complete_h2(record,c8):
            raise ValueError('Unchanged H2 row reconstruction differs')
    return {'performed':True,'c8_raw_bytes_identical':True,'h2_raw_bytes_identical':True,
            'all_six_literal_values_identical':values==generated_values,
            'original_loader_round_trip':True,'h2_reconstructed_rows_checked':len(records),
            'release_sha256':sha(source)}
