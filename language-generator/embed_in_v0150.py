#!/usr/bin/env python3
"""Replace only the six data constants in a NEW copy of frozen v0.15.0."""
import argparse
import ast
import copy
import json
from pathlib import Path
import sys

import language_io as codec


def assignments(tree):
    found={}
    for node in tree.body:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
            name=node.targets[0].id
            if name in codec.NAMES:
                if name in found: raise ValueError('Duplicate data assignment')
                found[name]=node
    if set(found)!=set(codec.NAMES): raise ValueError('Missing data assignment')
    return found


def without_data(tree):
    tree=copy.deepcopy(tree)
    for node in assignments(tree).values(): node.value=ast.Constant(value='<regenerated data>')
    return ast.dump(tree,include_attributes=False)


def embed(source_path,blocks_path,output_path):
    if output_path.exists(): raise FileExistsError('Choose a new output filename; existing files are preserved')
    original,tree,old_values=codec.read_literals(source_path)
    if codec.sha(original)!=codec.RELEASE_HASH: raise ValueError('Source is not the exact frozen v0.15.0 release')
    blocks,block_tree,values=codec.read_literals(blocks_path)
    c8raw,h2raw=codec.unpack_values(values)
    if codec.sha(c8raw)!=codec.C8_HASH or codec.sha(h2raw)!=codec.H2_HASH:
        raise ValueError('This compatibility helper requires exact reproduction of the released languages')
    if (c8raw,h2raw)!=codec.unpack_values(old_values): raise ValueError('Replacement data differ from the release')
    c8=codec.decode_c8(c8raw); records=codec.decode_h2(h2raw,len(c8))
    for record in records: codec.complete_h2(record,c8)
    target_nodes=assignments(tree); block_nodes=assignments(block_tree)
    lines=original.splitlines(keepends=True)
    block_lines=blocks.splitlines(keepends=True)
    changes=[]
    for name,node in target_nodes.items():
        replacement=block_nodes[name]
        if node.col_offset or replacement.col_offset:
            raise ValueError('Unexpected indented data assignment')
        changes.append((node.lineno-1,node.end_lineno,
                        b''.join(block_lines[replacement.lineno-1:replacement.end_lineno])))
    for start,end,replacement in sorted(changes,reverse=True): lines[start:end]=[replacement]
    result=b''.join(lines); new_tree=ast.parse(result)
    if without_data(tree)!=without_data(new_tree): raise ValueError('Non-data program structure changed')
    output_path.parent.mkdir(parents=True,exist_ok=True)
    # Exclusive creation prevents overwriting even if another process created it meanwhile.
    with output_path.open('xb') as target: target.write(result)
    _,_,actual=codec.read_literals(output_path)
    if actual!=values: raise ValueError('Written constants differ from exported values')
    return {'status':'PASS','source_sha256':codec.sha(original),'output_sha256':codec.sha(result),
            'only_six_data_assignments_replaced':True,'non_data_ast_unchanged':True,
            'c8_raw_bytes_identical':True,'h2_raw_bytes_identical':True,
            'c8_records':len(c8),'h2_records':len(records),'original_file_modified':False,
            'db_search_executed':False,'generated_values_equal_original_values':values==old_values}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--blocks',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(embed(args.source,args.blocks,args.output),indent=2))


if __name__=='__main__':
    try: main()
    except Exception as error:
        print(f'FAILED: {error}',file=sys.stderr); sys.exit(1)
