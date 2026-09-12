#!/usr/bin/env python3
"""Optional provenance utility: derive the three seed records from v0.15.0.

This step reads the entire frozen list. It is NOT the generation algorithm.
The generator's normal run needs only the supplied three records in seeds.json.
The old Python release is parsed as text and is never imported or executed.
"""
import argparse
from pathlib import Path
from generate_c8 import neighbors, read_frozen_reference, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("Choose a new seed output file.")
    systems, provenance = read_frozen_reference(args.release)
    index = {system: i for i, system in enumerate(systems)}
    remaining = set(systems)
    components = []
    while remaining:
        seed = min(remaining)
        stack, component = [seed], set()
        while stack:
            system = stack.pop()
            if system in component:
                continue
            if system not in remaining:
                raise RuntimeError("Frozen component partition inconsistent.")
            component.add(system)
            for image in neighbors(system):
                if image not in index:
                    raise RuntimeError("Frozen language is not closed under the stated moves.")
                if image not in component:
                    stack.append(image)
        remaining -= component
        components.append(component)
    if sorted(map(len, components)) != [656, 896, 992]:
        raise RuntimeError("Unexpected frozen components.")
    seeds = []
    for component in sorted(components, key=len):
        seed = min(component)
        seeds.append({"rows": seed, "source_record_index_zero_based": index[seed],
                      "source_component_size": len(component)})
    write_json(args.output, {
        "schema": "c8-seeds-v1", "seed_count": 3,
        "selection": "Lexicographically least localized system in each frozen closure component, ordered by component size.",
        "provenance": {"source_file": "fulek_pach_thrackle_v0150_FINAL_23ae90.py", **provenance},
        "normalization": "e_i=(i,i+1 mod 8), each oriented forward; DB row order (0,1,11,10,9,8,7,6), reverse rows after the first two.",
        "seeds": seeds,
    })
    print(f"Extracted {len(seeds)} seeds; source component sizes {[len(c) for c in sorted(components, key=len)]}")


if __name__ == "__main__":
    main()
