# What This Does

This program checks the thrackleability of dumbbell graphs with a specialization in the $DB(6,8,-2)$ graph in particular. It does this by taking four representative cores of eight planar complete $C_6$ $G'$s and searching extensions of them through both planarity testing and checking whether the $G'$ being checked can extend into a complete $\Pi$. This program has concluded that a DB(6,8,-2) is non-thrackleable in about 2 hours 38 minutes. The audit evidence for the successful run can be found attached to the v0.15.0 GitHub release. For more information regarding a detailed mathematical explanation of the v0.15.0 algorithm, its correctness argument, and the resulting bound, refrence Truman Scoppetto, *Another Brick in the Wall: A Computationally Assisted Proof of an Improved Upper Bound for Thrackles*, manuscript in preparation, 2026.  

# How To Use

For running a check of DB(6,8,-2) with all of the speed ups we added, one should run the following:
```python
python fulek_pach_thrackle_v0150_FINAL_23ae90.py search-db682-cores --processes 4 --planarity-backend boost --report db682_run.json
```
However, when experimenting with other graphs, one should create a python file with the following:

```python
from fulek_pach_thrackle_v0150_FINAL_23ae90 import DB, Edges, inspect, run

graph = Edges(
    [
        (0, 1),
        (1, 2),
        (2, 3),
        (3, 4),
        (4, 0),
    ],
    label="Custom C5",
)

inspect(graph)

result = run(
    graph,
    time_limit=600,
    max_calls=10_000_000,
    planarity="boost",
    workers=4,
    report="custom_graph_result.json",
)
```
This doesn't have the same speed ups as the first code but has more flexibility. the graph section tells what graph is being searched. One can either spell out the abstract graph via the Edges function as shown where one would define an edge as $(v_1,v_2)$. instead of edges, $DB(c',c'',\ell)$ can also be used for a dumbell. Inspect checks to see if the program can actually run a check on that graph. Now, in the run section there is multiple variables to control. time_limit allows one to set the amount of seconds the program runs for and provides an inconclusive result when time runs out; max_calls sets the maximum number of recursive search states the program may examine before stopping with an inconclusive result; workers sets how many CPU threads the Boost planarity backend may use to test candidate graphs in parallel; report specifies the name and location of the JSON file in which the program saves the search result, settings, coverage, and statistics.
