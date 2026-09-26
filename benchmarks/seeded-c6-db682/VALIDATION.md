# Validation scope

The two bundled search source files are byte-for-byte copies of the previously
reviewed implementations. `benchmark.py` rejects a changed source hash or a
changed mathematical C6 fixture.

The benchmark adapter has automated checks for:

1. All eight real C6 seeds: independent augmentation planarity, valid orientation
   conversion, a genuine Euler traversal for the reconstruction, and agreement
   between the two programs' extension denominators and the direct factorial count.
2. Seeded partitions of small graphs: with all pruning disabled, every complete
   leaf is visited once; over all seeds, the original space is covered exactly.
3. Agreement of all seeded witness sets with an independent full-graph oracle,
   both with and without prefix pruning on the small examples.
4. Invalid seeds and altered fixture data being rejected.
5. Large prunes occurring after a checkpoint not being credited to that earlier
   checkpoint, including when a slow progress write crosses the boundary.
6. No post-deadline credit, and no artificial later intervals after early completion.
7. Completion-time ratios requiring completed runs, with timeout bounds kept
   distinct from measured ratios.
8. Crashed or forcibly stopped jobs appearing explicitly in the report.

Local integration checks exercised the two-program runner, short runs on all
four default cores, the v0.15.0 local-domain and main-search paths, timeouts,
scientific-notation interval rates, and JSON/CSV/text report generation.

These checks validate the adapter and measurements at this scope. They are not
a new exhaustive DB(6,8,-2) computation or a formal software proof. Short trial
timings are diagnostic and are not supplied as a performance claim. The full
two-hour experiment is left for the user to run locally.

The original reconstruction's standalone validation suite is also included as
`sources/test_reconstruction.py`, with its fixtures. Run it with:

```powershell
python sources/test_reconstruction.py
```

That suite independently exhausts all 46,656 complete C6 systems as well as
smaller graphs and checks known positive C8 prefixes and interruption behavior.
