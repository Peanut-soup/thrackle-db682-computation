# What This is
This package compares our reconstruction of the Fulek--Pach published method with the frozen v0.15.0 implementation on identical seeded subproblems of $DB(6,8,-2)$. Both programs used NetworkX 3.3 and one worker, their runs were sequential, each program received 900 seconds on cores $0,1,3,5$, and both searches began with the same corresponding $C_6$ core. Neither program completed. The comparison measures observed search-space resolution, not total completion time or asymptotic complexity. it records progress in the intervals of 0-30 seconds, 30 seconds-2 minutes, 2-5, 5-10, and 10-15 minutes and gives updates every 5 seconds. 
# How to Use
first install prerequisite requirements
```python
python -m pip install -r requirements.txt
```
then test before running the check. All ten tests should pass.
```python
python test_benchmark.py
```
Then run the benchmark
```python
python benchmark.py
```
One can conduct longer optional runs such as running all cores and not just the four representatives
```python
python benchmark.py --cores all
```
Or one can run the check multiple times
```python
python benchmark.py --repeats 3
```
The result is given as report.txt and .json files that give the details of the run.
