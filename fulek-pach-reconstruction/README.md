# What This Is
This is a reconstruction of Fulek and Pach's algorithm based on how it is described in their 2011 paper. This means it isn't their original but our best attempt at a recreation using NetworkX 3.3 as we could not find the original so it may perform better or worse than their actual program. Its purpose is to provide a baseline for comparison with v0.15.0 to see how much our program actually improved upon Fulek and Pach. The results of this comparison can be found in benchmarks/seeded-c6-db682/. The validation of this program exhausts all $46{,}656$ complete $C_6$ systems and checks smaller known examples and is tested by test_reconstruction.py.
# How to Use
to run one must first install the requirements.
```python
python -m pip install -r requirements.txt
```
To run the validation one can use:
```python
python test_reconstruction.py
```
For running a check of DB(6,8,-2) one should run the following:
```python
python fulek_pach_reconstruction.py --db 6 8 -2 --seconds 900 --progress 5 --output db682_result.json
```
However, when experimenting with other graphs, one should create a python file with the following:

```python
edges = [
  [0, 1],
  [1, 2],
  [2, 3],
  [3, 4],
  [4, 0]
]
python fulek_pach_reconstruction.py --edges --seconds 900 --progress 5 --output db682_result.json
```
Here, you can define the abstract set of edges you want checked before running the program checked. This is called in the program where it says edges. In the actual command to execute the program, seconds defines the number of seconds the program will run for, in this case it is 900, and progress defines the number of seconds that a progress check is given. finaly, output gives the name of the .json file where the report for the run will be.
