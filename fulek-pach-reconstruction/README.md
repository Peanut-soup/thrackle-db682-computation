#What This Is
This is a reconstruction of Fulek and Pach's algorithm based on how it is described in their 2011 paper. This means it isn't their original but our best attempt at a recreation using NetworkX 3.3 as we could not find the original so it may perform better or worse than their actual program. Its purpose is to provide a baseline for comparison with v0.15.0 to see how much our program actually improved upon Fulek and Pach. The results of this comparison can be found in benchmarks/seeded-c6-db682/. The validation of this program exhausts all $46{,}656$ complete $C_6$ systems and checks smaller known examples and is tested by test_reconstruction.py.
#How to Use
to run one must first install the requirements.
```python
python -m pip install -r requirements.txt
```
To run the validation one can use:
```python
python test_reconstruction.py
```
