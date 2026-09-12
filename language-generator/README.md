# What This Does

This program generates 2,544 $C_8$ systems, generates 60,196 $H_2$ systems exhaustively, and generates 60,196 $H_5$ systems by reflection. It outputs the $C_8$ and $H_2$ systems in the format embedded in v0.15.0, while the $H_5$ systems are obtained from $H_2$ by reflection and exported separately. completeness of the generated $C_8$ language uses the published classification of $C_8$ thrackle drawings. For more information regarding a detailed mathematical explanation of the v1.1.0 algorithm, its correctness argument, and the resulting bound, refrence Truman Scoppetto, *Another Brick in the Wall: A Computationally Assisted Proof of an Improved Upper Bound for Thrackles*, manuscript in preparation, 2026.  

# How To Use

To run this one first needs to install
```python
python -m pip install -r requirements.txt
```
and to actually run the comand one can use
```python
python generate_languages.py --output results --threads 4
```
