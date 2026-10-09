# Thrackle DB(6,8,-2) Computation
# Purpose

This repository contains the computational background for Truman Scoppetto, [*Another Brick in the Wall: A Computationally Assisted Proof of an Improved Upper Bound for Thrackles*](Another_Brick_in_the_Wall.pdf), manuscript in preparation, 2026, as well as the paper itself. The goal of this was to reconstruct and extend the Fulek–Pach algorithm and to optimize it for the DB(6,8,-2) dumbbell so a potential new local bound could be gained.

# Main Result

The completed v0.15.0 search successfully reports a non-thrackleable DB(6,8,-2) with 100% search coverage. As a direct result of this, we are able to prove that for any 8-face $F$, $h(F)\le4$ by showing how every case in which $h(F)=5$ is impossible in a thrackle by structural arguments. This new half-edge bound allows us to create a new discharging argument giving the bound of $m\le\frac{18}{13}(n-1)$. This result has not yet been peer reviewed.

# Repository Contents

In this repository you will find eight key things two of which inside V0150/, two in language-generator/, one in fulek-pach-reconstruction/, two in benchmarks/, and the paper itself. The first is the v0.15.0 code which is what we used to test for thrackleability. This program is specialized for the DB(6,8,-2) dumbbell having a majority of speedups focused around there, however, the program is still able to test thrackleability for other graphs, it just won't have the same speedups as DB(6,8,-2) has when it is being checked. The next important thing is the $C_8$, $H_2$, and $H_5$ where generator completeness of the generated $C_8$ language uses the published classification of $C_8$ thrackle drawings. This program generates all thrackleable systems for $C_8$ and then extends these into a case with an additional edge, $H_2$, where $H_5$ is then made from the reflection of $H_2$. This program provides prerecorded systems that v0.15.0 uses to test whether systems can be eliminated or not. As for the other two key items, they have to do with the reproducibility of v0.15.0 and the generator. In fulek-pach-reconstruction/, there is our reconstruction of Fulek and Pach's program that we couldn't find thus it may be slightly better or worse than the original; his is important for what is in the benchmarks/ section. In the benchmarks/ section there is a comparison test of v0.15.0 and our reconstruction where each start from the same seeded $C_6$ core and there speed search coverage is tested on intervals. also in that file is the results of the test that we ran. Finaly, the pdf of the paper is also included.

# Reproducibility

The exact frozen program of v0.15.0 is in the V0150 folder with a SHA-256 checksum of: 23ae908626820dd3afaf1dbbc180619186e8bfcb417bf8a2bbcac2bb76369632. This program has concluded that a DB(6,8,-2) is non-thrackleable in about 2 hours 38 minutes with 100% coverage. Also attached to v0.15.0s release is an audit and evidence of v0.15.0s validity. The separate generator on the other hand regenerates 2,544 $C_8$ systems, generates 60,196 $H_2$ systems exhaustively, and generates 60,196 $H_5$ systems by reflection. It's generated systems match those encoded into v0.15.0 exactly and has passed the recorded verification checks and exact-data comparison. These checks support reproducibility but are not a machine-checked formal proof. Our reconstruction of Fulek and Pach's algorithm covered every system in $C_6$ finding all the thrackleable ones and our benchmark found that across the four tested cores were approximately $1.74\times10^{24}$, $1.63\times10^{20}$, and $1.42\times10^{20}$ over the 2--5, 5--10, and 10--15 minute intervals, respectively.

# How to use the repository

Inside of V0150/, language-generator/, fulek-pach-reconstruction/, and benchmarks/ there is a README. These give a little bit more details on each one and how to actually use them. Please refer to these when trying to run programs and get information about the programs.

# Citation
Find all citations in CITATION.bib.
