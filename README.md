# Thrackle DB(6,8,-2) Computation
# Purpose

This repository contains the computational background for Truman Scoppetto, *Another Brick in the Wall: A Computationally Assisted Proof of an Improved Upper Bound for Thrackles*, manuscript in preparation, 2026. The goal of this was to reconstruct and extend the Fulek–Pach algorithm and to optimize it for the DB(6,8,-2) dumbbell so a potential new local bound could be gained.

# Main Result

The completed v0.15.0 search successfully reports a non-thrackleable DB(6,8,-2) with 100% search coverage. As a direct result of this, we are able to prove that for any 8-face $F$, $h(F)\le4$ by showing how every case in which $h(F)=5$ is impossible in a thrckle by structural arguments. This new half-edge bound allows us to create a new discharging argument giving the bound of $m\le\frac{18}{13}(n-1)$. 

# Repository Contents

In this repository you will find four key things two of which inside V0150/ and two in language-generator/. The first is the v0.15.0 code which is what we used to test for thrackleability. This program is specialized for the DB(6,8,-2) dumbbell having a majority of speed ups focused around there, however, the program is still able to test thrackleabilty for other graphs, it just wont have the same speedups as DB(6,8,-2) has when it is being checked. The next important thing is the $C_8$, $H_2$, and $H_5$ where generator completeness of the generated $C_8$ language uses the published classification of $C_8$ thrackle drawings. This program generates all thrackleable systems for $C_8$ and then extends these into a case with an additional edge, $H_2$, where $H_5$ is then made from the reflection of $H_2$. This program provides prerecorded systems that v0.15.0 uses to test wether systems can be eliminated or not. As for the other two key items, they have to do with the reproducibility of v0.15.0 and the generator.

# Reproducibility

The exact frozen program of v0.15.0 is in the V0150 folder with a SHA-256 checksum of: 23ae908626820dd3afaf1dbbc180619186e8bfcb417bf8a2bbcac2bb76369632. This program has concluded that a DB(6,8,-2) is non-thrackleable in about 2 hours 38 minutes with 100% coverage. Also attached to v0.15.0s release is an audit and evidence of v0.15.0s validity. The separate generator on the other hand regenerates 2,544 $C_8$ systems, generates 60,196 $H_2$ systems exhaustively, and generates 60,196 $H_5$ systems by reflection. It's generated systems match those encoded into v0.15.0 exactly and has passed the recorded verification checks and exact-data comparison. These checks support reproducibility but are not a machine-checked formal proof.

# How to use the repository

Inside of V0150/ and language-generator/ there is a README. These both give a little bit more details on each one and how to actually use them. Please refer to these when trying to run programs and get information about the programs.

# Citation
@misc{ScoppettoThrackleLanguages2026,
  author       = {Truman Scoppetto},
  title        = {{C8}, {H2} and {H5} Language Generator for v0.15.0},
  year         = {2026},
  howpublished = {Supplementary software accompanying the thrackle manuscript},
  note         = {Version 1.1.0, 10 September 2026. AI-assisted companion implementation; seeded C8 regeneration, exhaustive H2 extension, reflected H5 export, and exact reproduction of the frozen v0.15.0 data}
}

@article{MiserehNikolayevskyAnnular2018,
  author  = {Grace Misereh and Yuri Nikolayevsky},
  title   = {Annular and pants thrackles},
  journal = {Discrete Mathematics and Theoretical Computer Science},
  volume  = {20},
  number  = {1},
  year    = {2018},
  note    = {Article 16. C8 classification in Section 4, p. 13, before Figure 19},
  url     = {https://arxiv.org/pdf/1708.07351}
}

@article{FulekPach2011,
  author  = {Radoslav Fulek and J{\'a}nos Pach},
  title   = {A Computational Approach to Conway's Thrackle Conjecture},
  journal = {Computational Geometry},
  volume  = {44},
  number  = {6--7},
  pages   = {345--355},
  year    = {2011},
  doi     = {10.1016/j.comgeo.2011.02.001}
}
