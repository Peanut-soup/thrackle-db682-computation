"""
Fulek–Pach thrackle reconstruction — Version 0.15.0
=====================================================

v0.15.0 is a correctness-first support-driven extension of the frozen
v0.14.0 DB(6,8,-2) search. It preserves the complete-Pi space and every
previously audited pruning theorem, and adds exact H2=C8+edge2 and reflected
H5=C8+edge5 selected-subgraph support plus support-driven host-slot generation.
The H2/H5 filters are complete-language extension tests: they never planarity-
test an arbitrary-gap incomplete DB state.  All new production reductions have
explicit verification switches and exact candidate-multiplicity accounting.

v0.14 already supplied an exhaustive C8 crossing-language support filter and
an exact graph-
automorphism quotient pairing the eight planar C6 cores into four orbits.
No incomplete arbitrary-gap graph is ever planarity-pruned.

Mathematical safety rules:
* complete crossing-order systems Pi and the final Fulek–Pach augmented graph
  criterion are unchanged;
* the v0.8.1 placeholder-tail partial-planarity test is NOT used;
* the current edge is represented only by the prefix actually constructed, so
  each UPDATE extends a graph that is a minor of every completion;
* a stronger locked-prefix minor retains only already-forced portions of the
  Fulek–Pach crossing gadgets.  It is also a minor of every completion;
* a branch is planarity-pruned only when one of these proved-minor graphs is
  nonplanar;
* C6 relative-order pruning remains a necessary-condition test;
* for DB(6,8,-2), an optional exact C6-core decomposition enumerates all 46,656
  C6 crossing-order systems, keeps only those whose complete C6 augmented graph
  is planar, and searches the resulting disjoint extension spaces independently.

Performance changes:
* DB(6,8,-2) core workers use exact C6-projection domains: for each retained
  C6 core, they precompute every planar crossing-order signature of C6 plus
  one future q-path edge.  Any global completion must project to one of these
  signatures, so all other local signatures are eliminated in one exact step;
* q-stage search is factorized by this projection.  It enumerates only planar
  C6+q signatures, then exactly enumerates the remaining interleavings with
  already-active q edges.  This is a bijective reparameterization of the same
  complete Pi space, not a heuristic restriction;
* factorized arbitrary-gap partial assignments are never themselves
  planarity-pruned.  Before a stage is complete, v0.10 may delete every still-
  pending q edge and test only the COMPLETE augmented graph of the resulting
  selected-edge restriction; nonplanarity of that literal subgraph/minor safely
  eliminates all completions of the branch;
* these completed-restriction tests are cached only by the exact projected Pi
  that determines the tested graph; no coarse-signature conflict learning is
  used for pruning;
* Boost/C++ batched planarity is retained and rewritten for safe prefix UPDATEs;
* one-level lookahead is off by default for the target because it is expensive;
* the target can be split into independent C6-core jobs and run in parallel;
* the DB(6,8,-2) tail order is [7,10,9,8,6,11]; reordering is a
  bijective traversal change only;
* v0.11 adds an exact whole-stage DEAD certificate for the q6/q11 bottlenecks:
  it enumerates every distinct complete zero-extra selected restriction covered
  by the local domain.  If all are nonplanar, every exact stage completion is
  impossible, so the entire stage is resolved at once; if even one is planar,
  the certificate returns UNKNOWN and the frozen exact v0.10 recursion is used;
* the whole-stage certificate is cached by the exact selected parent Pi only.
  Pending/deleted q-edges are not part of the theorem and are never guessed;

* v0.13 adds an exact C8-language support filter.  The target contains the
  8-cycle on original edges (0,1,11,10,9,8,7,6).  Every full planar DB Pi
  restricts to a planar complete Pi on that C8.  v0.13 stores 2,544
  labeled/oriented C8 crossing-order systems.  v0.14 release certification
  checks every one independently with NetworkX and certifies exhaustiveness
  using the published Misereh--Nikolayevsky classification of exactly three
  C8 classes together with exact dihedral/Reidemeister-III closure.  A partial
  DB state is rejected only when NONE of these complete C8 systems contains
  every already-fixed C8 order as a subsequence.  This is an extension test,
  not an incomplete-graph planarity test;
* v0.13 also quotients the eight retained C6 cores by the exact reflection
  automorphism of DB(6,8,-2).  The automorphism induces a bijection of complete
  Pi systems and isomorphisms of augmented graphs, so one representative of
  each two-core orbit suffices for a full target run.
* v0.14 preserves that exact C8 theorem but propagates its support bitset
  incrementally: when a child inserts crossings, only the changed C8 rows are
  intersected into the already-exact parent support.  This is algebraically
  identical to recomputing all eight row constraints at every node;
* v0.14 also factors each q-stage's C6-host slot product into C8-sensitive
  hosts (only target-C8 edges 0 and/or 1) and C8-insensitive hosts.  Sensitive
  slots are tested first.  If their exact C8 support is empty, the full product
  of insensitive slots and remaining extras is eliminated with an asserted
  exact multiplicity.  No new planarity inference is introduced;
* v0.14 precomputes every row-subsequence support mask directly from all 2,544
  frozen C8 systems, replacing repeated scans with exact dictionary/bitset
  operations.
* complete-restriction planarity is accelerated by a compact exact LRU cache,
  literal Kuratowski-certificate containment, and a compiled batch planarity
  path.  Optional graph-isomorphism reuse always performs an exact isomorphism
  check; hashes are lookup buckets only and never authorize pruning.

Result semantics:
THRACKLEABLE = a complete Pi with planar full augmented graph was found.
NONTHRACKLEABLE = every relevant Pi was tested or safely eliminated, with exact
                  coverage of the searched space.
INCONCLUSIVE = a resource limit stopped the search; no mathematical conclusion.

This is an independent reconstruction, not the original Fulek–Pach software.
Dependencies: networkx; fast mode also uses g++ and Boost headers.
"""

from __future__ import annotations

from dataclasses import dataclass, asdict, field
from collections import OrderedDict, defaultdict
from decimal import Decimal, localcontext
from itertools import combinations, permutations, product
from math import factorial, prod
from typing import (
    Dict,
    Hashable,
    Iterable,
    List,
    Optional,
    Sequence,
    Tuple,
    FrozenSet,
)
import json
import sys
import time
import os
import ctypes
import hashlib
import subprocess
import tempfile
import multiprocessing as mp
import traceback
import random
import base64
import zlib
from array import array
from pathlib import Path

import networkx as nx


Vertex = Hashable
Pi = Dict[int, List[int]]

# Friendly public setting values. These are plain strings intentionally exposed
# as lowercase names so notebook users can write display=single or display=line.
single = "single"
line = "line"
dashboard = "dashboard"
auto = "auto"

__all__ = [
    "DB",
    "Cycle",
    "Edges",
    "run",
    "inspect",
    "single",
    "line",
    "dashboard",
    "auto",
    "ThrackleGraph",
    "BacktrackingSearch",
    "SearchResult",
    "DB682CoreResult",
    "SearchStats",
    "print_result",
    "coverage_percent_string",
    "verify_planarity_backends",
    "run_db682_cores",
    "enumerate_planar_c6_cores",
]


# ---------------------------------------------------------------------------
# v0.13 exact DB(6,8,-2) C8 crossing language
# ---------------------------------------------------------------------------
# The target contains the simple cycle A-s1-B-q5-q4-q3-q2-q1-A.  Its original
# edge IDs, in that traversal direction, are listed below.  The q-path edges
# are traversed opposite their fixed program orientation; the embedded data
# has already been converted into the program's fixed edge orientations.
_DB682_C8_EDGE_ORDER = (0, 1, 11, 10, 9, 8, 7, 6)
_DB682_C8_EDGE_SET = frozenset(_DB682_C8_EDGE_ORDER)
_DB682_C8_LANGUAGE_COUNT = 2544
_DB682_C8_LANGUAGE_RAW_SHA256 = "8e260f0471170ffad6490fa6debdfd06c52f153a67d9079525511c63df7c907e"
_DB682_C8_LANGUAGE_B85 = (
    'c-obn+mfa#3`XTfQQ!Z4$DF?;=-*Q{HM?ti?EoQ!fB}wk-q${l>)f8d&vDFs+mG!Y+di)Q`LmtpeU0Z=uiW$N=g-4EG;(t%ZlB6M'
    '|7_g6?#8*idk=Zjxa*K|kCE#4khy*<j;L|v`VmLv9wXOJxTs%nxqd3o>i1wo&Fy%kjs1a+M|1qcNm`sIaOV-+aVz&U0=a4Jn8Vw_'
    'YRT<gayNHeYA<u#j^OS+IBmy6c>lUy#<iOr%xg5x^)mLbmx)}lgNNCLdx#J2`Q<KlFvn%}i~ddZQ@up}7Ir}OGyP5EiXBk>goFAm'
    '?Pctuzo_4}Te<sK)o)zDu{`9W+%FEweQ@O-V0(;bFI<!N#ogna!cnnq&ttFl{FvVfoZ2&U$)168JKg8da>X66UWS(&_Pmd7_v4x$'
    'oZJ0FBPVw6T-g0nKhYl<V6We3{U)6B2XL+5mfS4^3HuE=sGkfZs^4_(*dOlsi{(899?xHo1~2Zl&|h#Q&$#_E&h)3;xr@C0MtS#H'
    '<vkqBQ%>dGXOYKt#qy5Z<ULT6N1VtLj^qg!^3FZ#_ZUj5U)X7ItiO@#H_j~2>bH+vzben_XPng!<i$8j{oCx|i^FmYH==%H&1HKr'
    'dA)wZjcCU(?(vp9|B@d7zk6?Go-UmE(|arPG;>tXE%`~22lHy-vOJiNh|_uX>Ef7Islhm}I(HtyJ$^{Im{*ybR<6&3_g3b?hvWIE'
    '>m|=e%q`oS=LO=}QEthPBgg)LIU3+w^3TknUH#<LULMZ;IP1myc<4|3vvaCH^W&jE;6i_9f1p3{r^L-@?{u#Czs!NW;{TX?{KhlM'
    'B>zVN8~VS@h5w^~4gDW*$^W@L^;ek-|L5}5Uj>)_pU4aUm$~qNA}{=(aOWQN6TcSqi~bER{9n}1$GLLZ|3&?(yzKv?ejqRGFZFM+'
    '({B#TE!>FujWw6;1^wTO8_|yNe~<N{|D$=B<Xv0wf5tt(KA(}XPgoz(_|SNqIq(Nb9{N9Z8!|2*O8nY(RljB&k4xpA4!NpdyC(aq'
    'r;=R1xkH@I^^-W(xZd94*NiLe<zcDqouhM6?rz-la+i83e)8eaPcAs|8^rO*_}$)%N5=1VAotY{^t)KUWcR-~vuB+a%nsB)gB_^f'
    'HBRk7{WI7Bb5u>U({t1IlG%%$UL^3bK;+ItId&V$k-*HIyK>@AgCobwoY_GtSM)69K6(Z&m#Z9?o48VLa1@XqM1PFSXz#;)*t6H~'
    'CL^GZ;c|~>HSmnuoqnLOM8+lgjmphkISzA_dwwn4^FNrpXL1yIT)!mmB*(#e;d06Dpj?@^Do6f+IWJe{!Qi4Ddy*&fOy#H@dy*&f'
    'mT=S#t=|)|N&T!HSijufJ#kPjIfQ+dc5wM5kH?X7t-btTE_Wubw!=8;UgNIa%YDXCEB6|~S-HVQxrx(qpI^6fjibOx<&C}TkLHiy'
    'MBdoD{(_s{j;A|Bp7_7q4&rLLV)s(+TyP<;x0kt6KbLo(S)OuJ_2TkWFQ>=%+i7w8y|wsWxaS9vH#Z$`GOcD#{O-AVTrA6|<ez_Y'
    'I(|=&pQV1}cXR#N?+OR?qwdf33ywESD(Cj{sLwcx6QzC<PwECG#FK^7cv3egA)Zw3+(X_I*Clz;-rzL;OY+2DF?a6R4(i|3j&m4y'
    'V7bSLatG?Ua@-#|p8U-%<!SsE?XdW7$%(uaPm)!C%&Q*%0k@i0W1Ks;oL6I<Gk2X|^9TK!xfn+hC*E6&Cxx5m*Zdapf?LgRCePwd'
    ')(gc=Jn!c?3^>sX`Ip1F@K@*c6-Riy*0?A)#cRN=;*Icsm5cgi|L5E?E(!lvIr4u=p7}qHi+lfuyl2`{JzwrO*zZ>E8Vhdj%3a03'
    'MEv}---P?!ZyG=U>^J1T`c1gs{f69Ezg_09e)Jo1U;XCXavpqsz2N#hsD9Gc3pyWdqQAPX_|2LB^L2&z1D&_(x<WV@=Q<z3I1eu7'
    'E#OA8E0`Bn@sPBapopKB^EtQU;UM1S_~0JMX}s%P$lDXA^CfW+cY?eUcN*8qEpexFwcHYSGUst8#}TdEYXoQI2AA#Gx!3uZ?36bo'
    'c%C7F8-3guJP-2zGkqf2*pFB4F&pO|?<Cw~cgkId%NqyCqYrv0&$(y%I6$6oAn!at9>p6h@0odvJmXlNa*x@cS)K$ikAIPVqjLFs'
    ')X6`DylZ+p9!+WeuF={d0fNh;a^?HhS><^<NS@U18nqn<HH19SW0B(YX-qx{xxc~V?VY1Nn(dU2@|k-I9<&?69DT-CZjvb!&gIcZ'
    'E0Z@1ckU|h-m|>(uAImt4&@=o`lH5}T|F%pyQ2B6a635;+6LK~djR52wP)p?@uA#t8+V_T<9P<krA;I*mxlRSI4GAmE_dEVUM^R-'
    'r`*at)JYy~YX5HZvHR)0(jT;awJUe;nM3`tzvp&vd=KUN#-nn3)Ng;`t|@j!N>RHal{EWXaI^>4?2oxeGr>`Jbh{Gn+?8W{0nXb?'
    'lY`m|nU>fK4fA3z#?cHt&0ZeWReNDh`i(fT7vhS&&<NdgxisLKy%-1O64&g7xm>Pr#a@Wh{vFf$*SOqoh2wqYHMd8(`&u3ap5kBJ'
    'Z%|mGc0loD<=k&jm}B-bGnf1jg^9w^^!Cn?n-n{sZQ#shKLniF3vtcA^mz-pxxdeY%$4!`{G{Wu)UR^U-p1iLPx7!Gl|y;XJyquZ'
    'plPP}o7<^ykDif>{`lfR&yUE=ox5_mKc4P|`k9`e_@(GM{0nicKZ;zMo^!dCi*_{b+?C6E&h@Jt$_wt?Q+s*(_4b|vxFm1vSnekW'
    '<vMrm>USv|lK!A@T>Cfd**OY_nja5)UUBZn$zl>me%!h6&tx%~d#Wc~^5fLK&<?c&+IOse-2DM^)9i)AKem^Nocd>%2mU$9Q$IQO'
    'g+G-KtV=HWQ|IR1`eQ7{n{YIafLn~W1xG#H#+!4{A5Rafo@eDAyPDn~D9`)DIOsQ&hg|QE(Z(-LtEpTzt3E!QvvPUy=;a3YG<2gi'
    'E6bzL*!v?*wgr;i8^`jP<GsXY_ry_zFY=Dt<k8ey<q;?Hh!c6jnLOUl;gvV6j~4NyaCIHk<6YjcGkLZ?VtKR}KzXZm)UI5T_pCoc'
    '-tai_tnwD?s9iabckN!krxmS!Hr|92dCo!ofb;qhSL>I#kXP#$+!N!3Jcx@`-Z_ACdBUMQ<v6cJ?0y_-_poksyAMv*=bxOEO94z>'
    'Um~aLODVUkFBhDChxp>4+_DZ0?udEj7<r!2g<j#<=cajP!1{N|$vh*;o0((3W}MC+vi!I+ckar?Jfq8$J2=x{nrE{8B`(b~(jOB!'
    'nP);C&okNXh2!~S95~OA2Z#A%#qm7TxR__WKXjhafEPJ&(j(6^wA%XO)IUpje^(CrL;SOZ_k|;W@BM-Dygy=|2@d2T*ZZT7k0a(8'
    'k>~RamuvG!a8|C*GhA+PG0z+$&okNXW1cb2=9z5wG0zZ(^Guf~^Neve&m?(dd)*I_o$@$$J9RGkp*1Idk`{39_B{8Mzv|-yxEcPw'
    'kGHw6{Mr*=owa@|zqaO}9mC_gv$kX9|MsE&Z!WkQ^Nh;FcG!0kZU>LwR6m<Poa1(UbI}fnPxHJboVP>gEojGrn=!vdJB+h*B>KuZ'
    'k3;rOAHPAL4bX1{=i}{*qpl5k`z;*!tKdN1lCyCX^7dg|jHBQ}-XFLT<8rLI@Ebh8sXQN-g&Q$`hjY&&UHA3QP1o`FX8U^d5rU?-'
    '3pm;yV(vbIdmIdMryc>}y&T$Z((lAirMBsbTEbC&m~h8!+#{)SJkju61o=|JSwfd^d&t{gIX%KKX4H=&=T^T<^4Elu`VrUaryGyF'
    '?-S=ln4@jN#?5F)$jjUw<?b(>?7yUblXW~-ZFqk$m-|gQ5)~YMkV^eV+2+u1;{*=-%{bLda7E9=fu0kGdNwZ0JN+OZkB`Woq-E5m'
    '`@6w$vJr6mtsKW|iR1AR`E|m{zPE6CFpJk^Snd<trE>MaRpO{z=H^{FUcX_v#6h`sP>%O=;@nOv*AB`hu9th1{-tzU>bG;G{y6<Z'
    '4xImBj`X7Ygu><iWqA~)HF;|HaDI!qD$h1<q1;t}1Q+K?R{iT6w~6ca;v1B3&d}v)d=DJS15V}XdVx9Hz=Csk(O!vT3+Lzk$Zv?e'
    '37iJn$c;t)Yy&27y?%ah5$t}|zkYxa>{PhNu8^|>f5krw7wz=}aOfw^o}qqz04{NA&(L09z<v8&;EvKCrGCMc{-AQ_g8TI2r!SCD'
    '-m)FqZ;4yz#SY$;_O|*tm+P0>tHXTx-B0Fy+KND~fA_=qfVjsJ=opL4(~uvA^Qv>F&F6RFM1RJeG4Ff+8tPd&&KuEhN6UDFxr>k4'
    'h`mVt*j|Vux6!y6?WpmAbEnzgUF1RijGNKkke9hL?D^gn_MEsGda3rO9P5Ssv+8Bhj@R!;5=XclynYwLc;n$Dj)4AH#SzSv`mN%F'
    '`{a3gJ7eCryszZPor`(j^0d;tfSme2%lk_6%q{sjTJAVfxiJ4a7xR9U3-d2>>QAFwnD=kVN0)L(*uhwo%UsO+!u4`#0JA;wyc*+@'
    'wu?9YP8Zy1^Y2}`B=3xQ+Qwy?Ka@i|SjHR7>3HM#AjVs-pN=DmBks!GDDRAT!^TIiU$(zx{6gGg_*H+@Z(OeCJ!FpJjmX0jPVxnU'
    '%X&t6_gOiPU+yZea2DryzN2z(FU*yGTiJbZo?pBiN6O7TaeZ7;+@yLLd)15Xiw1XE9ClakPV!ER!*Y9VzBKNPxGuG$$~z;jOYJ~;'
    '*RFO-ab2}j*-tFo++m)P`pv?f7AM|S-hDQ1?l8}oyu_UmcV@f4R@~fSo=I^hb8~O)7>j;muGDWV`t8#F$;2)C?V5Y5-&pk9rTZI+'
    '>-|RYZuR#oe?{?b_0KKdy-$laJl@S*==s{!kK=q^<2vUeu1kI#+DmcgAL19_j$)@$KkGN(ik(V4*}2bnNV%W!5O7Da`=Y<#irquJ'
    'o4C*TO1R(g6>vuxM~nKM5#Pr+TGa1%yvFN*)*n2M#15iAbiAQnfQxc<yd{ptTd}`G#~Zd|X@5H261TADxp#YB>BYIM7u2(?26Zdb'
    '@`3NI<w0dmzhg6(^QxGW@6#-gzfYSy$fM1ie#bU>kPj>z@5`G!`cTsHfitJyu~i=C0~4qDz@%!)2c`(S<O3V0<w`y<$t(H5!kq`m'
    '8;8ond|=~1p46}81Iy}H6N4nblMJ=x3v^EF_r*yb=)EoSXpLh>1m)JeSKv;|KfM#@2bz>SBTx0-TK=hXdv0&dqv)Kp_mhM6zP4kv'
    'FAw>)&aL+4NfdIDf6Dcv^_uis&QtB2_1gz0d7IjAIiJ-y>o+U6=AXWBn%}hKPRlF3lRW6R&Vjtjosp+{Z!Q1yg=_h&&h1&xH7~bw'
    'W-lKc=y|0-%@@t%virZnz4}Sy9*1S}n%^zltABp~UIF={Z(PkQb#C=tgH`g)vAoJj9w@hijw9yw%J==w)%IqN+adXrrM(h|y>T_a'
    '(>ZDfbG5zST(lQCO-HwK7kQv>T+IV@4$C!pQtl@Q^>a@1EJ@E}@BWIvcXzJ&t0gzBe@otG=WJeGbLy|WemE}WAoG$-eywn)<#$%U'
    '_Q55;mbo+XMT=ki;96d(b9?TOn$Oy~=GTIo`=UQa8%LRgIHz)_?xSn|BpE@?pG=(QPd;4BpOjs6O$C5>axtG<{$!3jdz@qWlPR98'
    '`IFAoxU=L>3di{+DW0tPlg`z+v*b_O0Zf%Ad6Bt()^C<SnYfxiDV*0&@*;EnG8gh{{eqJ`6y+dZgFF=HT%K?>fAZlhFY@6uZz;vu'
    'Zdbus-qHsr<!U}sipP=Dc--=gQarxkEYIkJgK|sU9^B!6jr01#pXPom9Qe}@F8Nc)zv>+L(*-AfGU_M!iOEl{IL%L7a;N1n-btSO'
    'wG{{QDtAU+<h`~0$rrBWPdc~f{-}9wodbVbIro#;AKm^k_im?0_*2gR1Appyf{D{SLGY&o)|Zz5SH@e;|4UpNZ);Bcf#&tS=w<G!'
    'aoOz;xEX$}+r8%hmGPVN{}PwR@0x>l44<dZ+K$yY&v}A{o8eD$o*;8}ADQI|min2Wbk6bwKe%WI#2eW^TmGN6L;Z8f6D-^eKc4dh'
    'iL>hkG*9r}7Wsdf<NUf`oaOZiSMvWd2lAGjjiZoP^Zzm@`F}Cq#uxWnp636>xQzV21xNB~KH+&R&XxCjz>)KN2p0E>Ggr=wbDo>r'
    'vAy}Z-dB$A{@eUq?~0>*qz`#^o|EPAd2x})-@yv!<??xPEq4}9&wX;9V3PN&w+bin?EJaOLk`Z1lRvfd;@c_vD$c?AZsv6VYCC0L'
    'AUOZNuX^72FtMHQMoz!)bNv#B^~3YsWHM3id8cyYd^c^)ueo$?Tk6MmgVcUoaD2yNwS&yD9lXo4bKu&)Auswjodef?1J3o5&uweJ'
    '@p>!wTRvy4{iYoDTRA^1dNwZWuW+`0TX1`nyRYTtbJnaEKCdhK<N0I7k)D5WK92Z2w)V$-;aJ`~m&PyeA228L<r~N6VY%Prd)|tZ'
    'cD&2W;~eCf9pro(ZLf`^Qf}p<+{WR!O!7*(i9>nLrSsUWf5&w$x!S*lv-8-kKfXB7AAj#zakW3HJU#DR`-AtnoQw0=wLfyXm5Xv4'
    'r{|(;f3$KFhw_5MbK9K%jP0QPFz1py-Ct9ApB$9yTt2tW?d3Q^`gcszbK$5zzB%4kseU}>{T1haT)rc&xZ=mFJUe$>{J4C-L{883'
    '7C$cESDnLi*46LIO>#>v`CaGId2G@1Sd62>v7X;KJCCjM7UN^V@j0|Q-U=t>e#rwp(|I+~->mZVoVDl~%XK}c^WDmUyx{QMwu}#u'
    '7xtXaZ7Ub@f-C2?w?pFWX3yo^_I618T<ou%hwbl)6z=ui5#*luz~r@eObYk<-idJe+-w@>wvJzMIL_A`uNTrd9}wR!IT`1EzIMgo'
    'IA6%KbDucQ{TwcGdae@3xu3&z4$ryTIOnos{H{3L&&gam51Yohorhg<IL;TGorg{1+|JFuaXLQy-0X_OalV!ZdX{nI=WCJEbFMhf'
    '{d{fapg&MvaCmMO$GM-I&78^eaqj14h0|vSWM2T<OB+hqUgwHl)|{^6q2G9eYA(3azl}3L6!LhyF$d!<o&WtSm;BmTa&^3kyclog'
    'JTdscG%oA8S@CPnJScw6;`VlK_M5Bzk2t%xv2e-%Ex2+Xww8O2!s$NOH)r*ul-68s<4oQQcOKbJ58IbIv;74pcJPC9yE<%N>df{R'
    '9LRg){2VTiH{CZod%1oN_a|rdJK}upxhi+=C~wK-adg;z*qO&iaM9jRPRGY#`(bAuANl;R)KB)|&MvRC<C6=&ru%TGm;0E|?iWDU'
    '{WaLHd;ZDxk?7*pvXAr_pzcQ)M^`JieYkt`{gMS2`)do1zt7bDCgOCz3An!Bq#V^TIC@=!IXbV)9I2&odv34nH$CmueHG^@pTYL8'
    '?!!11l{n5Gs{2>leKzjc`hHm9WPga|<^7@3AJ-H;*Zr`n=gfs4UvQ?Eyx&yxA}7Z;-$!D-FqiexIbHWGIMrX?Z|Zt6{pEeGpPZGO'
    'IR4<hE%vYO&G)4iT<mYWa%KPO-h5wb!Nva7l3VOw-J9<>Ex6bRS#V{%$-V${!^hi-3we#}`%TK(cw2EOFLP=9vOFHYKRA-tI6i&8'
    '*uRo~<9T7h)&4EqV*g6?{KnP(NF3|A?l&<f@%S4T@*3Coo0LPnR1W23?mUz${qfC3e;}s;blsPdaycG<<Dh<pgK|}#mix&;{hYgY'
    '^^<j<i|s(>-vt+O_8V9CxrFoiw{XQjXHNa8>?0Mw%byt5T=Kh#6F*t@uf$J&aLJ!KH}|H$u^2~%i*?VETkKzzaa6cimsL)$jc@xo'
    'wcm`Z`#HHkY+r?Lz0dnE9AEjo8eH9fDcliumG@un&DUiM4()Hv)%}-y8xa3h4(+dTVpqDqq4r0gCc&;&obH1xIJT?0uafL)#hJX!'
    'g<a)+m3#C3k_CtMx8N50D);95APWxdFLS!x-uD?On_<P(eTF5s*k_=8i@D(HK11bfeAImgKL0U0SN9pdxHR6zl56`6e(q$!rE!_;'
    'RM-1uTvBHG=Ii~$)qR1=$@*O7!TMaea}=(w;|r(RK8tmH?%&|*I)2G5*73Q2gRATK%4Iu<^>6Oq;OaX0g=_0%=-=yrbtomw!#b2>'
    '1YP$iXYupXDX<QuXD8I3b`I8|ozr;t8OFE{eK=c(26yht#X3|tS=1c34kZrOp$l%$?PVWBGHtzOoLtME*P+`L>nP)R9i{SY9lBky'
    '?s4u2dB+Rq>rhIlhIMG|4_IGXf5`k%^qe`EXF6wkN$b$67h7NQ`$7;8RlRgh;+GYt`b+E3g<ed5X&w5TvvL!M>r2(2u0KdGy1wij'
    'tW(}NA0N8DWIfLp4%VS7PS%%RKc3&{I*R*x;b7g<xia2#9YEah@wVbZUgL0FCV4jARvgO9TpGW+uK3N#x}tEfzFhRL_}$Lc{w<uW'
    'FBkps#?}5voUShy{h{m27cS&A?%b8j{h{l@7Y^lRj@NIC{`lsiKalhFrIhRIQ08Pk_`*T`3J2x-I`lUO^>Yr_m)gG?-;*8ayxKWf'
    '2fT1|AKgF4{9Cx<pEGCAlk5w>%klV{OMW+Tn&!4I{OJdm{Hb%WzBK)f#W*S)tOHh@tS?>OVjL9?)&YfsbtqrA>2Y!CH&}-%r}3`$'
    '2feh6=YQ!DWk3JR?^?>eTfxcs#)pgZzx<v$a&a#wExPbt&h46)z4(sza`NT?+{@WGyO)zUdGEy83-@?0r)=K7a(<s+)KBhlDCPQn'
    'kx@UnPoZ&kKb+N1?|axTx$mKHGujdIGPg&$`wIu>SFPXJZ*afKJz2r!epAlx<zx=-<rKZdeOlaJeVH5Y<rKZdy_|(BdX9UyI){3W'
    'dpVIy_hXv=^q#EklDu5t<eseH_?`*kD1Re!JU-I>n7py)9NdrT{W})r!u^=R^>UA*XSlB_wf89cgL|VAhxaGq_~3FS&JhmoPwX7e'
    'zs%wNiLJeoPXnCXztP$&c{0Mm{fQsrBi(oSF+S4$geXtSozV`spAhAx_U8Ku`4M?rzp4M@rxK2QKOuAX%1@U23CU}~y@TO5%Kd~i'
    '$_uA2IOh8asU2`XVdL~3G+uiw{cgFR(CVl6=aBvu+>CZqKUwZ4w03|zs9)Sq=<N-8nLEQ?;QpL0?+kl^`)-;%y?-tAvS<h7Nt+#@'
    'KXp5R{AaU+?sxP3gi`LxpXU1sgR6eB+!JW+ZT_#^6Bu0aL*<@8=c@lJ_XK)>j77O{PhfDp+@t7a>HqS*dBIixSMJlo@sa#rxlgNe'
    '?hn#^TCKh2|H^$@t-a>|%6(cN<1O8P^)cSk{Z}93E!|i3G2YUBRUhLm-7obq-qO8HC@=ZvaxW9g!~Qsr7I$v8A9hiKnEKts@%z8@'
    'h2+rtX@*?*a4VPMP9DGNPw9M~=-D`kJ1H<h?!1xPL*D+%VVtAovi@qhDW2qVr9ZaQ`Xh5Q>KF1dw@11A3s>UA&DP1RXZ34|3q9-o'
    '8}ugpa6S9|AoT0T@p@W0JI*BBv%E#_9LnXmliwpq{WebHik>~5Ok9mi-t=7KlC_@iBhITeJH0ozQ{;-B(vG&<=@%FKz`~t+LZ#aC'
    'c86Ul$AO*N^L-d6uR-0wapr5a=j}clcWixpG)^<{tKGNyX`rqBLG_dOw&gXCyKytxag9YgG*iFY{i1%{j%o+neb#b?D|S%i$@oZi'
    'pyTM?d>kQH#u3|rjiWCv_6ddK@kU%8Zz4~}+ZPx6T*_G*Sss@vPsZgJ7yDAo$@m33wehQVz~hp+VlOs+Gsold5B37wr@fs1A^Y17'
    'fP1%t`#8&YAy`+?r%7E`0N2+Q!bzhKjqfR8w8i(^ZR5x|3S;~FW5uo3AKRVUaq5MtEq<=@E)Ji2oU`2)=VY$NIV*XqIA`<z&0LLh'
    'ay#<(0Eq8N&l=wY*W-KPyg%5Uu|GV%mv)ey3Rm>!@qOYXE(UoK7gsLJi?}#*Z1=zW1GvxrQ0`}c0Qb=!=lge4I%(+R<9z>as+>+D'
    '@83;v{!JYFQ*tkT{{7@&{$(zYOA4THUKRa0cbfmZx5Yed9FE`Zc$bIccU#Qo!X<l=`i1`kd3w>YUGu(}r;S6q+OpqWa5LKRQZCxn'
    'w(#Sbo6+9l$M5s~`yktkjq~&UyPtAyFK^%Ta6V65*h`zwKRKAsnX~UvJg-)HGEaYUFrN#j-;b1A&F7yS%;&@v|3_a{lAW?2at`c%'
    'G4Bgk?9}J|DzDh-B0ivPmFoXq?6mp67dvhK@5N4=|6AB8MG<=c?soM1cm4c_a(aTM-K)FgPCKvhXi)P6PvkUDW;+)5>Tb7uw_0%N'
    'zPUBm@6{!ae5!NY!To;Q?UwIb3ohM<x90l&w#4Ofse}7{zAJ8ZpYNu59>Ga`pYFk><)F?B!g2nKw4>aEoAsBtbg$%^>-XShJ#+p`'
    'E?4hG%=$}Qx<7Hv^?PBn{y0x&Tiw6=i?e$rSKR9U-P|9Y19`#8{jtUF<v!X+fBfBa!KHg^-?(~jEpa~HGMDagZCtS{_0N8P>?_B4'
    '0F~qWW2M}3&n&&PJG|V))%s<Q%Psf9O1V7GymC=L<aFIw?r~L)=9yOx<T)qzsd78&J+3r9D1T_dwehy($~~^6m$~NBJ+6(@@mB9O'
    'CA+`YTpO2}lW|n<h2?QXTkbDh8gGSL-3z;EzQr4t#+!3<U+8Z%yUJX;cQtdTCP<WfSJ@6=Tsl|oT~*G;o8Grc<<@&S=?5=2xOOjR'
    '<#e8I_ies#?Y_+=cUm5Dp3fJY%6sDux6^hnC)$1C(*1<5T)CGM?Y?m7Uc|<U-M4!x(e4YE?qlp6+kLy|6YYM**}a@AZgtNm+Wm?H'
    'dBC~dw|g|v?hBXh(ac<ok93bFZChM1K7uRvXe#I9L+;0{<AeH*?bQ3txpt3c<yPZ^?qhu6+I^Nwu8a?wiO)5c#>ax={Cn?@y_S29'
    '!nJ!Um)vQ2|Fzu4sk}Gtw0%s@tLJ%8^7(mP;qe-9WCuSv&C^$o_LKM?g1O*8-V4Y3qV;}EUYFequH28g=KB4Ze6PV=aOHl?#%V$b'
    'w3p8t$i0%YbJ5;Uj>i#maxNk6sdTQkL*(6Ol?Uw@F@DDv_gh}Mms92S`qg_m;~q_ZM7FIjw{{-@acw=w$xFMQd)IXeaHpMnzqfX8'
    'fOELcBYAO-{;ph-SI*@JhwH)Zc$bIk!L6O&4=&>IZE<gaaAo}_deQTj*k0jIJI{V^?fkxTxGodD*m=&oa!Fn}mmeIi%eLcPUgqF@'
    'XyamCwzYHqZ(Kd+&s<seY>V^VuUt9bEnHrwY>V^BuUt8wtXx{BY>V^6uUt7#%v_7xOMh@m&6-R7QMicPw|4&bjjQK>g*)9(Qk+d2'
    'qxC#&<|G~`uAYZ=4&r;-iWC2Lc6kur6DNM{O!9jCytQ+)nX~xdg==x*hUZsZ&nphjuQo2?#I2o&edFqRSmDkTA8d<rpM~T3?H6bB'
    '<+eEYSvZil<kI}REzW%wj^kLgtMShLL7v3BXnzCdt-`UqdXCgNh_lg7Tm2x;MmtUAwm5cc=SVY`>~z7^xN~dgNHb?~=L=Wj&TVmy'
    'v~bcNKRCC8#W~W#fxIP`?P_t3v~VHslT$lboHwPUAc%ALykx{VbUwxA>EKQ~S9x#kT&i<2pNG6Sr+HT{$t&kRgCjpA=QJbES;>=U'
    'zjB-t=Np4t<Tt_hP~kkz;d77?=TyCToFnHY@2#B=b<XsX;+)zJk8?s^IrkZy>LtZFD|wlN^GA(4?VRSlwR5CzTs=q1+*|$-d>?$}'
    '%K1UzB7RxO)A;3uE9c*o^Y}%$eqQaBE9cdi^Y}&1Wwrj``EAXm{wUmO=e%lvd~o%AnQ##2@G`2Ox5}KHw}N@b&s#ZXan5$&{L$rE'
    'oTHr1A0h8LA+L|$1?6KltY=;C)B6?3(VMEl#X5e$QGg{Jo$H1B37uo#!t(goj+V>o_^WVQu5z(HUvN~ea8j<{W2l_w|MB~wTtD33'
    'xC%$*2Dfal=Jheh<>G!s<y4+>i+1=yCDrpja(|37ao!*M$o<hd>5qNn{y+}<Bg&O_6wdo2%9VC>PWmIt^?NUs%l)yB+#iMW{@6$E'
    '59F{vLSAi0?vIdH+F=KzLVtXZ1Kfw~TxqXze$TOTdXS3W{i^a}Tw0pBa8({~cHoNNscHJ-I0v}7BUkp}j1&D4*YsC8mDltKocc8='
    'x9*1(Zkk@|ewcB!+`4~NxM}*!`%+J&cFTLrbX@I}_o5>YnG$*QxrtX!p6WPx>pOGjp`7PQQ^HS`M@^RZyICH6*HC$!3{p5Rm*N~N'
    'cN(Y18&7#>-rK?Nd11LLPOb{i?GWzK<Vfw{_r|I`ew1qDc8I)aM{v0vT5hyMjzxR9l=egAo+Fj33#4i9_t0mO{9d$j)7ndkZjo<W'
    '^|IvT3gM&|<!IeATrbiccatZNb&Y6m$g}p^wInW&+Dr0kdu5~5+ItLbZ>%qw<98m_PQ5?KL90EJW2>C^2RUf7`<XeiXO>6p6?xp='
    'Dlgf+$P>LJdByH&qLFghLBDeJ-Ae494`v}(>c^Qzcaj%&pY)=3Fc)0Xi`mP}9NB5oi`qezm&TFED|%UsBWj0~TiVga8(%`6^&(uU'
    'AAgB0dhzil9PNrxJH-Cxg7b07?NB?N$YHrG@7{%ra(NbHJ=1}|-XG&i97RxLrRT)SV|!zzzb_8-M>uk&+|XahGrcHR^p`l4SM=f>'
    'tyC#z0641Oe{p(Bi8)%)B6mo8TRXnECQtHDQGZR(UtGu|HM?Kq@3qN~llxQ7{WC3m;(UeL%W!$&$M@0wJwJo+%DKPigPO>3M)%m_'
    'oQT?AEtfNNN1qpRx%!CXX!C-6t(f|5Mk@Ew43{f*1?Bquv5!7~M7c13@OSn!e}tarzR>e%<I=dSm(j+hAEVFm+PGYDw@x%LE`bC6'
    '=|n>(>Izrt*T%13!;<to+W7VBRWjGc?=$W1Pr1h~?cjX|%4FF293=ExaMTXt_RBcyH|0(_kj?uHAx}?zW{%}4r}B7v!#MXF-VV}p'
    'Z^s7*<F{}l*Kfszol?J<yk0-%Ms5di;jg@Zxqh{Ozc{R)b1{Coe#+%?*{>x#ZT9@dwQ`Be_G}zK+cISx@c2=ThwiPc7Yb+b%e|HL'
    '0&^5VZz+xtc@Vc3F3W>BmN@@l0r5CB1mkh$rpfcT_})rf%$y|_K)g%xFy4JQj{mw|a-7KAvb{NOB914dEyV}Ou^(d29%PC6mpL3q'
    'KRG*1JY~L2+#%(nJ^$pIyfptR7k2uS3wbtAbAQ-89sMiw2XoQCX3x;SGQTkg{cH14^l!+U(I3<0m3bj^P;QwQm^<_yIq=Who&9s>'
    '!avi375y`C$v?Y1JC&cf@Xsz!{j+dxFXnf-y~VD+Iq0{-ja<JK=l+@XhyHoNjoc34!cNWaO8v4ue{)zr=iEO_{lGs5m;A2EOLqUw'
    'wQ`ex)^fo=Uo-jVZ3;)<1CoC>j;^j4{K#|cH_<rq=S^qw&q*HoXLV~bj%eeN$0eQD$$nRsWytZj$*cO)YqCG(6G(#}Z;tgj*H6}O'
    '#`X3VziV7+FAqy??;M?ra(CmVm%G$U@#7DNetf}+-yjbBGjU}1#HI1}i!*y6&fX#ap}&hQ`L|w>`_c=}3tYcL+MCAPFD|ts<^|MW'
    '8b`mlkO%VzZD?0JRevwbWaNsSGDjD{@b@0QM`Uuo#ZHMMo8H%Q+J!;D(fDQV+Jm!;iun7C-Agi69_6@IdGuWa%iRZ*dyWMs<vv`L'
    'd-?@Q{2c<z-3OG5^5)*;(XE!k`9($i-9S11b>ZxyBHq8ZdsBM3egP5hqZf{zu`_Ot&P^?sp2e%>@;UXSKTgab?rCha7dUM%i3`pz'
    'm^!Nd_(SnRUe(_*R4>HEMNdc7U*@76Re!16xWMVC`a6c|kGVNIH?>^VUoMvty5ydnqn68ue5P|MFE}fg&3SaLmdnF~IlZq%?-5Dk'
    'P0qdR_()tHZ^}u(>3t}6FA0vfDo@5ylxyRSIqToV<?*JRmn-8f$~C)h^5)*;ksS!9_HrLO-k3|{O*z+}j5oRGq?fDxb{{&9636|f'
    '+#H=t<E@md;|TPp<BiX2M0<hD<4rl!pN==spW0uOSM{gkNI2J@jyKR>=As={f2my8pN^x%ss3QRWiHu$Emy`HrL!Eh+!$|qva)bi'
    'Zj86g)pBjTU9-$b{XQ}tAI#zWq4(zmr&%qt`1{UD_RuW;zTKxK?I14sUFMFV^4t!DtK}xn%T0b#IW5=wjXCsxMV|GCa^e4qJnIiS'
    'NtOIizfVi`T>J*=5B!F3V5gna`jv6s?njFHrSXRCh4Cg_EjMvqZW<q`7Z@McEOuYyg`SJu7kQ><zRXS5DNhXB_J`~q0_DyFIoKCS'
    '-1LWP`o0PuOrY<7KRLS%%JxB!i+z<W?~4n08t+Ow@_vb((^L-HoA*I7$NLAIzgG7x_|4B@<px*xErjFeih^70Tku<+Ro-IXLb#CU'
    'danBssK0Lx^jEl%>$l?Cz6Hzc^{e|9BG0+#-?|@>+wsL={hVw27EwRn7kCzCZC~KtE`K)Cx${uY^GoOe18_0k>b?MsBi|Qr4%S<V'
    '(|rM{UtZTz{dirA9M_LH{~piv%Uo@*tbe7wbHU~HFLSfVOL}2>s+YOoqJFz^E)V@iS?`A({Nl_Gd|%+V{w~X_|DiwG7x=9|<i7N$'
    '+)w=>_o+YdlVzVF>+g#T{eeHN`v>4BegD9@V$Z_Ol%GxWV95v8c6@PS2aP*rUM=~+6#M<)#9o4nd}Y#0ub<rX^v+rR3a5JR_4~zH'
    '{hXWoqFjy<sD66G**mB8t6V8p<>`F%#cBP3OXG56d16;z9FAX(aen6sBKMX5=bVg7KFo~%{#tM(Z!7*jbHDTdko(H(Q|@OT9&<j='
    '$o(`pE-8-T`GdLNd3eZu<<}|qGjHzJ*NL%y=nt@df61Gx+*{rpa$k9Km3zyZ3+_8_4!N&<IOk+O;==?uA6*NM?XS#7jjQ&o^U+n?'
    'VO*JyuBw-6_c|Y~<dypE#)Z7!`G1vr%l|{}EB~)@Z~1@0edqrn_m$VD+|Rte%Dv_F1^1oT$J`(C`jGp|>kIBXuMfGed_CoU=IaIb'
    'ov$aH$93Q1DB`;BaTM{|_c%iCYaB(q_C1b}`xr+Nhsk|k#otSO#oX_Fy~4fb>mm1*hgZ1QJUr!o=GPVOHNWoGSJzQ5Wu6JW{2{*%'
    'xv%`X;J)+gko(GqQ|@OzTyWp{aF21}IZ~RZCH~v&oU7U22d8mj<xbfzmiW)*(Vo-~PUFPjAikeg?v>X8UmUIj3OA!2*J$m1;aYoP'
    'y)dmES6)|qak#E1+zh?g`Py?;ZsMx`{M{SuH~z#R?Uk#T-#Ke<;c~y3JbQligR}ZMceQ;p-lxHJ$`^<0l+5}58n##b!3SsZ3Wxh}'
    'Q9oVJd~vw$$(--kq5c--X3pdV*Y@F{e!4#T;L<uOalQ`+^^^UuFAn$hh{N^oYW$iXdgE}N44m%o_VM<M!*w!qu>Os5N3*{-uG$~2'
    'f1}*d?B$KC_JZr*X?ng!>)$sn`j=LMH*K?OhK|p_bnI^D?>KynDmcEAIOcuf&bx4y$>Zz6kjH8I!Kpl3Uxqy3=z~hCAAPT7dGuA|'
    '0<M&coXNXApNp<*q4+A^SG)M2p+56y9AB$JT)daSQCQ*lR5@|*{sMFMjGg9(?R@QJD)$<tTuTrW&da?<DVI1Zm$@icI4{@ov{HLz'
    'y(;BCh7VkBuX0>&;!1mi<AEvMqP?<?D&;QPt6VO3(ca*qT(M`0*ub9Y;RLZ~K5P%%Om@$YmV@0Z#}O9V{kGp~_emZ{Sc$vy_+ZXf'
    'TrfVYetIbca5Ie~t6$i&j-!y5>R04x{eZjkc)O>LH_#uABd#BhH<zc}OyiR42jh~t(q5DY^;2%9@oVz5e)Rff<YS6G`}?pkewh>d'
    '<Bf0RaJ)Sn<S~Z4IzE_N$gB2D9NQJ$FE4o%^f@otA4TKAou=n|Ti7XZrf21{oeD<}-f_8<j*-jN-L>FO>yLX|*dK7#AGzG<53vJm'
    'Z?P9ES2$?z!mfae_Acy7xYFKYS5a<h@526oi}rT=oAv$Vx#|1K*9Px`0;lh*%}wu(XU^VFRxaLuqvJ(<XlG0B@d=0T|7y9MuM+Q2'
    '0+-8G&ffoJ4&S+ra??AH$jv=-_|Btnz7;I}#vIMR=jQ%TIbHILo--GE{=rRJrVGd4SWnHvV~(y}=<+_fkO%MKcD;Z+cn`Ph#nM{x'
    'd$?cyD|s2*zelYfT@n}Nesa)`csDnd8}Bk|S`fU4J2!o|D(smbyQuHs5_hlcKEF3h_jA!aE$#L9FOfS<FL&WYFZq2~ZpXbX^jF?<'
    ')pp?c@OI#PuG)@1j`BOGQEnX{`5jc?%J`u7O{YrK@j+Z0AIx2Qtdk38cJPx^J0Onj-u4BU>*M1m7xLh})UFqh2k)hJy+qm<zL)xC'
    'FZd4Xm%ZToreF4=<B06wsO^pM_LBp>#5<^|TpVxpeN)OiJZv2K`=*6k=C{i#ue={h<#JrNrFSirqy3@R{Ckk++$#TGR`K=yP;G~d'
    'BY!`%aM6y)N7q$%eLu8wvKv-7&c_@(<gM#2SAA!+<-zlPWR2^2@Y=s;%jaLNLzTmP^yNDA4;+-6^30iI`)l$(xsb>EAdoMg`d4@1'
    'n45d!#zN1$&+vABA<C`s!D{~?IMj3Bk5Def2dn*qKX6#T(jR@_;tw3i%kc)4EB#UH_sJD`*uRHzwSJ#m$SZNlo8PGM2G-C0<Zlkk'
    '#q$fPeqG)xr}D}>yxE`HJAj2-o?lS^_r>|Wm&(QawX8p~gDt%e7M#8_n)U4Oj4H=|_wBp}l>5fj`Z>2c*P(v=i(`4g;r)}@-`l%*'
    'g)9C(-o^XD`F)nk!TYscp3VzjoZn~JxHNyTJo9T`9LY=E`F{Sx=9w?f@5gLhKPLiq|H?`IoXh88VxCbuknz^e#T3rQ<xdXEP3JXY'
    'K5FtlxsWIGR-8LY_H6Uk7sq-5Ztjg63p;q_iXF&2_;RiY+wsQbek<p3VxHl=|LC`J9;a}j=N}xDTl+)(Zj<-Pg*<q-`O8n@d(2;c'
    'vYf|B<;MK+lau<@cbn7t*WYbUTwnkCyUohQd#PnTWAE@Hw_49^u9y0baaz~<JI0CY>so)um^rblIF}#mM*czUDmXt!&-G(_IV*SB'
    'Isd#4r606EeskU*%AIDXx!fl2jRSdPr(AAX*Vg)da#h}Gc2DJsU7ag=Z(PWOcT2zQ1>Yn6vKO&?wu7U#!^g*O4(q4w5Dwe1koU%^'
    'yz&n8-1Hr2wo`itI&o^x`VMq(V$bCr=!d&k@n3!4d2af?bBX^xIf$>yyU5&cTlQ=A@IxEt+rs}bM{$_nZz1K@`0tae^>dEKFLN#a'
    '`{W@0tM4ppzo~z*ca{@}{f3<P2fnkc{np~i`hK$ZM~f#vIfy6g`^jCN#EG9A#FK@4>|VGUPkwR`N7VP2=cey5mw57%gLtxVT<$8K'
    '{Nx}mx%J*;oENr5JbCMV$mpN9MLhYNgK~>M-4^lWZ!Y9<oap72@u6|zCkOE)b8~OpSlGcUSL`63g%WNRPkwT_-`ae>E#gVxN`EZk'
    '$=@85Tl-@XPyXgYUY##r{BD~sU;J*Hx3)z*`J3bV(FJiePiFNUOu3Z*vic527aFxZlr7GuY?==e9OPwW&M(Sp`6XMNC&}_kzD4Fx'
    'o?ZZB^5Wb{k@s*YFL5rf<)LhGzGBmSkl;#tgVT#37x^Vy<nw2Fi}nVG@_KtU|GvoU?F}yEmHZO10}h)!zXZ9N?CKfr$*y`nNR}tx'
    'U67l}{!E_Q-|gp_D2=DtA0<rN!DF*O<&ypJ!A0ln08+QVEKmAFxnzGuo+fg4`z!LeKSEyOT%OrqYOkN~(f)O=v^O|SP&{TFxa#(o'
    '<t^G99LnqM_46M|UT<%3A&>2f_JOPY$$F6O1-Nd1v2IlE+Ere*KUr^qJm$Ln#k!0?x|DNwknh6}SMg0Jhv)myJFPX}Cvo-M6Xg2{'
    'M>m}up6`?8>A9lBkzV-wWy$x^d6nV=;CjA~arc?HmhS`ev~t(3<)(ZeomZjUYu9p9zK?NtlGpQnV4h}<@^eyqHJ=976~Og;ALH&M'
    'ujl(fJgHo1FUo`V3fJ>}jJuP(p6>(k<UMuYhwuGO`$PN)u<Z{aSN4aTqxH-^b)Tll<9AkIKL@$8pW~d#<AOym{5`<)K<P8dChH#H'
    'IH6(ceoo@<6F5HO&79|{(r28^X`YAd-%GiV-g>#3=OKB>cjb~iDVI1Ymk!0$a_8RKONwE6vi>cc*eP?@uAJCua9J-XFP9tkT;&yR'
    '?umQsN;tDC;bz%~%l;I&vJXdgdM>!qZ`2OfUv0-3{{Gf>2v^#1hQGhH9m+wud0ZyF=(r3n#%1O1BrnEg(qD{A;bz%SEc3^2j^lRV'
    '%6_8hxygIuio7%C!KCNf-ZSRGq-QMm(mWaYepJRA??+T_T7S?vInm!NoFww}amm+ORnGSHlDx!mds$u?zt@VheMgoj?L~QWZ|xWh'
    'ySnDy>Ngg4CEVN-x3DYXX4wZ`+0`cpcEDWO2VU9LCs*WE{f&iP2{-q|b-RlEtE1S}Q#{xeaK)}34(uxOw2op|BJVyMSL{mUC64pC'
    'j$&5}dBPRDs`AvXupMkK#D!f6SLz2`mUqrQanx_jfu7Y~aKByb#r7Hgz=a(MSN7Y*UKaA+xFWCWPxAG8d-;&uQS1uZtNZ8?=h!|!'
    'FHts+n}RF*{LV?7<6Pb6=cUY=OZ)ft2K(sWT<oI@M_*xQ-EUvWd*fc^;eNZx)41e|i+%Zf>b`f;v&M<OFOOW=mv_$fCtTf^S3R$|'
    'wBN4nu=wwbi+y?FXgN6Re!Iz2KlH`LzI^3izg^{-zxv{0KUTSO$8u%A-Rmdg=!=Ve`O3k5yVvhG7yG-+oh43Ot)r&yw`2UWT=)Fs'
    'pxiQV@qYVC-X|CGI7?yH{dUvKaJzryVqadkxi@Ys?BJCvc0l{>$jN?t@3&Vj_gjnaSL^+$`|YVe7VGoh9F$x8<Is7b%KPL(UY%!v'
    'i}~m$C-Tm(`<BRI>3+`nb>C9#PYRd!bMk#lojY}ZE#J44xbsL{-*+VL{hl3dhrR&!et%BvI|{dGhu?S8xzvub@2FgFN7+wguI_Wm'
    'x`*PS&G)&2OY7vs@nN~6?{lrzwa(@BYTchiZhoz&&!g{~rTVGg2rjKx6L%+hX}#Lkjn3uuVBHr*ZoaQ;C1;&(1DE|>%9*0)iRGRX'
    '*`DN!a4Sc*r7?Hy!O^xTbJuivPi;gV-&>aC@$<y8|IE2skM%*hnuSt0y2pz-FPFF5fs1zRNuFlE6pq@lCwaQP%N(^s>-Tspsh_n2'
    '>zCWRCl1P`fy9Yq*bXY6<<Y$<!L|0%f2G`+xY`cmbX%FZYxi=;-phS{cFxKTF3L@umizp=m22F!yZ*-B^+%Q(oX8t{*I#hc+wpXV'
    '$dh}NayzcMw{qp)BPn+-xRBS|%Ur3S%j5e{IyY4>E>HDx+I`40(Dgp#XX29kfn|J1(&3c%VR?dMj>l2t)fZ06{p9q%%~Q|Muz%6}'
    'i?{Pu`}@i1ICsv^<FJ1*?mnx$H!kGK{ZgtIx?d{mMXtAH4)j81m)n~;)5{k}-(Z_Ow`aNj)VL;Z#T`4Gj~ep9hwd+?K*v8HAt(2+'
    '2)AFxaW<UYU+nVu-Yt+9`U_6(P08}a?=nX>c|?23PE$M15gfGlgL8YaeQ&)FIoZ`WhwX6A=X1R`dDDAhfD66wt9`1MaaMW2-BB*u'
    '={L8OC-K1uJ#)FeejZ0yJ8tJL{4UP-@5cQg;3u8q@5IEx{UG2cnX?C2*Yhuboi^@co^~$$mE0$NlfSS2>YCuMmT^SL3vLxhBzYfk'
    'Ns{*wmzX@g&r<YE{@%U^;QVo3_}xDGqs||d3we3|aIW-Qoj)o^^GA|r^T#D|cJ1GgCtu@@tNpv;F86;tzg3Q}b*|jpmAi`nQx4|K'
    'PkAt3zRPoewVHo<BcySC{#AeF_iX>R1GyLRw;dq&We1n}(;s$#+?O3V_XoYa$0ewjnD;knuinQEe*70_e$qI9Cq(?8a^ZJ>aUl=l'
    '1Gxu0`yrjruL<!1$EU>~WDerkS1#fM;6}4kh!1{nVW*4u+4}?L-*=9nSeGs1Kh_^zb{y*{jyvyxoUWss3we9uG=3p2)-xcltY?gC'
    '<(Bn~bG6*Eo?*_{GaM(ja<37bl^a|hm(IP$IXvEYE$t5!+xsL>6r0~CF-{*8w)akyi}x22r}6z${X;q4esPY!FR(m5V>`$p@O_pi'
    'C+o|#?49HKeRDe*77e3a?$M-tN7`i=%E`tf%cK2zDVLvs$?_6s<$iGF(WaGqjan{ET&=xy-5kr4Yu-Dj<$iNdd|>jP*+)3nbLLFm'
    'f_whSIO?q|kNw7itMY;)N2J`?yPo-3fX+2NFS%*;dmNjVJJ+1bTXAz=$Q!*Ki8FZ%?v&@~clts|$%IerymN3&CJ_DR9DN}aj$?b}'
    'tUvfrzLZNF!F61Exxv|cJFlFMUy)bF?}D>;e!e+QL?(H8oG&<A|GsdC_Zxl427BSdMQ#U$1AF=4lD#nJc2GF5m&&;vpghv^g?3Ol'
    'u$Rh(z0l4x+RM1YUV@{xW_uanPx(5dZZFgh?l*6TbID#-+{#`aPjkL-$zEQ$VlU*m&NY|pWx+|jVg0e!a?epXmiLp>`i;Go+c=f?'
    '#z{Cy{Y&>A-5kWyhPqta=<^3~WC!1z*bB+iJ7$@?&oxK#zBqkh9O}0ZD>v*fxTxPJ$9Bpb$GXb7oyzHe+zyd<pH&{TW5oCvU)*nb'
    'TtAkl<7k}A`U!VOJ8tJFNvp*<eZP~q7MD;)tHdR=u8{ZuIQo!C+;Im-*ZBrl;ti2U@kWssA6SV~dCVnwa{H;zTa?hidggo@)nDRd'
    '-Xc!-q&A<ojDvZQ5-FtL&Mpt;LE@x8&LpqTGkyOwbMO1C%<(6yu=|alU*+3hHXm=9W4r(0(l}y{>`&hzpPgfWk9r>O+#lr0yny{N'
    '!2Sxy@?;I_@1zF@^AYx2s~^lq*l(%a=I^;b$WQvZF>|Tk7F_kug*!*#%s;<y#XoO{`N=c)Z}HC`T(*P5{Lq>Et@zX5oc7yce&~dL'
    'yAJR#6p({|;rp(2oCinBK9YZ-kJ!k$f1!XE{7aSR{)M^lFGU{u7k0aD_q4p#_992y$_LsrbKYL`FT9!LcG~5ce^E~DG~`|VK8lS`'
    'v)jD^vfmWk$-e%RlM4?)9-TS{Zk)iOyf^OB^PFH;!0Gd4$`$)tb8~O<XkP&A&$%kEb9^oV+e`k6@AVt09l}9-U%ArW!i@{L;&<0v'
    'ZZC6`w>e5XuI|ShcglO<%+dD!6F1Rg4Ohf#Vh4$%2~IdVe=eN(A>-IiS>ADny!)*3gd=&viM;#F@=|~B#}7Z(o8)PK&^Ef%597|x'
    '{Xw3#V@#<Z#+{vGdGdyd-(v&Zxo17^BkOsbl@mSlM@P^za;WE!cb`=r>N(`yXO>s=Y~!ufFY9?9S<j98gFMu8$gAxrdUkn*n|swC'
    '-{+zF<G9JVq8H`vGjsaR0B!F!dFpqSQ+W?p<pG!dLDkE+kmGX4zR+{${vc24NAjAUI|u6-&@*t!4@tSaZ+s^I;(iy}QP*3Ao2KWw'
    '-b&mb%B}6K>!`v_>$kc-N*wBi%XN9@vC13i`^CVW@!odde-^IhmykTW-?nh+`@$Qi>3{QmfBcMhxg)=1Ywvgefs^kV=ds9F+1mTv'
    'f8au1&qL|^aKN4M&UfGc6Rzf~B>iPB<(Is1py!u;Oy*i%3&|V%4f{jRwQ^S+=Q^IA*TRXQ>D}<kNnVR^_-;6GkSD_lsGPrXc6pE|'
    'BOK*hoJHP=`6VOQFZ#D|Vpr+C@;`7(d6IXN+dIx)KhLW#?-~II`94`MrCiAO$$9~KHQ%T7FC`ltt9+kVF6Z%V?Va>LaM+HL@3Xac'
    '((P{BoR_h+_s@ZY@9c?_JQ?9?9>uW%r+#;pC-cI!Jeh~Ps(-#F_-B2e{ocy^?8?=A8Y=f1z1*5lL*-WgyvnEfkeBjl-sHI-+U$E-'
    'c|V@HmUpwYcg=&V{hQw*?_9{kcgTS&cHr_P-=cApACctA_g~=__7d_qesQka%Zh7xH<`P}f}6W?SMkrQyqgbsDevY@9?ZX++z$fp'
    'ck4L+#o0Jt<?)pIouhMeSMDl)XpzVBW>+<j=gqEa9?zRy)jXazyQ+CSZ+6x4cs}%!@_1hLlJj%OpGrQ>nfvXFi+<~QH_5MQyy2Yq'
    '1C58kuK`!{bCQ3_T*{|;<G>GTJOq9yxR%F5@<y}!p2zdX)jXcUX@B%Qo&`7cy9W2iW)CUS&9$`2vFUrCjnfAbX%FEtj_uDmiVsZQ'
    'ahtsRtn!4@#NpfI-6zW9cR{6o@(|!N&c~vD_U?mm$8B6H*WV$6cF@As+ClTQbESUDas8aTc9%y7UWz=96P;6e%w>7NsbAadp;444'
    'afx#wkJj=aFF1KOlI8Km233DFE}av3!WI2FH}@`&H)}S153+O9^m2`+7k{S#%N2R7mn2WQY5KcH)1SN>>Gfm%Mg7FTRBoD{uhI1E'
    '??afpRKFrG>L>kijoKfa&miT>g#gwclE>(J7LMg9r~M)MiNLv@K^||0r2a@8_J?s^Ki4yqEAp^E5{La^T*xy$vpnw)$lGij_6OwO'
    '2N(78{(!vA#$kUz9z5*;hhO9P6#SpRcigz_|NI?e;COwsW&g+DU5Y&6vi}n<<eC5DxDLi|t)Fv)x9m3JHhj1Fn~Qgwfzx&*e_Gq&'
    'oXR6k%1xa6UC<x<D}QGhxS|*3!tY*3_+6ggn!Ir#r}C2D6?wo}Jh^4R>+b{u7xKdIvb^Bj?{a+A`;EtM;wT>K{q~EC_kV$t`ei?^'
    '{n0s<SNhGlx%YOE|MT~MJD2=@>5t&B9r&K`Hy7^-16SKC^$UMhxHNwhI|vT-!u2ci++OlL<L?-EF3mH=u7cyZcx1h-<Yf-mJ<f$*'
    'V%}0aU2$pNs`l)hmYeh<@~*G@HtEBz?w4F&_iYlV<NP{czl7tuv=2i2kGy|y;r*CDINvXkd|O;s5Xbum!O;%+QTIzSH=}-Ke<PP0'
    'T;1Pj@~j=d<SF+p&(<lCUu^3X<Y2#q9B*3JKK&-^+Ux6nQSINk;L5s|xS8aw?jcn>m<z6~Yl#ba3wsH9vJZ0M{h~iO-v{CNuW`J;'
    'QMt0eLASzB<h0zM@{IeG=Xp0rUB|P$b9An(<5^zf{$K~OZ}Dvh$bH#??=$?N9iW%bcKpSzko&N!*pHCB`r<cay&s&6x3V9RIq(N%'
    'pP_L!&ObRA=Vd=4agq0R)O`lDtJshD#f4qfeFp50*pK+)CdSz`nOmH_T^MH<j>9mT2P3cQH>Yt#=H$D^7V-FYVLV<qk@s+srv)6u'
    '+0)9say<UUVLV>A8SSvVuVuN3Ywd-&eOf!N9Jd#4Mtd!fEaXLeAN?lFvWV{s7yZG<?*7JEI}%s=P0RK5LgAv{q}<G1?Rz7CKf?I*'
    'i^KRdbFAg67kgnBxqWoK{N$|M#O3dt)(($jGpF^-`di5J@1dwa;M(_4(4WSM9~{Q9ndAEDy3F(^@oC}qkhlMt!|$Qa<?o@Ozf!-@'
    'pRNZ@e=B+Z-4yf}9Io?Leq&tU9IgkQ^LsG*ICl=#TOn^WyMN=V-Qzkc${o%Aa6L1vKd#a2<&CTMg6ouNdcM*+<>LFUX;nk{KC;H!'
    'G!aVkC;cJv$P@g@dA`{+?#lV6g_|Mo8f$ryZ}wXrbKmkf4-ebRgFV{854RYH?S17+dug)F`LTtYArI=8IBf5iJZ$fqJX*q)_Hz6u'
    'oIHGETxsu`yEH#+4(G0vZ<{$;BNuu4AeC{Rcl|@2=Usoui#)uQ{>Fuz<eUBAJRdH&v8Z3<uYGZRFFW?fIK-|bf7km>IOvaeF54e*'
    'SI$>1+zffwSjz+Z`;-Uv_bRX0A8~x2`ABwk9>xCNxom&TT`B)Lb80VHp4-cL6#M&>2ln?Wuh?JF-?)$idwJ)w{V_Kd^(*$b<SgGi'
    '`s3Klk4L_DaNOQ4^1`<-?zcQS=deXyILq_A@WPQiUZbeI$|bw!a<824UAP(byT+n^$?m`9h24M3)4b+s?YMIOc;RNW_ZqFeW!^eA'
    'n~x%YJUHk#2~xkf-}12ELZ0WD7f$=l<yEfqoB7?yA1~aD`hlJkhyC^?5Bu#yUg|fO=lSS`o6%nAH|MhdJ2soQB5yso+;1GKy>q|i'
    'm3~uso(EsJ=r@s9x#V}H+$-g0XHNWNsh>SWe$;vYTb}48^7OY4d4DK3&ShzPuaxhdIWD*AZy}G%t@;Bl&kNN~$Aw(@@lQ_k)>n24'
    'T$(>b-dN~4&mW&$D>voK{{t?|7*_'
)

def _load_db682_c8_language() -> Tuple[Tuple[Tuple[int, ...], ...], ...]:
    """Decode the frozen exhaustive labeled C8 crossing-order language.

    Each system has eight rows in ``_DB682_C8_EDGE_ORDER`` order, and each row
    contains the five nonincident C8 edge IDs in crossing order along the
    program's fixed orientation of that original edge.  The data is not a
    probabilistic cache: its byte length, row structure, completeness, and
    SHA-256 are checked before it can authorize any pruning.
    """
    raw = zlib.decompress(base64.b85decode(_DB682_C8_LANGUAGE_B85.encode("ascii")))
    if len(raw) != _DB682_C8_LANGUAGE_COUNT * 8 * 5:
        raise AssertionError("v0.13 C8 language byte length mismatch.")
    if hashlib.sha256(raw).hexdigest() != _DB682_C8_LANGUAGE_RAW_SHA256:
        raise AssertionError("v0.13 C8 language SHA-256 mismatch.")
    out = []
    pos = 0
    for _ in range(_DB682_C8_LANGUAGE_COUNT):
        rows = []
        for e in _DB682_C8_EDGE_ORDER:
            row = tuple(int(x) for x in raw[pos:pos + 5])
            pos += 5
            rows.append(row)
        out.append(tuple(rows))
    if pos != len(raw) or len(out) != _DB682_C8_LANGUAGE_COUNT:
        raise AssertionError("v0.13 C8 language decode count mismatch.")
    # Exact row-content guard: each row must contain precisely the C8 edges
    # nonincident with its host edge.  Incidence is target-specific and fixed.
    G = DB(6, 8, -2) if "DB" in globals() else None
    if G is not None:
        selected = set(_DB682_C8_EDGE_ORDER)
        for sys_rows in out:
            for e, row in zip(_DB682_C8_EDGE_ORDER, sys_rows):
                expected = {f for f in G._nonincident[e] if f in selected}
                if set(row) != expected or len(row) != len(expected):
                    raise AssertionError("v0.13 C8 language contains an incomplete row.")
    return tuple(out)

# Loaded lazily after DB/ThrackleGraph definitions exist.
_DB682_C8_LANGUAGE = None
_DB682_C8_ROW_MASK_TABLES = None

def _db682_c8_language():
    global _DB682_C8_LANGUAGE
    if _DB682_C8_LANGUAGE is None:
        _DB682_C8_LANGUAGE = _load_db682_c8_language()
    return _DB682_C8_LANGUAGE

def _db682_c8_row_mask_tables():
    """Return exhaustive exact masks for every partial row subsequence.

    Each complete C8 row has length five, hence exactly 2^5 subsequences.
    Iterating over all 2,544 complete systems and OR-ing the corresponding bit
    into every one of those subsequences constructs the exact support table
    directly from the frozen language.  Missing dictionary keys therefore have
    support zero.  This replaces v0.13's first-use scan of all 2,544 systems; it
    changes no accepted/rejected state.
    """
    global _DB682_C8_ROW_MASK_TABLES
    if _DB682_C8_ROW_MASK_TABLES is not None:
        return _DB682_C8_ROW_MASK_TABLES
    language = _db682_c8_language()
    tables = {int(e): {} for e in _DB682_C8_EDGE_ORDER}
    for i, system in enumerate(language):
        bit = 1 << i
        for e, row in zip(_DB682_C8_EDGE_ORDER, system):
            table = tables[int(e)]
            # Every order-preserving subset of this length-five row.
            for subset_bits in range(1 << len(row)):
                subseq = tuple(row[j] for j in range(len(row)) if subset_bits & (1 << j))
                table[subseq] = int(table.get(subseq, 0)) | bit
    all_mask = (1 << len(language)) - 1
    for e in _DB682_C8_EDGE_ORDER:
        if tables[int(e)].get((), 0) != all_mask:
            raise AssertionError("v0.14 C8 empty-row support table is incomplete.")
    _DB682_C8_ROW_MASK_TABLES = tables
    return _DB682_C8_ROW_MASK_TABLES


# ---------------------------------------------------------------------------
# v0.15 exact DB(6,8,-2) C8+endpoint-edge language
# ---------------------------------------------------------------------------
# H2 is the selected subgraph C8 union {edge 2}.  In the target labeling edge
# 2 is nonincident, within C8, exactly to the six edges below.  Every complete
# planar DB crossing-order system restricts to a complete planar H2 system.
# The frozen H2 language is generated exhaustively over every certified C8
# parent by enumerating every order of these six crossings on edge 2 and every
# insertion position in the six fixed C8 rows, pruning only with the safe
# locked-prefix minor.  Edge 2 is temporarily oriented backwards during the
# generator because this is dramatically faster; the recorded edge-2 row is
# reversed back to the program orientation before it is frozen.
_DB682_H2_EDGE = 2
_DB682_H2_PARTNERS = (1, 11, 10, 9, 8, 7)
_DB682_H2_SELECTED = _DB682_C8_EDGE_ORDER + (_DB682_H2_EDGE,)
_DB682_H2_SELECTED_SET = frozenset(_DB682_H2_SELECTED)
_DB682_H5_EDGE = 5
_DB682_H5_SELECTED_SET = frozenset(_DB682_C8_EDGE_ORDER + (_DB682_H5_EDGE,))

# Filled by the release build after deterministic exhaustive generation.
_DB682_H2_LANGUAGE_COUNT = 60196
_DB682_H2_LANGUAGE_RAW_SHA256 = "51e2f918b5749ef845d620546a66ceead75863d97061dc36ac5582e30d24590f"
_DB682_H2_LANGUAGE_B85 = (
    'c-maub(~!Fz5nq&GqY@VH=7W5_hjSl?#XU88z4kTkXtVlcQ5W*THIY*TrSp>dyy8(?XSh5r4*7Xq{Ui(=X=h`dBWq-KR%t!%z3{)'
    '^8I|j=W}MNs-l`Ub@jFRT)rwFRmE0an_%Ut3aM4!rZ%6?RaFP8t|oacsw(6XD|s!ds!pu>n%Ii}QFT7C+SJrmMZrw1+M25Pl_+1f'
    'qWC=uRaG@n`1D-(^r~QmPtWC&mx2}lX)b(vu-e3C@}5!IisFA4e|S}06s{~>Rrp_Q#s97lzhQM^g)1u*s*)?KYZKMh)K}-L3sEk$'
    '>T9YCv6a47Ut3dMonB{Mo7(t&3i;~l^e=1U_bC)&D}JrME=o1Te;Jk321eCUMQwtxtTy?}_$uq7qK1-{YKX1+Ho?jV62S@|k!nw@'
    'HsQ6vB`PYau1<(n)d#l}^~F|A@-Bto&0r<(QV9M_tne-Ye6RwvqQ?@e?6Ih#FVRq6SChO;@N{A&?-HUQzV6_@nyOqrAEG32Uu+ff'
    'xx}h)$-yNDmmFMjMH2D5#Ncy~$Q4P%pBLrJR>~y@mmFMjkjOzI2Z<aca*)VDA_s{)+Vg17qdkxIJlgYU&l3}QNaWF;M|&Rad14|D'
    'i996okjO(K4~aY^@{lNy{ROhWK=v2N{sP%wAo~kse}U|et@z4{bt$z<bt$&8m7zdoC{P(<t0sMy_%EZxO5P=Sut3!)P&EovjRIAp'
    'K-EaB_+9hiwfH@=HKdw&sU}{kiI-~PrJ5QNTe0Iy+N+74YNDr_=&2@ps^jR1gCgb<d|OQ{#a2!72}zl#CbFuDtZE{wnpmnPmUf|r'
    '>_Q&x0+(IjvI|^xfy*wC*oCax1robZQFejLE^yfeF1x^G7r5*KiCrME3nX@dL=D<&&|ZV~8noA-y$0<yXs;nAY9LXA_8PR;puGm|'
    'HE6FPCTbv21Bn_))Ig$591}Hlwe?j=AP1{9?nJ6Xt%-tFR})@~!z%g9x;QthLQ3URt3D<eTe&u+$VwKAHi2&P?{aZUCsy+BVlesC'
    '3jZ!(YE$w<?1j`ySjR;^SFx(|$+gtfhEkN~RAR;0s^X=-P`08Z!`f7Z5>i)R2$d)PccDzw)#pQXNvxXmU6Own#3uhPwrU}fT5%mr'
    '(zX^ZwQxzT@R#wMq*i^*I$T)37B01LNv-hj;>%2}<lhBKwQ#8|#b;btbNN~*)k3KjO0`g`g;Fh)YN1pMrCKP}vF6mV=G3v~)UlG('
    'v62KUe#>M9O03MfQpdUytTxGChBdp6Ri=(rrjAvnj#Z|PRVG;JdsfAcsbkHlW6h~!&8cI}sbkHlW6h~!&8erp)Kg#TsW0`RzC?9J'
    'F7;HKdRCzNP<!GG%qKOZo=Oy~HsM|Jp|h!{64g^}>O-}O-=&Z=UG>zSdTLL7s6FBHl8RDKB??yZdGTxc)GF7ddTLKSwWlprxGj|0'
    'La8m3+QOwRB-%ovEhO4fq1(cxEnM2dr7c|A!lf--+QOwRT-w5=EnM2drGdR+1AD^;_J$4Y4I9`SHjt?eWNHJM+EDBc<H8<uX()Dw'
    'Q51?+1HEDcy<!6y-au|PkedzUW&;`5K*lwYaSdc#0~yy)mAJ1azRvi+1~M*KZIahQWVK`G-443#pxX|*?V#HZy6vFb4!Z52+YY+z'
    '=)~JWw;gobLAM=r+d;P-blX9<9dz44w;gobLAM<|+rhIv%-Tb#J(Su*sXdh1L#aKK+7pBAi(KN$7q39=q0}Bq?W>Z)P!s=Uz7T&x'
    'mQs5twTDuBD7A-DdnmPsQhQ>sJ<Qs}Y*%{kU8#J#Qu%hJ^6g6H+m*_<EA?#GVvm_p+LexTS9<SVs}f{IO1o0|cBQ)QN>{lnyVhN)'
    'V7pSmc4gPvfhg!e6m%d8IuHdNh=LB}N(Z8#15wa{exd{YL<jPy0};}J2<bov(SZ)41JTog=;=W8bRc><5Ir5}89ES49f+k4#8O9i'
    'c7$g~cy@$mM`}+;cy@$mM|gIGXGeH;gl9*1c7$g~cy@$mM|gIGXGeH;gl9*1c7$g~2zG>ECkS?eU?&K6f?y{ivJ-Ww69hX!uoKKW'
    'QKdS;tP{*SL8%jzIzg!ulsZAF6O=kZsS{Dx31*#O)|m>{nF`jK3f7ql)|m>{nF`jKZml!*tTXkjGxe-9^{g}XtTXkjGre19s#|Be'
    'wa(PK&Q!O~RJSffPZy%63(?bs=;=cAbRj~z6mu*W<<i$O8P|pA=|aYJA$qzHJzdDSF2qt7VyO$U)P-2;LM(M5mbws2U8<61yCxSL'
    'k?%rebs@645LsQ}*%h8$;n@|QUE$f4Z0ri%uF&mT<QZ4K^e;1XyH+I|u$uU_IF`DSsa;{+71mv$+ZDQ9q1zR@U7_0*x?Q2$6}nxa'
    '+ZDQ9q1%nT?MB{qBX7Hrx82CwZscvZV&0|%yOG7+$l`8faX0d|8+jXB;YgrJz8hKGjV$g)7I!0yyOFou$lLCv6Rbk~0lDs_6Rhyz'
    '`R-8aUOKZX#5=%T_tKeFKDN@=$^^SZusa01L$G@>&Jqn(C9AqR5bR!+xVAq2!}udoD^?X>Ss~vYO5Ljxx7Wv2D*em45Lt0mEEHcW'
    '6AV^}taxWyo&IHrthi^dF1{8=Rw29=buY$sKJd(SFOp9pIsVHut`pYrUuNlchi(t(_JD2===Oka59s!QZV%}8fNl@y_6X-hwLwv!'
    'Te4ERJ)qkIx;>!V1G+t++XK2ipxXnwJ)qkooHiv_7F5JmtS4MqswmCy*h&;->GptbPfjO$avs@}^T?i@)Ar<?wkPM2Jvoo;$vJIL'
    '&S`sc9@&!<$ex@)_AH)2h6-J%>dARzPtGHIast_t6Ud&NK=!OkQl%z}N#~<pkm$uZZ7;a=f=e&XX?t-_+Y2te;L?k8+FqQ~_JT_<'
    '&S`r=sTY)bL8%v%dO@idlzKs_7nFKIsW)qCZ`Rb_tf{?ODSH=BX2Y7ASeZVgH!EfD;>m0juc^7Rm7de~F6L1zHqP+g#XPD`xb!aO'
    'Q5^F5)JoUCTy^@F>G~I2>1)aQ7hAESY~RzHwYWEHabkrm3xfdFy-Qq@+bzB6iF&hY_vT!<cX<tuSC(9FR`lNG6+M0}-<$QlcX@r!'
    '=d)II(Mr|ktJ8O>to^;qYk&M&zBipf?{X&)zZUhTFX&yB9Dm08Ql80Dob(0Z-(~xPKEy;HVxkW*(TAAmLrnDH?7j~X(uWA?LrnC+'
    'e|_*@AN<z`|MkIteeho&{MQHn^}&CA@LwPN*9ZUg!GC@5UmyI}2mkfKe|_*@AN<z`|MkIReehUc*1x{2e|=g1`WEjTq(17)eT2UB'
    'Zhbi~?@RC2m-F(z^k97}en>tqdqUoq{;V(kSz?vF*|(xL(U3ho?@K4wm(%mUtc`tH8~f2S^n+PHnDv8MKbZA{Qa>p5gHpdDrO?yn'
    '%2vv(AKh=isw6p*?jl@SmS;bB_Je0Xc=m&5KX~?oXFquMgJ(Z@_Je0Xc=o4G^ruerr%v>zPV}cv^k>i2pE}W>I?<n%q(5s%f7Xuv'
    'tR4MXJNmPB^k?npPwnYX?debL=}+zHPwnYX?debL=})!kPqpb!wdqf_=})!kPqpb!wdqf_=})!kPqpb!wdqf_>CbA>pW4%(9cF(j'
    '(Ews%05LIum>57z3?L>35EBE~hYuho1`rbih=~Ej!~kMq05LIum>57z3}B}}fS4FSObj3<1`rbih=Kt`!2qIQ08uc2C>TH#3?K>y'
    '5CsE>f&oOq0HR<3Q80ig7(f&ZAPNQ$1p|nJfmGUoRN8@5+JRKsfmGUoRN8^XN}Eg01O{@lFp#=Ckh(jNN;{C<*+A;<K<e&5>h8cI'
    '>s+!k9Z20BNZlPs-5p5X9Z01eNNpWRZ5;%`K@c1S!9frl1i?WN90b8ZtXzX2I0%A+AUFtSgJ3oYW`kfhh?Q#)1P4KI5CjK7a1blk'
    'Ab1Xf=OB0vF73`@uScmBc4xW3Y;c8jEO2n8g2nm<S6IhMHn_q%t}la&H7lsgR}D@oQEh#pI&32c7wb}BR47~F{fn<9d;7q8aIxCN'
    'btz8q!GUgko#D7HTxVci6a0`|XPJC*o#kqiTxXela%IW*XMGq|td0g3``wssu4pBn9-?V*@KOAE!9{^mxXhXmA^EEO;EMm^e;KTr'
    'qS~tJ!Q~T)e8Q!CK9N}Es*xy4t>nxjv5MX-{$;R2?MbYX$6{*;9vgzkhTyRwcx(tB8-mA%BpwS~Le&_8|4LT)yW(r<$xu~dWqdmX'
    'Zw|qmL-5}a{5J&u4Z(jy@ZS*pHw6C;!GA;W-w^ya1pf`ee?#!!5d1d;9}U4rL-5hi(g{cmEh-GfV?*)SP&_sij}66RL-E+qqQ}Bn'
    'VZLf89vfQpN<Q(}P<%9${2PjohLUkZ6OYw~Q@=z*)_+6s-%$KF6#osye?#%#P&_s?@mOtrDC|{*q4;ko{u_$_h9>??NmNx2#hXL%'
    '=1{yjlx!SIHV(zpL-F)bJUt9g55v>L@boY|Jq%9|!_&j?^e{X<j7%Md--nT#!|?ksJUtBG4#T&@@a-^sI}G0r!?(lm?J#^h4BrmJ'
    'x5M!5Fnl`<-wwmK!|?4ed^-&P4a0xK@ZWI!H@tGP9%~<7Ia!aF`{DR+I3630$A;sv;bh}*yfPfG3@87F<D<k%&)}0Q3s!OlpIlki'
    'N5k>TaJ(`cuMEd4!;9T^Y{h;UUhJ<EALWMQmEm}0IDQz8ABK}-!|}>+{4fGPjKB{g@WTlFFake}zz-wv!w52G1i3N-uZ+MeBk;or'
    '{4fGPjKB{g@WTlFFake}zz-wv!wCE^0zZtv4<qoy2>dVt@*^NW67nOdU?ZtuBOyPM3N{iyjKmKk@xw@J*2tnC5=RFslPe=xt45aZ'
    'PzC>u#785^oRN5JB-L#s)ommm8%cE=iT_68v5|OeB=u}0^=u>_8;Qq8QqM*f?`#DUsa5gjNW3|ctQyJ6H4;ycr1Fi#@1yYhDEvMO'
    'zmLN2qwxDE{5}f5kHYVx@cStIK8kD{g>OgU%~5!B6y6+#H%H;kQFwC{-W-KDN8!y;cykoq9ECSW;muKaa}?ejg*Qjxu~B$z6dr5D'
    'V~y0vMrvdu9&5x$jrgb$A2s5YMzXPy{A<KVjpSb=9&4mxHc~Mg@mM21YQ#s4_^6Q@*+`9S#7B+zs1dI;;+00c(nyXq;-f~qG8(Up'
    '#w(-o%4obY8n2ATE2HtsXuL9-Tp5iYMniry<VQn(G~`D^el+AqLw+>mM?-!z<VQn(G~`D^el+Aq!+JEV$1wRYhRKI9oD7ZOWM~X0'
    'Lt{7@8pB-480JdGFwZcCd4@5Zn2lkcVGQ#OW0+?c!?ehlijNXSWgjJqvL{Mom@65>iP9LROvY4v6r&hZ@louvF`PY(DV~PLuT-ah'
    'nO=2lrLQGdolnST&z{C`_B4j`r7@f@jm2YQ@z_{AHWrVK#baaf*w}IggnSsw<jPnkSH|MMvG{K+{u_(`#^S%R_-`y88;i%r;<2&#'
    'Xe@IqWAV{gd^8pxjV({S<P$F0`IoWyZ!G>Bi~q(}GA`knotqhpZ^z=>vG{f@z8y!c8%M1hN39!2ts6(J8%K2;$0{?9>Nbv5W*pUR'
    '9Mx?c)omQrZ5-8Y9QAA*^=usVY#bGAT!nlt{dYz3x%4lK<P%ESS~rebH;z?i9F=bzm2W(GG@d*fPacgYkH(Wn<H@7(W%6Mq8BbP?'
    'C#%L2^W%y6@x=UiVtza^Kc1K$Pt1=e=EoEB<B9q4#Qb<-empTho|qp`%#SDL#}o78iTUxw`~+ft0x>^<n4dt*Pax(e5c3mQ(I*h|'
    '6NvH&MEL}wd;(EEfheCqlusbaClKWmi1G<U`2?bT0#QDJD4#%-Pav)*5Z4o#Y@ArycSK<$KC#3z3dMXPQ9h9<pGcHX<i5;ACf_GA'
    'K|7Hr$tQBpW+L}qCNkYVk>|rF@?6hEp52+qH%?4K-z4-+Lf<6xO+w!!^iAS9%t@%7guY4Wn}oheJY6{nwUbag3AK|@I|;Ru@$F=^'
    'Pe%J>v`<F+WVBD_e%xe8Oh)@;JUtl_lOZvgdv25AGMPJRli@NME>qAq1$|S{HwArD&^HBrQ_wdBPftPZ6!c9&-xTysLEjYgO(6=V'
    'pmqvsr!qx4mATQW%#BWEo^~qpv{RWIoyy$kROV@?GEX~|xzVx}!_9?H&rFI=Wj1swv!PRYqJJurqEnd^oyw%>RG#Rc28n6R(@ulS'
    'G`LJ-o^~4ZwA0`+4KCA|r=7+;?KHSdgUd9yOoPibxJ-k~G`LKI%QU!5gUfXCVLJIRoqU*1K1?ScrgJxbI@vLu$+79=%5-vNI{7f2'
    'JMPoTj_G8_bndE8Cs(F34>q05nL*{70f`xqm;s3ykeC698R(nAb0IUR1v998Gnmky0f`x?ok70Opw7>r&d)^OO!Un}-%Rw)MBhyG'
    '&BV7eQ9Bd0Gf_JewKGvW6SXt(^h~tR#J4jcF$=Y`P&*5?vrsz=wX;w=i#eTHXrG1lS!kby+F7Wb#g29s+GnAC7TRZ_eKyab%;q_i'
    '*^rpco@6$AlG#w24W-#onhmAdP@2uz%xunPX7g0aY@SM)4VT%R0?g(VU^dKVa|$q<Q-Il=0?g(VXEtXuvpJ2K1J60|oCD7}@SFqB'
    'Iq;kV&pGg%1J60|oWrhe4re8E;5i4LbKp4#o^#+i2cC1_IR~C|;5mn#;v9B-bJ)4fWxbut3Okn-b}pUATsn`rtgv%gVdv6$%%$^~'
    '%L+S}6?QHw>|CBvnag@Rm-TioE9_iW*tx8*b4xqE5FpW9o>-X&mwEId^Pn^jO7rML=Fx}DgVH=G&7%*QM;|f|O7oyJ4@&c(G!IJi'
    'pfnFk^Pn^jO7oyJ4@&dNqxs~~eDY{Mc{HCqnon0UpXxoI8NvDVDD$c8^Eo-0PraT`k20U?J)i15pB`mCwR}E3$^x`6K>Gr;FF^YO'
    'v@c*<aslhu0!S=?!~(Q0piV4+!~#ex;ACh4Bo;to0ooU$b|GpPqIMx_7ov6{Y8T@7g{WPK+J&fHh`xpBTZq1e_<bR27ov6{eqV_8'
    'McmC@#NFIQ6%sLuMVwhJ;>>ChcWf6iBe95k^NX1LTf_<0B2H}=asPG^_iq<*p0$XHiABu%E#h=*5qE4CamRKMr(27-N4tnKt3{ky'
    'E#j{FBJRpAhVEkME{5)6=q`rtV&+j6!+J3@my0<cT#O$ULw+&j7sGlntQW(2F{~HEdNHgQ!+J5S7sGlntQW(2F{~FucM11Xm%w@n'
    'te3!g39OgEdI|Sam%w@nce$59cL`Cx1iDLz>m}TIT>|+fkY57%C6HeN>m}TIT>|+fkY57%CER&kf*+RPhb8!72{FF}uPntYOYzE5'
    'ys{LpEX6BJ@yb%XvXp#SijS6(0ZZ}GQoOPhKP<%$OYy@}{IC>1EX5B?@xxO5uoOQm#ScsI!&3aP6hAD*4@)7x4D!pk|FDev56d9G'
    '4D!n$zYOxr$be<gT?XA{#QZW?FXK+dGVW9?gY`04FN5_mSTEzg#WL<&EQ9qjSTBR_GUzUc=W=*1hv#y5E{ErGcrJ(Maw2&-vAZ0)'
    '%b~j*p3C969G=VJxg4I$;kg{1%i*~kp3C969G=VJxg4G=;JJdzu!7340-h`2xdNUm;JJcYu!4JMD~R0{)aw=8OI`u%6-4q1$giMk'
    'te|SFfcy$ruYmOm>ck4_#0prifb|OM#0u`mt-uc}zUGH)^<F^@S&5HU;-i)LXeB;ciH}y|qm}q*B|ch-k5-ZaEAhih$ghO_O31H-'
    '{7T5Lg#1d#uY~+c$ghO_O31H-{7T5Lg#1cauY&a|>dPwX%PLr}g7qp`uY&a|=&m9IRuS{7V7-c%Uj_M9RGU>)n^lls1^HEwUqyXc'
    'MSWQX`Bji#1?yF?UIpvb&|MAP)zDoH-PO=t4c*nyT@BsU#O`W%u7==h2(E_UY6z}|;A#l2hTv)lu7==h2(E_UY6z}|U=yc|O`I||'
    'v1e{#&)meGxrse<6MN<+PHmewwQb_;u!*z7Ce8$!I6G|O?68Tm!zRvRo0wH;VpgSzeRvb6woRPcHZiNx#H>maJN72#QJR=XX<{Cw'
    '8S>4LZ-#s`<eMSi4EbirH#5W2%xP~kr@hVip&36k<A-Ma(2O6N@k2A@n<3u}`DRXgn_=Ay>t<LtGZ)m%DRDD?XvPoCU-LtDE~uH)'
    '<uz24HB^)}RFpMTlr>b8HPnzb)Z{hPkTulgHPnzb)Q~mQkTukhHB^l?RE;%MjWyJXHO%*{VZLV#^F3>*C~K%FEyQ&Taos{(w-DDY'
    '#B~dC-9lWqFsar;l(!J&EyQ38G1x*3wh)6Y#9#|C*g_1p5Q8nmU<)zWLJYPLgDu2h3o*Es7+gyXt|bQ75`$}r!L`KTTGp|(#Nb+@'
    'ZY@!_mZ)1x)U74z))IAViMq8!-CCk<Em60Ys9Q_attIMOOLr>5cUe}qmhMzUp$%%~zFI3W*h&nx5_PRaT`TvQTe<Vv%Dhc0C%Ubi'
    ')3$Oixs@rJR_?L4a*w^0S*mrV?_dwNWulT*UAB^MWDmD<%2sv73TtDyqf)l2OIGn7QSi#T@_nH26*KEfcgw=<mE<qeyF%fssMeM5'
    '3WcvnDqDr{)e7rM-;o@ytZH59JCeh-q*nO8lH~5ry3+TY<ia;Hl&o;8E*D!Fp7DETcm}J&EV0VWs&*qLb|WTsBPMnuCUzqxb|WTs'
    'BPMp^%zrl`WH%yYHzH&=B4jtt^>-s)cH<;}H=<`ZqGxyR`0dU;zTLUUw>x)2cjr#%?%d-mTjADOc$dtbyWP2Sw>$UhcIRH*?o1Hv'
    '&Yip6xpTKWckXs)f@lx)?ZF+*Jy5#`YWLud<{sS9+yk|Hpmq<`?t$7pP`d|e_dx9)sNDm#d!Tj?)UGE}*ORI1$<*~^>UuJDJ(;?m'
    'OkGc=t}lHTaB{zDed)V^!|mJD3f~1BrB{~C+x6t_`qG?0{OP%9eQ8c0ev@Ejvv@sOyq+vxPZsY<7Vk+G?@1Q#Nfz%(7Vk+G?@1Q#'
    '$xO|jWbvM4@t#aR>`4~yN#5>BrtV2)-;>I|fm*(STE2l=zJXf4fe6_^glr%}HV`2jh>#6L$Oa;00}--;2-!eo-#}&GK!j`{LN*W~'
    '8;Fn%M92mrWCIbhfe6_MrHxS92&Iis+6bkMP}&HkjZoSMrHxS92&IkW(MBk3gwjSRZG_TBC~bt&MksBB(nct4B9AtaN1Mo_P2|xg'
    '@@Nxzw23_0#A>*StlC6YZ6d2SkyV?>s!gnoo5-<Etc{z<xXq~DjM~kp-Hh7JsNIa(&8XeXtixusZ$|rO)NV%YW_H(`(Y_h&o6)`*'
    '?Ryc|dlA=r5!ZVW*LxAydlA=r5!ZVa<2o7PsoJX;$;o(6YK0t2)`yZ+NaA`gB6%+&d9TtrL!1spE08Eu6<<sC0bxmxt>W2C67v-+'
    '{)}h~6>|&OzXdK^;IaiSTi~(<E?eNT1uk3QQnCt3RoqgfR7moD3tYCqWeZ%kz-0?uw!mczT(+WpE84fBeJk3xqJ1mcx1xP3+P9*8'
    'D>1PZ?OV~l742Kmz7_3T(Y_V!Tfe3~8xwmoWw|#~mU~kf_NFrIO=Z}d%CI+;VQ(tK-c*LYIq}?^6VJVwtK6Hp%Dt%!dvhkYH)nEt'
    'Q#JPHOm1(^<o4!FZg0*;_vXZNZ%#b-f#5z6+y{dDKyV)j?gPPnAh-_%_krL(oZ{@mS>-+u+y{dDKyV)j?gPPnAh-_%_krL(5Zs4z'
    'qJ22;*@ttRec7+<%MN8<b}0L@AKRDx*uLyg_GO2%FFTZd*`e&qB;~&BSN3JUvM)Q7ec7Sx%MN8<CMox2l5#)P?#J$IKeX?M_WjtM'
    '?Z@tHKeX?M_WjVlAKLdr`+jKO5AFM*eLuAChxYx@z8~8EE381Z^>t|n|6f(fZJ@fe(*9SXJ+WdIi50ggRpE3ipIUXr+8V6*1L~@h'
    '^Rv{dOTO>E^jcl9LjPB&yYW9vd+-0MN^bYprJZBRN>5I{!Igc3D@&~SO_OU$tQdUw^!Pfz!L@vYYxxG(@(r%#8(hmbzIH9i7+Lap'
    'QPnrOvc!sCOV*BHWv=X-T-i6dvTt%_-{i`^$(1Em{9-OyoxaJHee-KqmReCVtNAUi^IH)77QX!!zWo-y{T5gKEw1`oT=ln#SDo%3'
    'zJ-QwLHAo#$z>K-(Qk8|-{v~M4bN}G^V?k6x4E)!b7kM=%D&B&eY;3Ee7R2YTIM>x4c%{Z)!*T&ze5y!hpYY$SN$EX`a4|pcev{B'
    'aGl@bI=@3qe244&4%hizuJgOl{Vq}PU83N-L_yg~x~K1Qo!{j;zYD?d60P6kTE54%e2;7S9@p|cuH}1N%lEjJ@8Rk1ab@4*%Dz{X'
    '7{%W0docTc(v8;ESBJ*~idLyN{XV^EY}JMll(g!nR((x!43;ZfVd;qfGTHRh7s7j1eV-ol`}COKFW$w^B^th8`jv&Skfc_;YA4Sl'
    'l&$dP&B<%Y4UZ6mg`$<7%@nQVETNEoLUM~Ejh^q9ew`tq^!;MT5{0kSuG$|G`$J-XNW@lcSODX7EatgCT=s{{{&3kJF8jk}f4J<A'
    '_We=2KWg_!?f$6UAGP}z)m9}pZT3g|0m<$xXb*vQ0DH9q;Bo+54uH!6kT?Jm2SDP0WKR-EgzG$j{n!CeIsi%sK<R+wG$!SeD_SX+'
    ')T%_*0YugT&^>_2`T_cWfW9A~?+57n0s4NxRsVpi{z37|qR<i*t#I}fw@YO!z0MzSoj<_uKfv!lz|%jds!baDxPgz~^gt9Hh@u0D'
    '<O9)nAo>nO-+|~m5Pb)t??Ch&h@t~gbRdcjEJkv=1{_%WX8gpP2cq^s;`+c?dr%ZrhmSuH5(g2<2f^haxEutDgCKDbBn~244}!}<'
    'a5)Gr2N9nK;rD}}bP(Bp5X=sO*+FFgK~Opf5(h)#U`QMciGzudgW+;8Tn>iI!EiYkE(gQqV7MHN_Jh%WFxn4B`@zJ^!H_r@5(g76'
    '2NN#`L+KFe;2}^t1WJd%<q)_W0+&Omb%(&^5V#ydJv#(Shmci=5Iu)L@DLOoN}WFxeTNbghobgS)E<i3Ls5GuY7eE(ABy%viI77f'
    'aVR7XrOqD;mqX!lC|PwVTn>fHp>R12eTNbAhoSZ`)E<V~!-~HHo~zC$?~>JU7}t3i{yU5-JFFP<$-qm|sxLmvc3A1xLy~>*VPwEz'
    'WWZrm%)^NJ!-)CAzD6S1hS%hhJ^JB9!QoIk97=~n>2N3=4yD7PbU1!L9A<~Z>~NSJ4zt5yb~wxqr)nGyv%_I_ILr=*+2Jrd9A<~Z'
    '><IGc2nZel!6P7e1O$(O;1Li!0)j`7M@PW(2zVX=&m$ms1O$(u?j8ZbBOrJL1do8(5imOfW=Fv6NVpscmm}eFBwUV!%aL$7vdASF'
    'Bda=+bMGU$7jh(&j)c;YMBR}vI}&C`5_LzCsYgQTNaE~Bm>mhTBVl&r*O(<oWHtHZbn8e?){i3Uj)Lw{&^-#eM?v=}=pF^#qo8{f'
    'bdMqikAm(|&^-#eM?v=}=pF^#qu_ZIJdc9sQSdwpo=3s+D0m(P&!frdqoI2=bdQGa(a=2_x<^CzXy_gd-J{9yqoI2=bdQGa(eOMP'
    'o<~FQXqX)hv!h{lG|Y~M+0igNhVJ4Rm>mPNW1w^ll#YSYF?0~eK;jrk98>HWa>+T-F~y!Cmz;+jLkDpT%#I-<kAdJZkch41QI|j>'
    'ijJkTIu`B65<SO4;#f!=3yEVPaV#W`rL#H~F2@ot$3p2?C>;x>W9hSwh0?K5Iu<U+!sS@F9EZN+(03gAjziyZMSb}sK9A!b=5b`l'
    'anzpUsO-m~_BhlYM@$@tzT=33<4}7XYL6oWj{BPS+T<~&e3D1UksZeqA;%LF$HVM+m>mzZ<6(9@%#MfI@kGe+#KiGXIvz^LL+N-Z'
    '9S^1Bp>#Zyj)%+fa5(|(C!qZVw4Z?X6VQGF+D}0H3B=0@#LEegH~|tTK;i^QoB)XvAaMdDPJqM-#LEeAIpJ$uvhi{v_2opO=S1qu'
    'iSRrTo+rZdM0lPE&lBN!BGu+ZV(CPx&57_l5uPW)^F#=q2(uGmb|REcgwjc9KMCz8q5UMZpM>_4(0&ryPa=9wLhVVYJqfiZq4p%y'
    'o`l+yP<s*)auV84`kMA^gq+O1-IKYSdop)(Pv%bc$=u04nePianQv7(nQv7pTLDvaGIx4U=1%X)+}k~wd%GtyhkG)2dQav~@5$Wh'
    'J()S&AI6>zZC4rvKP-_*#tDB|(w+<+{;;GyiGm-Nv?o#U!;<!Vc$*)Vv?qn)hb6Tk1#)F8>GFOU`#pSm8WXXVv`^s&H&ZLo9)657'
    'wdzWJR>?}w;7?(e;}m8&PT^^tQ_6m*j#Zq(vpc6S%W(>`9H%hLaSF2>r!Wn33ezyBFw1cYvmB=|y>SZD8>cX@aSHPqr!cQ^3KK7<'
    'F!6E<6ECMi=~O743Z+w_bSjiih0>`|Iu%N%Lg`c{UQT7=<y0u03Z+w_bSjiih0>`|Iu%N%GSzY_Q!S@5)p8oO;52H%Y1D$#s0F7{'
    '3r?dJoJK7;jaqOTwcs>r!D-Zj)0p}=jmmHumEkmM!D-Zj)2Icfm7jhpB%hw00XdBskkhFXr&A|Rr%s$soj9F3aXNM4bn3+E)QQun'
    '6Q@%rPNz<sUgDBGV0AiG<8-RV=_R$*LG2kRIs-*#py&(~oq?h=P;>^0&Op%_C^`d0XA~8MS*?88O7)$AzB5pC#@7@TpGm6@kG7r3'
    'v*Ty-l--$?43A$tlV|SE<e9rOdCKlgo*h4vXYtSEyFSk3nY%N2?(<BZBtMhq@y_IVyfgW(k2855?@XQ~Ka;2P&gAL5GkJFWOrEkk'
    'lc(&?g4tOxI}2uK!R#!UodvVAV0ISYmU0%)DV_zvvmkgD%+7+@Sui^bW@o|dESQ}Iv$J4!7R=6q*;z0<8)j$2>};5w4YRXhb~en;'
    'hS}LX+j%xocQ#KOpAECKiMq2Pcs2yjhTz#SI~!(a!|ZIBoei_Ic?$Gw2%ZhWb0ByQ1kZusIS@Ptg6BZ+90;BR!E=bZb6|E3l+J<D'
    'IZ!$WO6Nf794MUwrE{Qk4wTM;(m7B%mwJ6J_4-`u^|{pRbE((oQm@aYUY|?7K9_oZZn0jcdzo{o-se)i&!t|UOT9jqdVMbS`rOi!'
    '!O41i9#L=}QE(nna2`=`9#L=}em{>~IS;>|N3NWQ-_OJE=i&GB@br0j`aFDl9?wCa$8*r<@f`GdM8SDP!TEHm=hLa4Pp5i5o$C2?'
    's^`<Go=>NGKK=ap^z-M_jh;_8dOqFg`E;Y_(~X`_&wf77@So2!{O8lppHDx3KF{!<&olhz^JM<{Jehw!Pv&0$&kNvr0X#2&=LPV*'
    '0G=1X^8&uV-~#pm7qAbw0J;}I_X6l%0No3qdjUKzfaeA511^Bz1rWS|?>)GH9m56Cy#Trwe2s4Qdk-#Pr*R<}ejyotAsK!l8Ga!d'
    'ejyotA(j0?GW<ev`a*L0LUQ^-a{5AY`a*L0LUQ^-a{5AY`a*L0LUQ^dV(=nj@FHUHB4Y3&V(=nj@FHUHBEC`MA|mo4BJv`l=OUu#'
    'BBJLaqUR!_=OUu#BBJLaqUR!_=OUu#BBJLaqUU0ss=b&~&5L<n^kPo-F6MdBi#g}Jm}jUi<{7Gs%d2RZLB5zLsxIb<s*8D|>SCUw'
    'y_hFNFXjo+i+MuyV!k2aVx9@T1nrlg{Svfag7!<$ehJzyDfbhhE4c&`mz2AUSW)2;xLi{1HDWILOQ3WKlrDk9C6KrT5|<RuKhsI='
    'OW<+|TrPpjrNxu(biVvj&b=>%*`+YMw0IJnv_xgAI%Ac1UJB1k;dv=MFNNo&5WEy-m%{8)m|a>tPfn-NE`{Kw#q;D`(t}+J&r9KX'
    'DLhM7`uxMC@VpeBKceGItoS2Ro<E}h{1N@<kLW*tME_Z~lJoK((MKj${0Zs3f*)}TkXZ3+`Q*eiSmCTDm&=!|Hl;K1l9f*7UdDOW'
    'Wt?YS#(CCdoM&Cec~;p9pOF5$@{>xJae{RjCs>zpf^`{ZR+n*Rbs4AGmvMr187Ekmae{Rjr`bQoV?V}6KgLHt#z#NKM?c0#KgLHt'
    '#w$POwCTs3O8*$I{1~tNgzNkX*ZC8!^Cw*APq@yXaGgJ4zw#5V`X^lVPq^xzutWI?8h(O?%gOi4$@j~tn3q!{FDJt<C&Mpi?YNw^'
    '<8r=h;Bvle;BvmR<8t!-aw_KKJdJxf8GZ$du0YWhRIn@1cLnwA3e;Xfb-M!XSD^ihVs%R=Nv=Tc6~*cnCHu`Q(0&EluR!}1)VeDm'
    'aRnr<fW(!o4_C52T*(@6C2PQy5WEtCSHkQ{C|wDcE8%h_F>xg^aV3<lWJS1=HQ-9PTnULQA#o)nu0riqsJ#lcSE2SQ)Lw<!t5ACt'
    'YOg}=Rj9oRwO0`ZSE2SQ)Lw<!t5ACtYOlucSL64qA#pV%u7<?bkhq%6xf(84lQ~yI>1s0PYM5OOv#ZIRtD$r?F>y7Nu7=Xp<jU1B'
    'yBcO!!|WQkTmzSD;BpOIu7S%naJdF9*TCf(xLgC5Yv6JXT&{u3HB^*qh^1?wbPbfQfzmZlx&}(uK<Qe#(QD~OuO;fPCF-uF8@-lp'
    '^jgSY3;Amye=X#%h5WU!z81RILibweUJKo8=}oUC>aL|Xy%xIHLibweUJK7_;dvcgu7k^UaJddH*TLmFxLgO9>)>)7T&{!5b#S>3'
    'F4qxf*FoYsNL&Yr>mYF*B(8(R^>k0y)0baQFLgb=)b;dI*V9W~PcL;n-P85-<=4|oT~A+reX%c(^5Fs1>*><3r<c0EtS^2sx&cKu'
    'py&n^-GHJSP;>)|Za~ouD7pbfH=yW-qM}^V58i;j8_;(Hif;ItqSE)A1b5zuz8g_=BZ_WB(Tym&5k)tm=tj=qZ$#0JD7q01H=^N2'
    'G~D<#4cXKBo5-V^sO2|Ny>B9OZX$DTV(q_)wf`n2@or-F?j~k6Z(@4tCNk$HzHjCxzG3DjzG3DjW}<FJ-_6vCn^Ai+RpVx~-%Jg;'
    '84@=`;$|ktZbtjf%#qy;iJKvDGbC<?#LbYn84@=$Id(I%VmCwSW+>gl%5@8M_ZA4=0<&A7bPHT=fy*sK$Sp+3El|3J*}_|xue${<'
    'x4`8VxZDDlThM+h`ff$vt?0WIeYc|TR`lJ9zFX0EEBbE5@3*4wR`lJ9zFX0EEBbEzn!c=WZ^O5@q5U?r-$r)a28r9qj@#gJ8`*Ii'
    'lx~C4ZDhx7aJdb?-v*c4;Bp&WZiCBhaJh{PxD86TL*jNw+zyG`A#pn-ZimF}khmQZw?pD~NZbyI+o=<`6EC;J<#xE-4wu{EaywjZ'
    'r%v1srQ5$oDH}_7(EZ*)WZgk0cL#LufbJd8y#t<iK=2L--T}coAb1D!$#)P-cQCPg2L$hc;2jXW1A=!z@D7;W0kb<HaVI41gv6bY'
    'xDyh0LgG$H+zE+0A#o?sb0^yGMEjj+zZ30uqWw;^-%0e`35h$uMj{(MchNoFMR#}?z0_UwQg_iy-9;~T7roS7^ip>fyTg>rUG$1~'
    '(M#P$FLf8a)LryachO7TRpt`3-;KVzQFJ$o?ncqwD7qU(cQdbXH~Q{I-`#YMccbra^xciVyU}+y`tJUkzHH}sH*+5MFqL~x`P4l&'
    '3imLhdk^1AcMso6cMtbW@8K@#J=`U|hr6WraF_HRCLiu$^5Gt4bnjtC_a5%s-@|?Td$@0Z5BKfw;lBMnOhw$o<ikBoKHLkldtr7j'
    '%<hHRy)e5MX7|GEUYOkrvwLB7FL#gcWuD<)nB5Drdtr7j%<hHRy)e5MX7_SO`d;oc-^=~t`?wEuANPUo<37-R+y}ak`#|?`ALu^r'
    '1Kr1cp!>KFbRYMD?qibqKJE(L$6cZOxDRw6_kr%?KG1zkGT+A}^L<P*|CDO;Q>x8RsWv~Q+WeGi^HZwLPr3K<Q>x8R*^B;^>9C)2'
    'C+4TziTNqj=BG@K{R|C1L&ML|@G~_03=Ka+!_Uz0Gc^2+8u>F6{R~AvL&ML|@UyRJ$X3PsQFK3w?nlx6D7qg-_oL{36y48?a6kI)'
    'N8kM@x*tXNqv(DV-TyU3**gCKz0CvkHV@F-JdivGU7AUJp!8I9GL!fK&qzPOb6F4YT-F2hFAvbaJV5{Q0N+^f0N+^f0N+^f0N)Ms'
    '0N)Ms0M9``z;|Rlh}s8H`ygr`MD2s9eGs(|qV_@bJ&3*sQS=~+9^_f>2YDL)LG(R{z6W{E`yqV$5NaPn?L(-22(=HP_94_hgxZJj'
    '?L%mP2<;Ey+lL_W5F{Rg#6x)cAxJy~iH9KZFlrx0?Zc>j7_|?h_F>dM%=7&Zqwis!%zv0~I(V4xk$4!j52N;B{QfZd9{!rX>@)n2'
    ';OR%u{s`J1LHi?Ue+2E1p#2fFKZ2(pfy5(_cmxuU;P*!$@dzXyfy5(_cmxuUK;ls{;8D0d3YSOW@+e#$h0CLGc@!>>!sSu&;ZZ0('
    '3Z+M(^eEZ!D3l(B(xXs%6fTd#<x#jihW5wM{utUHL;GWBe+=!9q5Uy-t&ef$@fc^Lk3r%wNIXWoJVxd`hW5vZkjEhL7$hG18j0-Q'
    '_c8Xjj}tGC!|ZXGJr1+SVfHx89*5cEFnb(kkHhS7qUUj#Jr1+SVfHwb9*5H7P<k9nk3;EkC_N6PC&;lUVD<#eo`BgCFna=KPr&R6'
    'm^}frCt&sj8TSOto`BgCFna<@Pr&5~xI6)uC*bk~T>d*;bxk-A34fYe^=)D<v0D-={?qtMVui64n!`3}R~f8$i_oSjq<h7xj*`DD'
    '^?YHw^xx%~sIUV5cjc~L?Az3;ZxeDQO09ItD~^f(u4<FK7{5!5{=bWpYO$5POKteIi$E|Jt~yxtZ3<z(nOgC6hFwp%mfD))rzh`H'
    'TT{BHm@8Vzr^h?6#4661<%1P|D<!#emwZC9z0QY2s?<tIL{&k1*~(R{d^o@gpB{c=C3FJu=ciWqy!f@$YE$g;a!=xiC-K9R_~A+X'
    '@FaeC5<fhNAD)E#laPP1(wE0?^CW(F64p<``bk(n3Ed~5`y_Oqgzl5jeG<A)Lib7NJ_+3?q5C9spQ;KQ;pEgWzO>W|bi?xjPeJ}E'
    '$Ug=7ry&0n<e!54Q<eL^@nxr0qAzCs6kd6X?05<vJ%x{+!Yfaa9Z!)RPgT_><*kr#Nv+_qz~w2t`4rxK3U9_%P3hisE=sMUj}ohr'
    'RZrpfr||nz`28t-`xL%?8XrB4kDkUyPvfJf@zK-x=xKcPG(LJ7A3cqap2kN{<CUlJ%F|@d)A;CV{O~k>cp5)EjUS%I4^QKVr}4wn'
    'kbfHTPecA`$UhDFXDVmn@w=o}LOy<%XYk51c;y+q@(f;i2CqDWSDwKu&)}73D(B_#8kbr{X2HsM>=``v3?6%ita=9jJ%j(A!DG*m'
    'N6*0QStvaVrDvh^ER>#w(z8%{7D~@T=~*Z}3#DhF^emK~h0?Q7dKOC0!sS`GJWE_Z3#Dh_^7Ej!O>!C<HzGd|8e+BScQ>R~eVeLq'
    'M3-90zY7O;KQHSGCAw@?=aY9So{<H)RX?wsamHTxdF6~V*6{Pn<a_d3u_{JE{m)C@OgizOhx}`ko`!}`sI4h}LaZrR#ZO57U9q|)'
    'P2aYXzT~FHHaxuzPjAE1+wk-@JiQH1Z^P5u@btFwX<;D04c~6Vx7*66p+W67JiU#4*v8tijhNq7q7<q|ZW|SB8x?FD6>J+7Y#SA9'
    'TZwg2iMCPCwo%WvmHZHn@>8q4%4{R*wo$=;Q9A!jy!i_v@)tzpFNnxr5Rtz~diL5j={fr^h|gaTpT8)be}>Pi`UTPY3!?QGMC&hz'
    ')?W~x&y~+`!>2z-wRw(e^BfWR91-~(5&0Yu`5Y1X91-~(5&0Yu`5Y1XT>0!b>`9)Z5<N#HdXCtAj@W&U*nN)JeU8|Dj@W&UXnl^D'
    '_@87S7yB>1uIfT;g%OF^iY4U#r{vox`0Rg5ibB3um96+%s-yo&c3|=4gm;PGv#24thxtDx4Y8nn(TX+1`@}+GCFkDZ56f2K%)|<n'
    'wvewX{<~0V3-PWo{JZ*aFDra{d@cW5y3XK+-2YatGrqF_tz2jFm+_y4pZ!QauVkg47p(AugXt$ER-3xC6;7@AV$!Qltv1OZb3R!0'
    '!JXCdhbOPq2f2lKV_LMryM&NTt?({!pcP*W?-If;v0_O@g8!TR@?va-3@H3>@*9*TKm2b+d!jG=SV;KG;IZc+@jN7+hs5)ccpmM~'
    '7qv&pT<r5`f4-<ad^cLIY^5Zghs5)ccpmM~qy2fbKack3(f&NzpGW%(Xnz6iFQEMew7-D%7tsC!QSbsJUO@W`Xnz6iFAxPUK;i{R'
    'ya0(8An^huUVy|4ka!UiFGAu)NW2J%7t#JAo_-O1FQV_oqQ2xg@6;;md$Fi5N(jD)+80s#B5Gem?Te^=5w$O&_9fK5gxZ%-`x0tj'
    'Lf=d1dkK9n;mwy&`x5$ILf=d1dkK9nq3<R1{W7yMS5^NqvjQbnah(o}>MzUdbXawMnOU8p!Y?zcQ^pF5Z~QK4-A&KWepy^Q(sSrv'
    'mgZ5SxP2*Gx%f@<MXSC|`c0a@EcUzMl|pQ_Nfwq^P8>hM3JXg*xe{B+auGf~Ty?p}tP0ms={QrX*b`M@rLWZ#uPhhdGu_7}MzE5z'
    'lB)1x{+GqGlB!rjlv>3uD3B<hj-;PZJ}XJBn&cD0yZ*9xRuVu&xnG5Kvo`sJc-c;^<P+kh`BxQ>#eVr!#bc>eSCjm^u=uA|(peRf'
    '_bhc?F_&Lex~_QT{8gpvikJIeRr;)4#!8<3FIl;w6{D_AG{llhRxXUV6s<&2A&RZ6AASY-UqR_*w7-n@mrMObK5U6zhQ!N|co`Be'
    'L*nI9ACin&zFf-ia1@(=8SO8l{bjVjjP{q&{xaHMF7+?rs$(ll;$=v@42f6B%~#0HSIEX!$i`R5##hM3SIEX!$i`R5zgNh=S1Nna'
    '_#<B-8(%@uE9BTK=zE16dxfleg*<wNJbLA8T(Wue3Yqh3;^o&w$ghczUlS9*CLexHKKz=P_%$){YhvQpM8U6#f|8XB)ik!U%zh1}'
    'U!(R_6un9Yyo$b8(f2C)UM1#VCFWm6->c|*6@9Ow?^X1@ioREg`Bzc<Dr#Rv?f;eZg&R19|0`W}6x#IvD_wOMgw6e5={kdisB9(u'
    '#Q&8(J-kc&o|PUfd9B=Mm8`T6sVZB^C~C0Et9J62<yE_A6<6kxm9ETD)o;-78#Mf;6j@2f@*5QW21UO?(Qi=n8?O2{T<34N&fjpI'
    'zsdAVRb?x^>i<`|>SX%u|CO$~5VGq3m99FOwkuh=vXy8EnVSE9WeuUEl&v7BP_lBx*NTe5=T()g5NEmAN@F5ao2u&H67#<$=6_4f'
    '|CT8KEm8hkqWrf+`EQBx-xB4&C9Z!<T$ik%D7==9^4}8Wza`3l$G-S??2CWLzW8_Si+{(y_;>7!f5&e3ckFh5SE}>LRsW8?@9)_A'
    '{;pKnLqNt>b|?HAz3^-F!mrT_zn1jEQC<3ZuhAL5#=iKqBsbgC6_S0<YwVU1D;AMv>TB$lUQ1%WO<i?3Iw@ME{`$2f1LF5g`sCN>'
    'wi7G7XOa)E(QUs*NBtTd^=ow0uhCJzMo0ZRlwOC@>ri?fF0Vu4bx6DpiPza%ybhPw;qp3MUWd!;aCsdrufyeaxV#RR*WvOyTwaIE'
    '8*q68E^ol)4Y<64+BeYm2KwGW-y7(A1AT9>=XwLRZ=m)K)V_h*H&FWqYTu-Hdz0SnP4-o9(#gF^C-)|u+?#ZAZ&uDY<Cotoor6_{'
    'nYK6S^4?^Z^(I~3n{;_^vafoRebt-ntKOv6y-CmaCYA3^dcHT=SG`FG_$K?RH|Yo8q#t~fz0;d?fN!yXc#H1oE!K{=SUcWg$M6>2'
    '(_8GF-lA80i(c_9R++b0W!_?yd5itSTdX;6(OJC(>$jl$R+t@$-!oqw2KL`Z``c)Ln^p8}NW2Y+w;}O1B;IC)eVY~bZM46Q_P5dg'
    'Hrn4t``c)LoAvf>NW2Y+w;}Nk`S%X__YN8N4jK0j8TSqu_YN8N4jK1O<@7v$+jq#ncgVPR$hdddSG|M2cgU)DQ2P#9^$vOT4w>@~'
    'nez_0@-7kbE-~>gG4U=@@GcqfE*bDHQSdHN@GepCE`EO(zrRb@^)6iAg~Yq~{XG=DN6f#6zW31g9{S!R%HJc(-$UPf=z9-+@1gHK'
    '^u33^_lWZMQ2QQg-$U*1>Dhlz&;EOQ_TSU9|DK-x_w?+)r)U2?J^SzJ*?&*Z{`+LgvNpN0V5L_b@*(`YY(M{p%vI;3KV+^tpZi1R'
    's&mzU$Xs=5m99FU|3l`gi?0>0I$!uh=BmSMm8;HI{ULMJg<zGhI#`vf4*#xl)w$~TiKX|6rT2-Y_lchOiJtd~p7)8K_lchOiJtd~'
    'm-mU6_t}NKPxQP`^t?~>{E=PAAK8WckzL3i*@gU(T}a8w6<^ElN&Z-R4ka`YRevl!ix~bZTj`y<KXT{pkL+ds$bRLI>{tHC4&?(B'
    'eSo45Q1k(cK0wh2DEa_JAE4+1?nQopq7P8?0g66A(FZ8{07ZX7(VtNCClvh&MSnukpHTEC6#WTBf5Jz9DryMBO!=~vD*6+O{)C1<'
    'eN97Zg?A}beaJrGL-qk5vJWU(rGJ;*6@1A4=tK4h9~Mt|(yRWE`)VI@-|0j44<E8)_>g-qAF?a>kX^xt><T_)SMVXbf{#k|EUpEG'
    's*fP?5hOl>#7B_$2ofKm{Ufx0gxZf#`w?nCVn_5*QG2+~eA!A#e8fGskKpnVTt0%!M{xNFF58RWtdOe?Dz+EDOCd~v<fH9$a@*<T'
    'wzHGkPG7g3zHU2x-FEuA?R0C~ITPQ`-f26%+xFsFNz!JOt@KQMJ3FcE?4-7{liE(b-cHZAo$9@vo^LxlsqJ)t+l!Nixv-H6R%Tzd'
    'o$hcu-QjjlskU>@zMVbScKXQe#o69m5|cad<_^5M18?rYn>&)<G6;VeFX7=YGrrw{Z+GC^9r$(!zTJUucNBe_J_)h|Pw&9fJMi=l'
    'JiP<o?!dP@f^Tb6eTCF2dpcOPQR(U59mScid@|Fvqxkf1A(>IyQJksCCsRo~h>#sb$POZ82NANPIIWdSX76?oFFS~r9mLBH;$;W%'
    'vV(ZpLA>lBUUm>KJBXJZ#LJ&KFaI;=<$vac{Lh?_|Ctl=KWA!Wu(Idnf94LrpEETwDqHE<+MhXD|1&4+f97QU&z!9PC8MFb@Ry8+'
    '>il0a8me=D$!MsK{*uv9sQL?a{x2B~)zyDt#rq3&{x7U?f1%F*g*yKiYWZIw|5wQWl{*!G&8%FhRq@JS@ycKE%3txyU-8Oc@xxys'
    '|5wQW74m=0tWHtcO8xLx?r{7Kulx<K{4JxeQ1v%f=D*>wzu~dJ;jzErvA^N5zu}|5;g!GPmA|px{tX}foeuEtbbx=S1N=K3;NR&0'
    '|4s+^cRIko(*gdS4)E`Ed4Dg~$b2XiWh?Ds|4s+^cRIj-py3~A_y-#Pfrfve;U8%D2O9o?hJT>pA9S(*K+!)?^pB#3@Ea2OvXv_O'
    'M^$~YAcfZw3w_xR_hb6HkLl|^rmy>$==qqw?&D&<r`Pf^+5a&;-^aw+$Mk$36LlXGbsy8aeO%fbCi*_6llz!X?qfQ+kLlz-A&)+R'
    '#3zvW1QMS>;uA=G0*O!1{t4PYLHj3Y|D>orpWI*h1QMUn{eD6=enP+d3CupJO1|c#Sa&~x;3p9L1cIMH@Dm8`q<h*)_q3DlX(!#&'
    'PP(U^bWc0!o_5kb?WB9!N%yp~m@DZMw>#;jcG64jq<h*)_q3DlX(!#&PP(U^bWc0!o_5kb?WAAYNr$wP4rwPH(oQ<0oyF<)FzX)P'
    'Gutoiq+i-ezqFHnX(#>CPWq*t^h-PGiFVQx?W8B#nfz{9eRw7`Ch<?!>3_0L|C6=&pRC3IWG((DYw<r>i~pI)v8d{w^h^I_o&G25'
    '^gmgr|H(T2&rCk#s{X}V{4dtxf3e>Fi}m(jthfK7PW+4Y_FvSAe^D|2MV<H;mEm91f`5_4pF;jq$bU+Q^eG+Er+DR4yz(ht`4q2w'
    'idR0xE1%+rPw~U2_~Fw`t&7T5>XlFFo<5~t`ZQC|a*0*(-)H#mGyL}%z0_x{0iWU9&+zSM`1Uh=`x(Cd4Bvi+H$TIhpHb&O!?&MN'
    '**~Lte}>;bN5ki=W1q8*ea<@eIT~WCKGeQKKo(osRqb;Wea@=(Ir=_lRr|cCwonLnxj#qy=V<?&Rqb=Mf6l7*Ijh>|aQXaeT#_&E'
    'N<KYU*){HS*0|4E<34AN`+}_cf~@+2tonki`hu+bf~@+2tonki`Xb|pU}bac3v%oWa_kFo?28QfsBEPf_XQdE1v&NwIrarP_60fi'
    'MTTy!>Ps^2OET_DGVV*F^-D7DOET_DGVV*F^-H4lOY-kaqV-GS^GhP~OCs`1BJxXO@Jr(COXBQH;_Tn-AO6k$;os~Z{>}d3-|Qd$'
    '&5q&U>;wK?>SjW?Bvxf-^KbS6|1NbiVbv~M>Acjxi+7X4n}kou?h*cjhX0`9KWO+58vcWZ|DfSNX!s8r{=>}Ie^B%v6#WMc|3Sll'
    '(C`&?@GI)zSJc6;iW6YzwS2`q*jLoSub6xKidFk7=AOP{_U9|&EV1fJSN#=}Kwq&2e8nWtS5&^Q;(C_6OL&B_@D<hVE2`U9RJX6F'
    'ZgC%&p_Eu<N@XjdlssTqrj%MGF2SmBNv#r>#ELbfRjOpAlv1m-lEhYqS!$J-C03bPuqw<_tHdm^%FKdQVHS!;g;}sF%wj9UEV0VW'
    'f>mJ_!7PGV1hWWc5zHdEM39Ie5kVq?L<ETl5>b&vTG=DGq*iIYji3}kDS}c2r3gw9l;RgN`@djS_J6UJ+3}@TX~&mX<sDxx%I^5e'
    'R<h&EMcEmb#0uvqQMkijveJo{)T(cjOMW>eSe3nDuqwO3)GF-;b5VBx7p%(uFSar}zSs&osoL~AXme3^kC(A>sa4tIWvukInxclJ'
    'WT#IzC+9?oRoUaER%wqHTbW&5YL#|%iB;a!1*@{FORdtbE|16Zcr1^{@^~zd$MSeAkH_*wkA<<4xParoJpRk$u{<8j<FPy*%j2;;'
    '9?RpgJRZyAu{<8j<FPy*%SY+c=>ct6FtYy3<G(!q%j3U1{>$UPJpRk$zx>zy7k&pkC<;kkz?%iUS-^h<{8zw#1^idQV+C@ofX7N!'
    'I%8JAe+4{NfP4Y+1;`g5Ux01_o&^XNAXtD|D4><8q}a+#B~?e+sif*CJBL&qW#^E}Rx*cF9c3qvVk_-Y!q=3Rt#tCJI?7HS?Gj~Y'
    'jdqE$vqrl_*;%7qqU?0hE>U*6XqPBEU9?M-ohRBQb1fAsohRBQ%FYwjMA;6oCdzhzHBq($tckK6U`>?m0BfRb2UrtjJHW&$cYrlf'
    '_H4Ukr5#{Rl<fc$tK8GpMA;6oCdzhzZP3sL4Q<fS1`Tb{&;|`{(9i}AZP3sr%AU`+K|>ofv_V7oqLj+neH#?j(s|U<dDPN*)Y5s>'
    '(s|StyS03>->i+YyQNxsw_19XT6&aPx{_MDl3MzZTDpt)|Ih55YUwp<={0KUHEQWKYUwrV;8F*dI=Ixqr4BB2aH*rGt%FM)T<YLb'
    'NAFe#r8+3p(Yw{btPW;%P^yDc9hB;zR0pMcDAhx$9!m94s)tfNl<J9|dbrfXr5+OXkf<+`$R{T!^-*>oUJsXgdfIxr*m{`7Z=cz*'
    '*AsR1@T`YtJv{5-Sr5;)@N5guw(x8V&$jSv3(vL?Yzx7*L{?jPwuNU~c(x_Z+QPFfJln#vEj-)8tS!vi!mKUK+QO`XuB3skq=6o@'
    'fgYuS9;JaErGXx$fgZDguCjq1r6J1RF>0VkX`sh!pkryE$84a-Y>2XVg&OEMgH^dJ)DUIw3N_G;Hqa9_&=WP#6E)BiHPDSV(2X|G'
    'F9oY|H>rW%w1Hl#f!?%%&Z>dVs)63Lfj+At%HAVtpi^x}9<?Kn+L1@?qU@<(JF==BS=ElLYDbl7M~<~4$J!NhtPsAEsA!c=3)_)#'
    '?Z~)xWL!HcSUYm89XZyH9BW6-YDdkAt;{K7JF>AI+1QS3Y)3Y>BOBX8zCGmIL%w}NK3NUpRBewR+T(}z_@O<1Xb<`JkZ%w9_SCxe'
    'kZ%w9_K<H6>-Mm259{_2Y!AWq5Nr>@_7L1PDn7*&@5~B?)QYns93G}t+JEK}D}7Qa38vHve;Gn#*Gg}iORZvW8vn~(D_)7Y>{{_k'
    '{29AO#b=Ykr&p&|%r|^`YNdT^F0qnMwU8X;?ON<V)4KyDE4@3gYm|TpzmAf=X9&qQ$^JRD(oQvf&p0I8gx^Z3Dip2I@5X!b)Ji@f'
    '_-NOpu!m2G5)CCQRaB-MTOHup0iGS;*#Vv%;MoD59pKpko*m%X0iGS;*#Vv%;90V&lVj5k@azE34)E*%&kpeH0M8Ea>;S<I5bOxS'
    'ju7k!vyL$9SXzCP1ngK^eUr56SXzCPwCV`Kju7k!!Hy8@2(ymFU`LpBgjq+Jb%at!D0PHVN20DH%sRrX6U;intP{*S!K@R^I>D?H'
    '%sRoW6U;intP{*S!K@Q;)(K{vVAcs{onY1pW}RTx2}+%y)H%w217PPU`wf7dqwF^Tc8;>&0N6Roegk0VDEs|<oul%ve8vB?bEVI!'
    '%9XA3J4HK3+3ytX9A&>TvU8OE#>mc5_M2=wN7?U(?i^*m^DkrNDpvaa(4C{~H$r!bvfqW+1rl8#(FGD+AkhU9T_Di~5+y7BcGWJB'
    '=mLo@QTCfOyTGLjT)ITr@B8fnr7ltSJGHyOtP9M#z^n_*x<uLU)b0You2J^8CA&hfD+Iejuqy<+La=L;{T|4!@aziDu0&Q>cy@(n'
    '*C_ivrCs6K6`ozA?6;40g=bfob%j~CDEpn8-Qd!VIO_(bZcyq5rEXB_2BmIM_PaB?!K@q1y1}d)G1v`e-C))&%6`*pHwbnkKD)uQ'
    '8$7#3+3$Ak2HkGNZZ}wWgLOApcaO5)ecBz?-J#nZy4|7M9lG72+dayDYiW1rc86|v=yoR}yF<4-bi1RkN0j|;*B<EWL1gtnZ4V-='
    '2ikj}y$9NRpuGp$dqmmqZ|wnz9z<Oaxb%Qa54iLo>UzMX2V8o<r6+28qOT|VdZMo<`g)?TXH@=0%J`3aR!$FMkM%@RPZae;QBOSG'
    '6AeAdm7ZirPqL#Y`Ox!g+Osj=izw&?mtI6cFDUhbQZFd=f>JLi^@36_{N4*ny`a<!O1<FHi;B_<O1-Eky<pZ0X1%B=y&%{Ng1sQv'
    'o2=>$!QL?I4YS@b>kYHsFzZdO^oC$>;;c6Wdqc1{1bY)_z2Vs#wSA}|eNfwn=;?#@K15F+Nc4e3A4v3pL?1}>p@#H<OCPxOA+q|w'
    'r4L;Cz@-l)`aq&D+WVrmFZ%kTuP^%gqOULd`bOnnyp8fzeT(|iU(N1|+P<jmOBD1)Utjd~#qWJl+ZVO{@OwYB_rve~Akh!M_k&A6'
    'xb%ZdKe+UROFy{uBMSP#r5{}SL82cd`k}oa+WSY@?{)8=Ictsz{WE9Hxzs9Z$mRQIG-RygiHH7C_Pg8rN9EsEjjya^rQhV<zj*c='
    'CFiaEi)X*-udwznp6^D<UEqwBt61sp4)iZp#c)a$RcEYR$*NCIw{lr4ms-JpQ5<tYZQ06|tYY+Jtz6NHNd&q<d)dk*R^~Sl`bXK{'
    'K<HmNGfqFRe1crEk`v_g^UCMRMXTts<P*v@IaujwXgFsNBuZAigU$`Ww*#W=clHm6vftT1Aj*Dc|9~j_E&XLH`Ii0x_;vuk9e{5K'
    'MA>iYAAqM5tNfc11MqudmA}D%0G=KI-2u=YfcAk=_WS$?lEnkb;(=uGK(crsSv-&|9!M4sB#Q?|*>C9|NQE9qg&tTU7=AXsY^C4X'
    'KaiXrSRxoEeWQU<_V*?RmI&r^$-m2fpZ~xp`|A?}=^zHuK@6mW7)S>(Fcb4ZZ6)R_R@z+*jIzH>F_2zkAic)GDErG41F1^`={yEz'
    'qC6@Lin6~<F^DK1L<Ji}1sg;K8&o>~td7!m$<(t!)U!cR_LnIJkpY9qfI(!yAmVxu^=uF|YY<gx5Orw~m1q#PXAl)-5H(~FRbx;f'
    '7%ncjHmX>Kl2xuDgUF-7upSKS!BmvNRFuI~l)+K<S3m|+Uj|cO2E%$VtOvt-FsuhtZ3aVrFcoDm+6SX{NR<7(kRkL1L+A^JP+x{n'
    'UxrX$hEQLIP+x{nUxrX$hEQLIP+x{b+20EpLYFXvE@23jXb6>P2$g6Em1qc+Xb6>P2-Ri?)n*8FVhA}sge)G)<k3(jkA^aNG?dAs'
    'p-dMIWhQDU^F%|LCn{O#jQmihi-tyZ=^e6g4=g{l6d}nt?a<OyNBQK_!{J?R(tlRR8q%qx&})Rx%T6T?L*Fp;4MX2B^bJE_$x7$$'
    'hoN>DYKNh382W~xZy5T9p>G)ahM{j5`i66tbU1fOhjW*7ICnxzR;p+?^F+g$CmPOF{BZ7l4(HzIaPEB$XR>2BlO4mE_a0u+o?K^r'
    'dg>pRoP4nA%9MszNF@5QcS(nHUvxP4MMpqs1e8WVX#|u;z-0tnMsUA)1e8WVX#|u;KxqV&MnGu<ltw^l1e8WVX#|u;KxqV&MnGvK'
    'ltw~nB$P%%X(S{@qJ1RVN1}Zs+DD>&B=^ckLSiH&MnYmFBt}AFBqT;cVk9I+F$pw^NuW_o0*zu4XcUt`qnHF5#U#)urj<uA2{ek?'
    '<x$K9jbajL6f-=*3S^RLpI~LCc7j!tycVV%Mlr)PiW#0!nVnnlFN=G%D6vYrv+xO({aBP*#cnjH%}xT1ViIT+vp=Jl{TanX&nPB('
    'MlsPdDzlDNRX5_XMm*Mt#~SfiBOYtSV~u#Mk=d<A{MU&88u3^o9&5y7jd-jPk2T`4#>~z;U$#=Zjrgw-|25*jM*P=^{~GaMBmQf|'
    'e~nCXHR8=iyxE918}Vi%-faAuH?uQX!AePl?r=1o9*w6*<J-~rb~L^njc-Te&C%rFXuLU^X9q^(+tGMsG+r5vA4WrdG~`D^el+Aq'
    'Lw7VhN5gY8Jjd|tz!;t#7{jvzV|aF849^aX;c0;}JS{MWrv=88I-St6=f;#eo#erjF{LX@zU6jIsnbcGaTv>U1!H-xU@XrSjODq4'
    'u{>8WmM00u@+84no+KEXxz6x;mFo<jP`S?Vo|Ws&N8{)!$I(@eqpKW8S2>QZavU@H<LD~K(N&J4haN{)IgYM!99`u&y2^2MmE-6t'
    '$I(@eN8fn#jYr>j^o>W~c=V0unS=4@8;`#6=o^o|@#q_mzVYZAkG}CdxiB8J6X<&;(DzKB@0mc~GlBWR3CwX$pjVtghctnnXaYUa'
    '1iGLJbUG85xtu`XGl9Nm0)5W}`ko2&Jrn4ACPHE&Bql;)A|xh4Vj^AhL`Y18#6)_<iEx<+mx=U>6QMK_N)zES5iS$qG7&Bl;W7~}'
    'li)H5E|cIg2`-c1GKmP81c^y#pM>^FOp#7ves>ZiCebxdVq$j^lqL~NlVCOpW|Lqx31*XEHVI~vVKy0NlVLU)W|Lty8A_9hm&q`j'
    '4715Fn@sdfhS_A8O@`8BxJ-u2WVlR*%VfArhRYQCmnrlwQ|MHu(9KMto0&p4Glgzu3Z3c{debR%GgElVU<%#L6rL8CLf<-trv;|a'
    '#ZKYbfhqK~Q|M`@(9=$#dzwP`G=-ja3cb`6dfF*;R#WJ#rqEeUp|hGoPdkO4b_!kB6rN6)LWetrj%*4Y*%Y2Km_mOxg?@Jm{q9uq'
    'XexO$l{}it<oi^zYARVZl}a>~9Gl9l`&6DXm`cV?CF7=&aZ{;MQ^~QZ)TOCp+*In)RGurCN;Xa<8>f<uQ_04uWaCt_aT;`|L3bK-'
    'r}31*G+0lA^)y&dgYGowPNSYpgYGowPJ`|=cus@hG$>7j(ljVdgVHo8O@q>O=8UH^XFQ#G_UX*CPiL}tI+MlInI4|b#PxKhho>_='
    'Je}#`=}f6lXO?(6v&7SxC7vD?pSBEh&H2<S&NZi2X_`K<iXCU7sLVRikUVY?Us;&VPOWfdVK#eur5nwqR(fUeuCi!_D~p@`)Jm=_'
    '^sUpG46j&utdwWjo2iwVhn|7QX5g_Icx(n9n}Nq>;ISEaYzFh*Gw|39JT?Q5&A?+b@YoDIHUp2%z+*G;*bF>21CPzXV>9sB3_Lai'
    'kIleiGw|39JT?O#&A>-9@X-u>G!q}q#78rk-k-_z{!FI#XX3G$cx)yfn@Nt%#A7q@*i1Y&6CcgQM>Fx!OnfvG9|bEYieE?+1uJ<i'
    'QIxI->5tjX#A7q@*i1Y&6CcgQM>Fx!OtNYw9-E2BX5z7#cx)CPn}x?_;jvkGY!)7yg~w*$u~~R*7CANxkIlkkv+&p~JT?oD&B9}|'
    '@YpOoHVco<!eg`W*epCY3y;mhW3%wsEIc*~kIlkIv+&U@d^8Im&F1d-Y$g$AGl?*pNrc(V9?WL;V0NXWj$fY5{qWh`51-9^!EENG'
    'W-~=Io7sce%uCH?5@9y;QnQ&$n9aP@Y^D@uGcPrpnT6TROU-7YXEyT;vzd^Z&2+<TCZuLF>oA)Mso6|7%;tXo96UCMd4@U6Gt6P0'
    'VGa`vbC_V5gU9CJu{n5b4l@gL@X;K&%;Bo%GG8#4iGsOI6wGC!U@j8{bD1cZTe|9GMsO~(g>#v?oXga}T&4!*GAA&X>7u#J6U}8#'
    'U@r4SbD1Za%goSRCJN><B{Y}$f_Y46%ws}h9t7txp)n7h^WZrTp7Y>251#YjIgcrfc}!u<gXcVW&V%PXCb{M@$u$qw^O)qC2l;uB'
    'p9lGQke|mS*E}Y<=HZojcx4`5nTJ>A<A?e9VLpDCk00jahxzznK7N>wALiqS`NZ{n{4gIs%*PM&@xy$`&xibc$j^uTe8|s-{CvpI'
    'hxL3|&xiGVSkH&`0%o@sQ0o@3IxS#zTEObGfH}DZtW^tGs}?Z3wSYRffI7H<I=Fz9YXPg%0@kAitUwD`a~815EMO&Bz}m5Z)nWmY'
    'aSNCZTfo|}fGWHYx(lJZkd<U1E6GAul7&phEo5C;$hxu+x(lJZ5V{MYyO338A^H}gXb}@`i^$DIWaA>TaS_?Lh-_R$HZEc|Z4tS-'
    'h}>MnnzM-9TtsdzA~zS2V~fa@MP$cfX8jg3>$eyZi&;q)Q^6KPX)zUSG0YajY%$Ch!)!6k7BlO&m|4HY@LUYf#jH7tsdbCtxfq^{'
    ';kg)|i{ZH#o=YIO1cFOowghHNV73HiOJKGHW=mkU1ZGR1v;;~^ptOXjTLPseP+9_|B~V%dr6o{W0;Q!?jipqLrPSo5)a0eq<fYW)'
    'rPSo5)a0eb=t<Anmr_HPQbU$fHI`D7mr|3LQj?cblb2GHmr|3LQj?cblb2GHmr|3LQnQv)lb2G#mO*zJbeB<+mr;|KQInTZlb2DG'
    'mr;|KL3bH+mqB+KbeB<+m!WSNik6c{%gLPO<jQh#WjVRBoLpH>t}HKUNTzw0^Ze0rp37QJ9xW%2mXk-zsou-UoaJQBax!N*nX{bC'
    'SwX#CLA6-{r4`ic71W*;5L`j+Spm-#@LU1U74TdE&lT`oLG@liU0MOp74TdEvlTE~0kah_TLH6`P+AG4m2g=Jmz8i?373^{SqYbw'
    'a9IhLm2g=}oUMe*O1P|q%Sz&GC6rb|X(g0aLTM$GR+Uf8a`{5Es(fM=Te(%`yENfssALr?R&tt_kI9s+a3GN@S%u<j#R;3_3~*I>'
    '9wppuSyi4#3HP~Hl~3BjN$INM-Lfe8!nMST-zI!QVkM{9)z#svR#z3z*2-3LKPQ~bB!8LQ5sQ)=v56JlC3%#5Rrzc!O0<{G)}lmv'
    '>1-`Z6s2d>)yYkwRmBstvK7A0vQ40wyi0QLEPQ(M?`mt(>6=1OTRu%oxYQ?llP~6tU#m~TAeSt-!Ah<=`L*W63RfMHKU!Tm<BYF*'
    'b>)mRzUtN4`)Y;N+52kw)!F-M@n4qCIKzqOYJ9XBAFakmtMSq5;yt%0S@KrnvDIZCg%i)!Wgiu-<PKaoAxr*U#$&6C_uQhSfUd@W'
    'tMORH%9pIN|0-6#XjQzqI(z3XSViCF6J}XYuP%E!k5zmv<M)b{FInX%s95=;Rf&m;l`mQ8=OrG?#>?s?UXuHpiN~_hvpReCv3hm('
    '?qgwf_U>bNm!uSh$Ihyv)kNLuB<f=Fp<EZOQVg!n-lr_A&fcfYH<i!e!)bF96{U%a(nLjRqM|fWQJSbIO;nVo(u7;`a|KPrZWFQF'
    'M6@;$pG{PhCMrr36{U&zY$76?s3=Y4v->C^k&V_S;<Jf}Y$EEKh_j|7vckE3Se}}Qx+dbRDT$@PC1h$7an?jEH4!~cL_rgNZ=&`z'
    'SMIjN|FoG()J!F6rV=$%iJGZI%~YaheA|p~oAGTkzHO!wHRI`KDp50)sF_OCjHjEaM9uiU8BbTNeAz1by_qW2OcXRzrJ9L}W~x*('
    'RjQeIX{Jgw6FtpDPsPfYtx_yCQ^A^vtY#`$GjUe2@@1<Ob<I?_W~y5=5!p<2YbHLMscy|ww`QtaGu5q`xNfGpH528{RJUfT+Zw9d'
    '8mikGs@oc>+ZyWG8tT~^qI?Z;y{3G>INWbsLzJ%}uGdh()=<ILP{Gy^*K3I6HB_)Q#Pu2?c@43<hG<<wM6MwQ*ARnih`Kez*%~5i'
    '4Y9PQ7%%CsORXV#)(|gi@cSA(y@q<$LOpAtp0!ZVTBv6&)Uy`qSqt^71y8r&=@vZQf~Q-kXD#@>g?iRPJ!_$!wcz&_>RAg>(1PDv'
    'sAnxiK@0V)g_vlep0yAmE!49X>RAiX(?UIKA(mQ*r55U03z5}AJ!>J(TBv6&L|qH@tc4hCp`Nu6krgYSvC>-CLbSF}>spB27HVA!'
    'wXTI)*FvppA?91CbuDB-3$?C=TDO*IinUBrtYw;FEz=ZhnWk9FG{suxU)C~Bv6hL6wM<N`WnyA2QxR*Kidf53#9F2z)-w69mdS^;'
    'Og^lw#8Q-eLMeKpd}^if5+(0hijeqn)>dL7{=~JFC`fo_=U>(`Td|heinYvEtYx;Ml`7Rrm1?C*wNj;8sZy;}sn)WO!i-BRHLI1H'
    ')k@83rDnBKrCO;=t<<Gf>QXC}sFiBdN_}aiqO?*&TB#we)R0zcNGmm@m8#K7ooJ;pv{DON$^KUIy_I}#CEr`g_f|5zl?-ns!&}Ml'
    'R&u(PEN&%>*OA5R$l`Tm@j9}29a+4NEMCV<)H<?w9a+4NEM7+zuOo}sk;UuC;&o*4I<j~jS-g%cUPl(MBa7FO#p}r8b!726vUnYN'
    'yN<kFN8YX@Z+9#Hyjz-$yA^-Xtttu+K%`b(@i#<wOHOT*zl=XGvC_YcuPn8azl^UeSh0k<s&J5>ORc)#%~)Sz)s=oxG`0f3y4VT1'
    '<S*;Pk!KnOi531bkdMk%GUdEma#k7ZNPgldv68Q3kFUCD)fInxbhqS7k)t;0^Wmvg`kl~{l}oyr-663%BzA|y?!}*>OY{}3qP}1y'
    'v*1<X1M|BVXTj4sz}->1J8E}F?e3`E9ksioc6ZbUEBWg9aAid+bWic82P;EjcS!6Gi9IT6<F$B?if`k-ZjXvL<8Eq?iZ|n)Wsi!Y'
    'D0!`<C@Q{|DvAM@tX$D5YsiOBPpw>%?|USt%duCg!=5Cuf>#RRwoq!tT}f4_-+Lr?#9~U-;TKvHD^QB{RR^o4_%89aC06<_F^t#>'
    '<t<qe!nK6$N==)1Hy>N;A+f&V>0Dx!d>eCFkM{LwUyt_nXkU-^^=MyT@n0@^Eu(flYS*K7J!;pZc0Fp>qjt}dzHrsio+aOgCAGR_'
    '<w{nnJ#0{NdzQ2(Bc^+n)P@Has>@a~j9RjC#n+1Z!sk_$tiUA~Tgh)FC2GT8rq>yMn6s*S1Af?mA2#5J4ftULe%OE?Hb8y@<V#k#'
    '>g2VIA2z^q13WhpJsZiRjpWfr@@OL(Hlkr88aAS#WEF~5HnKLNZzEZ?k*wN?zKz7$M&fKEakh~-+X$CUkl2L(HsQZbXy1hPO=#bQ'
    '_DyKtg!WBn--K^Bp>`8$H=%YDYB!;F6KXe?)`#RbH8+!0o5`xpWYy-<+7XUQa+}Gq&84*?c{pM-8Mm2?+f2r7CgV1j)`xIqRV6E4'
    '9;)(1tCWqK$-m7-eR1<ym0Fc-+zWksp>Hqr?S-Pf(6AR8_Cmv6XxNLZ-ixc=iyE>Q8umiNUTD}tL~bD>w-AwAh{!EO<Q5`w3lX`6'
    '7~Db(ZlS(xAtJXBSzGB*w$h_)rAOIHx3-mTZ7bc{R=TyVbZcAb*0$2WY^8tMO8>Hz{$*>0OJZfanXPm)Tj^%D7CV;oS+=e8FI)dV'
    'SN9ztRei1xeCN!f2m&`vA;#V!h(HpJuu23hSRx>jW{Dt3M|y{)Er=B9O%!79AjO6h6)dQT()`&jG3F+kM9ejb1<C!*_nb2`=M&8z'
    'zS-TG^FGh>mTx`uFI~Z<E4Xw8m#*|~UFqGr(z|t~ck7DpUGcpuzIVm<uK3;+-@D>_SA6eEC)brut}D271(&Yi(v7^^E!9NWQBzsb'
    'E!9NfQz~nvR<SyDqdIk?I&~u+x)BfEh=*=u;cnENZq%G^spjJsomO-s0=kityOEQ-k(0ZTle-Z)-Kfkrg3FCW|Baw@BPiWSX1Ea~'
    'ZUl)NLE=V`xRL0;5#Mjb_Z#v3Mtr{!-*3eC8}a={eD99$-SM_N-gZY5-O)sMG|?R-x`RY_kmycU><%v7QAl?b(jAn#gHm@;>JCcX'
    'L8&_^bqA#$;L-z4^Z=zEpwt6R^Z<z-AkhOPdVoX^km!Lzdf<BxeD8tpJ@CB;zW2cQ9{7F}Rr@At@lDj?n@aCV3%RyvMe*H|H>Gbz'
    'i-PNkRi}`b0)VNNI20AE+VKy=tII2MH-&ov5-a|cq-y8ls(n)eeE5d=H)G(#e-{3a*h;>k@D+&_e?!5%spMbs)NzRm$+V!?*b0AF'
    'D>Pb(6~?}ywYn*dmEd3e?L{jpTb1E8@$qMd*T&?7l~1hjDdCEsp5WONJbQv?Pw?zndbeCfMP<oK@azemJ;AdlnDqpuo}kndlzM_v'
    'Pf+R!N<BfTCn)s<rJkVF6O?*_QZG>I1xmd@sTU~q0;OKy(ksO!++CS3SqVzLK&cnF^a7V&;L-~udVxeQkmv;xy+EQDNb~}U-XPJN'
    '&bT+Y^ahvS;L@9D>|MHDCv?WW(Nb?P>kUf1iOt@`W^WMeO>71${l3D7_C|xf!MZnC_YPPe9_}_syv-sXti$8`Si*p%H~Q=iE4^W*'
    'H>~uAl|EqI2dw*mbsw<q1J->&w-1W!1J-@Ox(`_Q0na`l*armrfM6dG>;r;*K(G%8_5r~@AlL^4`+#5{5bO(reL=7<2=)cRz985a'
    '1p9(uUoh)SO!o!Bz985a1p9(nUoh(nW_`h|FPQZOrM{rl7nJ&fQa@1Y$N0S;nDqm*eqh$GbQ^EjmD>*l`w{Q`N_T4oT>61-ztSDF'
    'g|ADkqCWd&;ypZBHv0P!{r$kYU$ROP-(?bhGn)(g#XQ8%QUI+Vtn^FPQ^K<pez_ki?-#QYZaqm*%5u~Xj{3zMg?pO<p#5O1U$RD1'
    'Coq;zt)k}p!B{^S>kni7VXQxl^@p+kFxDTA`ol_pSm_Td{fU77aMT};`olwiu<j4m{lU6FSoa6({$Sl7tows?f3WTk*8Rb{KUnt%'
    '>jCMAJ&JqN0qKZ6ihI)mblU^ywg)gK8Niri0ArE?bm9Z(#0Suc4=9ex!?Q#Kilg%IEWyf*Nd_<`89-k?fWCY{+=-|Cd=#uCZ4|8h'
    'fFgfk$*=G%p)Zd=rSND2=*tH%a=SUB&s^or84YHvF!@yY%_M8YJF6;gP8C@h#2Q;c6SXSCA%L4xorRUj)GFk<kWq3aD<99M-JIs#'
    'FkZ<Qtg;5fw<no4M1L-Kb6Gv{Q<t@rSRtFn_c=y4XEYIiO0i!`|E}0QrPkr$?+U+}ABcJeqMm`MXCUesh<XO1o`I-mAnF;2dIqAN'
    'fsEq@qNRaoX&_n}h?WMTrGaQ^AX*xTmIk7wfoN$US{j6U2BDrosAo{gqssX2vRWEc%4cCm^q_J+D=1_T${K{02BD=vsAmxB8H9QU'
    'p`JmgXAtTcghB@6?O?nejJJdFZ!obk7>@=MD}(WGa2g#!AW_LmVr4Mi4#wNTX;%_%HH(6k@qIA9561VwX&(~bpc-3cBnA^lgNdWT'
    '|AA663dzTHWeAuJ0ka`sHU!LufY}f*8<Juc`j>pkN)Q|Zf<r)X2$&5?D_7_>^0^@(I0OWTfZz}i9FkV2_+pc22zU+w&mrJB1U!d;'
    '=MeB50-i&`b0~NY1<#@2IW)yH^aYhAD?xWCcn$@@p&&Rk?iu3GEEN2qX$KLWI=13Ap;mnJ@zAu(s|*iTu(HSxP5ZjgL4?1{@-P%0'
    'hQh;8co+%~L*Zd4JPd`0q3|#i9)`lhP<R*$55sct^@?@k1ENu|!h~Je5|z)zRw2=ceQNoNVK6of#)iSzFc=$_YQ8c)EjNq^7zSg*'
    'U~CwS4FmaMY427UuPO`!`C%YG4CIG_{4kIomUe5&4JE_iVHi9NgNI@8Fbu4Rf%R~(9uC&S!Fo7Y7p%JBjaijpD_1VI!f%ERnc+7x'
    'JPe12;VBQHqYl5BWo0;VG#rkG!^&`284fGMiKF2}&TtqTo{oq@?;U<K8#%*ab2w}cht1)zIUF{J!{%_<91feqVRJZa4u{R*usIwy'
    'N5Ihtco+c>Bj_1Mz{3c7h7qM3M#I>C1RcZ(B4-4wi~#Eq={P4Kn9Gd-!4Y6K0?bCFqnChEE*b$!Bfw<@xQqmeksvV=Bu0Y7NRSv='
    'y8knr*B%KjBf(`PNQ?xDk-7Lv*gEm;Gf}WYjOF8Lj@T+hPS}?kz9Ea*$aJKbk3ky=f+In2BnXZK!I9}`Fla7(dlt`;;5iaJM}p@l'
    '^28|e#3=H_D3Bio@}oe06j+Y}>rtRPid--XtVe<MD6k#{)}z3B6j+Y}>rr4mid--X<VS)0D3Bio@}oe06uDp&JdA>eQSdMt9!A5%'
    'Xm}V652MM~qsiB!;b=4*jV51@hOyBwHX6o8!`Nsz8VyII;b=4*jV70mCYO(fztQCK(XcrhHb=weXxJPLo1<ZKG;EHB&C#$q8a7A6'
    '=4jX)!wl9KW~s(7OErdBsxizxjVYsB$jM`viygyU>=<UE#xUPHhB>4$%%YBAW@rpELt|Jq8N;f{So|ByoZMKv9gDYP@pde;aAWa('
    'EWVG$_p$gs7T?D*?=}`B#xl1y7F@<Mn>H4d#)8sVP#Omk<3M5@NQ?uCaUe0S9AkwK9S1Jsz-1h`j01^rATbUk#^L)od>@DJ<M4JI'
    '-j2uH@yyH?ttev^ktkYG*(%{O9$bo6lv>4GyTeYM@yx-G2f^{o?~Vt-@yzdzPjgSaxi6o!Ds$tR-yP2!{P;9W1to=V&(6q?2l?^L'
    '$d6}Ucs#6(XI^+bGr{9wY<$XCKqCHzq7{{`gw65H5|4-5@yrsBhw1S!T@BOKFkKDP)i7NR)73Ct4b#;yT@BOKa9a(x)o@!~y1PAB'
    'h>mKQt|oG-;k_EBtKqL2#;Reg8pf(&tQy9uVXPX)s$r}e#;Reg8pf(&tQy89u-mn0MH#EOH?(L)MJvPf1oplbttev^_l*{<sAQED'
    'G6985Kp_)Q$OIHJ0fkIJArsP_c=>qGY|*NWcb`s3_vz&0-KP^^dIC&O$V74Qs2s(K6$nhmo3V9xtgINp+Hpw;7kdROtCtCIJAwVJ'
    '6X0kfz1u|kvx)R)6EnV-tz;}Sk#21wqnC+vYZDpOO{Bk`NS`&4UTR{h<S2ee$Ha_(@o#2&sfqMb6X~8N(jiU4_euCZ3EwB-`y_my'
    'gzuB+R40MNB#@Yd?~~|MC()@+qEnrei(m9nCyHMyHVMoo(Tz?5!AWUm2r7^NE`#SJ@SFsmlfZKlz3C*-odmj*iSWrp_+%n{GEqF4'
    'D4tBDP9{<(6RDGl)X7BZWMXqNv01b#<MoHh#L;BpXfkm$nK+ulXlV+gr74V-rl7hhsBQ|Xn}X`5ptC9HYzoSn!iZ=JI-7#drl7Ma'
    '=xho)n}W`!ptC9HYzm{EDX4A=s+)r9rl7hhsBQ|Xn}X`5Fd~|Q25VrY23Bfdr3O}N7{k^uhOL3I8W^jAu^L9SHSkvhe>Lz|1AjFz'
    'Rs&--FjfO&HH>I$7}3_iW(_0S8n~^2+Zwp7f!i9mt%2JbxUGTP8n~^2+Zwp7f!nF%kf~JrsZ{%^<dCW4kg4R5spOEU<dCWKgH!1T'
    'r<T|Z`DH5I;Z(ZAsdR@^=?ACMB}}DDm`YxnN<TQ2esC%s;8Z%msdRu-$!=5W0H@LcPNf5!O3ycyJU9(jrh)u4ke>$f(?EV2$WH_L'
    'X&^rh<fk!eod)vLKz<s?PXpa);5iKhr-9%!5S#{r)4*&Rm`ww-TR5X~3ujbr;f%^HoZY#FvpctNcIOt(?%cxJom)7&Q?lYWPu;>f'
    'lv_B5atr5BZsByvEu0e$R=6S|d9!(9#n&Dbyf0eeQF0a2@qIeJPsjJ^_&y!qr{nu{e4mc*)A4;ezE9_T&UBEN4ieKrVme4n=bX)S'
    'aG4Ggw-)`2-w}6f(TC6?MYk58I)1IntwdGHieJETD<|o0Ek0TJ%!;BFkGW#2d<O1T&cNNuskd9h?*%I#ZZw|3bIzczo554h;HhWu'
    ')H8VM89en2o_Yo+_h#_aGkEG5JoQYTY$ne#lV_R9v&`gKX3~w$B!kT)OU>jtXY!mgdCr+U=Pb^X%wp%!EOs8vV&~DUvRZTTrzB5Z'
    'v@$!7W^vwd7AHt%ao%tiJCA0u^Jo@(jb?G4WESU1W^tZm7UxN3vDau8`_^U`<2`N~W}~y&#R!kvi`nRGb}_=^>o#V?^lX@(4b!t>'
    'dUi3U<5%z%tw4J|wTg<I&B@Z)a66k(!EBhG9p1<oeij50Tji*_4R3G5zuWNWHaxlwk8Z=G+wkEwe7KEVa2p=ohIVhmzuWNdHvGE{'
    '|8B#-IdD4%Z|5*GG>5pI1MhRdWe&X00i`*hGzXOCfYKazp94yBI0rokl;#lcb3kbhD9r(-x%fU8Z|CCQTs)eKM|1ILE*{Orhq*lU'
    'T%LL^OwYxKx%e;_ALhZ>Jbai3EA#MS9zM*&hk5ugk9od%WZ`*q_w&ff^T^5b;BOvC%maye_&yKc=i&Q&yq%AK^YL#!{>{g~`FJ!R'
    'ALir3e4ctfPdy+0=HtVBe3*|93#d5@s5uL$ISZ&c3#d5@s5wQevS?*0&;lyZ0(QbKpdKxt9xb3AEubDPpdKxt9xb3AEubDPpdKxt'
    '9xbH*TuA@9kp6Qa{pUjZ&xQ1#3+X=>(tj?b|6EA_xv-3GY-Rh;h4h~b=|30Je=baW@8sRF3+coc(tj?(_eJ==2;Uds`yzZ_gzt;+'
    'eG$Gd!uLh^z6jqJ(TOkOr2HaqSp+VNz-1Aq;TM6@BD(ZNV73U9785y(*+agVJ>-jts>MXrVxnp>QMH)JSxj^+CLR_O4~y9uzL@A('
    'Omr+JIu;Whi;0fKM8{&fwIv|21SFP##1fEL0uoC=VhKnrA)_n-mnGzoC7`qfl$L<f5>Q$KN=ra#2`DWAr6r)W1eBIi1C~+)mXg_*'
    'GIz0*Q(8+o*Rz!U1xq>Ewv<)irO6a$*zS^#t;{O$Qsy<5auRDPXMUElFJUPs;+8V6v6PcMOWBvOlrwNkne$l6oX1l3ax7&p$5Kwf'
    'E={}2;9o_pWnjGwte1iHGO%98e9tnlUIy07z<L=7E(5b=V73g*mVwzaFk1#@%fM_Im@NadWni`p%$9-KGBCRx%x(v>+rjL1FuNVh'
    'ZU?2?+2?UPnB5L$w}aB{pmaMZ-3~6dgUjvUayz)(4lcKY%kAKDJGd;TlUoi-%Ry;5-P&?6TMlN+iRtCcKrTmh%fWLw2rehWmlNU3'
    'iSXrMy_^VN&OGLFw7VQumcz<&W;~a}(Q;-rm!s?D@V6ZPmc!q2_*)JucfiUWuyO~i+yN_hz{(x4atA!zfv)d>l{;YN4p_MZtnUEb'
    'J3#ji(7gk6?*QF9K=%&Ny#sXb0Np!4_YTm#19a~I-8(_|PSCv*bngV+J3;qO(7h9M?*!dD!ShbC#+{&hC+OY@x_5%-o#1&Vc-{$~'
    'cY^1gAb2MT-U)(tg5aGXxPsB{3h-P3o-4p}1!LG1pt}NeSFo#W1z4{jzpP-TX$3s2VCT^aRK9|>r4?kG6`5?4{H&aNR*-vEz}O1*'
    'n5`fatzf-s1>CM+|I!NLXa#FoD`0vBOs`<QY6ZNnV8_x5qG|=auYmUz@V*k>SHk;BcwY(cE8%@5ysw1!l`y>$ZdbzXO1ND~#I1zs'
    'l`y>$ZdbzJN;p~xM=RlIB^<4Uqm^*95{_2F(MmX42}dj8XeAu2grk*k^gCAZf0yAQ{4Bfv{yWaj{f<2nzvC?8?>L|OJI-(ZE}j%C'
    '{9U+wKeg(__fMx*ac_3XO7@B+R_$<+bS`{Kb~XNYtd;+clWo6C-~SM{isf>@i=`A>g(&-728r+~L0I8u1uK6SxZDLUcY(`Y;BptZ'
    '+yyRovD5x8P`V40?gELs@b)gey$f&e!rQy>_Ab1=3vchn+q?1hZuV>3jqi8k``!3{H@@GE?|0+--S~bt-rmg_fV=ViZgxf7&CdS2'
    '+4*ocDBaCz$Gh3}e>a%j4Q6+P**%<_zlU@4_b}4Ghmrn0jP&neq<;@1{d*Yc-^1Ac9?r(!!`b+I7~9{&*!~{I_V+NhzlXE&_i#4;'
    '9?r(!!`b+I7~9{&49LAG>t2*~Z)xtL@F>B`>=C>do!!f>z<b#dc`vHF7iHa>zIPzmv2<_x29(Np2hqJ`qI-$Bd&xcbqR4yE;JrlL'
    'y{PA2)N?QDxer|K1DE?i;y#eL4<zmbiTgm}J|gZuaJdg}@58_Q@b5nSyAS{F!@v9R?|%HdAOG$rquh_T_v7vTczZwI-jBEU<L&);'
    'dq4i&Pe!>PZ|^6g+)qZipNw)pS>t|ixgT8a2bTxP8V`^)9w2KxK-PGGtnmO@;{me917wW{m>+zA9P$A3gAb5V9w4JUKt_3hjPd{('
    '<pDCv17ws3$S4nxQ63<pJU~Wy5G_53mL5be4^odFL?I7Sj~=AvJV-8hkgnuGV&%cK4~b9zmaL>Jc@UjFh_W7}0zF7nC02M{PdKIg'
    'AX-YS_-BPt!h<O5L6ntPwc~+elz#}!9s;w6!0aI~dkD-P0<(ue>7f**_>6SPN-%o}%pL->hd}8eP<jZI9!i!s0}O>=eF)4R0<(vb'
    '0YmuBLdt#!1Rnyyhd}Tl5PS#(9|pmPLGWP^d>8~D2Em6x@L{sl!<>zO7)3q|f)9h>!yx!D2tEvg4};mmVD>O5Jq$_@gVMvG^e`wr'
    '0!oj7(j%bs2q--QN{?`Zz$0Mx2$($rW{;r3N5Je6Fna{d9s#pQ!0ZuJ_Xr3+0)mgAx<|nC5%7EjJRbqiN5Jz@@O%_J9|g}xxsl;f'
    '(0vp<9|gfjLGV!!d=vy91;Izz5B(_joIDD;kAm)_p!+E3J_@>zg6^ZB`zYu>3c8Pi?xUdlDCj;0x{rbGV{|2tf%Rjc`xx4N47EN6'
    '){lYpV?_94VD=bY$z$AG@fdhMMvw9sJ<4O;P4O5V%VY5H7-OKv=w=?{-ipUS{xOh$4CEgJ`Nu$h709mw`Bfml3glOT{3?)Nh00gK'
    '!zy@K1rMu0eiiqJtb&JC@URLVR>8w6ZVXukE305-6|Ag+l~u5^3RYIZ$||B`6&$UCqg8OU3XWF6(P}ta4M(ftXf+(ICKIiOvDI+2'
    '8dg@r%4$wutmclT)#RSl<et^Axtg0|R>SRTxLpmmtKoJv+^&Y()o{BSZdb$YYPekux2xfHHQcU-+tqNp8g5s^?P|DP4Y!Zy5<tT%'
    'FY{5bg7@J?mib(46}*Vg{8T)S3LZxVkHh=pMC0RWcNm{MDOpLc_&8POajMMYRGG(N^Kn>tJgyyuZwRl%%RNpdd7Mh}IF;n_<jr#7'
    '?_%Gx=spg*kAv>xp!+!JJ`TETKz9x3t^wUOoS|9+)@#6e4Op+?gwq<3Uqg(oA;#7aV{71O4Xmtzl{K)k23FR<${JW%11oD_Weu#X'
    'ft59|vIbVxz{(m}SpzF;U}Y_=tc8`eu(B3b*22nKSXs--wzZsBTMJ`r$%<>?Z!L_ig|W3Twid?L!q{3ETMJ`r$(U>5Z!P?-g}=4%'
    'w-)}^!rxl>TMK_{;cqSct%bj}@V6HJ*1_L8PA0D7Wa2vbTL*vZ;BOsuY#ofPgQIoC*g6<n2V?7CY#msy<NV(`>d`vt(K_nUIyhQK'
    'JzB>ZzjainbyTNyRHt=Rr*%}IbyT2raJvp}*TL;NxLpUg>)>`B+^&b)^>Di$Zr8)@dbnK=x9d5Bx}Hc~5AW-V+x4hmJ#o7pO{_-+'
    '>rugaRIr|IW<Alk9)+yuEa`gsm-VP;J?dGHde)<!^{8h(>RFF^)}x;FsAoOuS&w?wqn`DsXFcj!k9yXlp7p3_J?dGHde)<!Cs4r?'
    'sNe}!6`o*r`3abQg4yLKm|cE?=zoHBgeTH<g!sg5$x2ogo}lk}f(-oxygva)Po(ecj_J!iLEe2Lpp^Wq@V_TO@Ch(`0?eKSr6)n@'
    'Nl<zcl%52oCqd~+aCtJtB|eE<vJ#Y@1f?gz<w<aPGMv{gJWY5nZxjV9XgR#kH_F9UL51;I?!s?o5quH^pG@DE9NzpJ{w|B>li>Me'
    'jA#6t@%LrXeG+t^1l=b=_bJeQ3Ur?W&!@oiDe!!XbL>x{!Kc9bDYDH|p!*bfJ_Slofzngp@)Wo{1rkqz#8V*g6i7S`5>JD~(;)FQ'
    'NIcDn{-?p^X>fTOB%TI|r_tck;PN!MJdMttMrTi>v!}Tw;A!xD8a$sybx(ut)1dn_s(Tu&p9brv!TM>ieg>?c0qbX|anFGKGa&yA'
    'SU&^S&!E9)K>it!e+FEh;ogI1s7}v-*)!CmXSl!M87j~-)SPFiInRLLGa&d32tEUX8$fUa2yOtu4IsDy1UI1F4dA%}JU4*g1`ynU'
    'A~$ev#Rl%J*nlE8fcysTpV$Bo8{lCBJZyl64cscR0aiA^$_7~304p0%`35-J07o0(XagKQOLzDzBe!Q6xjhS;&%)-jF!n4wJWJMi'
    'maOqCW3FeZT+fnGo`t_>$tcf~QJ#gdXW`*la>%pfkY^d4JxfM;7ObBI>u2e~o(1`5LH=2g-w5&>L4G61Z=^5Z2oD?KVIw?jByu(q'
    'D;w#yH^SIPB4;D~ZG^v#@V61hHp19O7~2SA8;Q7$@V62EHp1UV_}d778{uyw{B4B4jqtY-{x-tjM)=zVf1BWM6Z~z0zfJJB3H~-Q'
    'lG?=BX%pOTg4<1Sy9sVL!R98|+ytAOU~>~}Zi3BCu(=5~H^Js6#$%h{b`#ugg4<1Sy9sVL!R;ov-2}Ir;C2(-Zi3rQaJw09H#275'
    '%$RvI+-`>3&2YP!inkdyH^b&;*xU@8n~BuTaJw0fHdEs^Q{y(n(PmiLOpV)2joZv9c{3GnGi+|A;%%nlZKmRFW|X{{`nQ?-x0(94'
    '8QwR;`(}9G4DXxaeKWjof%h%&z6IX5!21?>-vaMjm@C;rgl|C;TZs29C}ax?*@8m0ppY$SVhftsf+n`0i7jYi3$rR)h~h2iWec+^'
    'TTssy)UyTkY(YI+P|p_Bvjz2RK|Nbg&lc3P1@&w}JzG%E7Syu^^=v^sTTssy)bkuW?Vn?({d4T5e~#Vs&#_1TIqocejx#FHaYp4i'
    '_Q*fSIh5zv-ToY>OP*uT`g81Ae~$BN&v9PuIrg(Z&nbiF@%?#xf1Yy%&x6GCAn`mW37!X+=fUN9aCshFo(GrbIW6!!C_T@Kfak&N'
    'dCmYl4}#Bw;PW8(JSe>YN-u!Y3!wA@D7^qmFM!eu+$8n_n7sgIFM!z#p!5PLy#PutfXfTu@&dTL01_{N#0wy?l`|?uE6P|!l!{hV'
    'wn~_71+$_R6|Kx^maW{gw-t1^a@*Thu-?l3Zd<wEZ7Zjrw!+F*&ctkmm93nK*~(pdTe(wvD`#T1a{6g&T#gFA8Rl^FS*!T7;^~>K'
    'oQ&GaUEEtaC$$w7Y~`HPR!-e)MIl=`b+eUoHd|58R&J%+%B^%;QPx(@;A}-_TRDTX71eD;bz9SWe*!LvRo37(G`I~7ZbO6H(BL*S'
    'xD5?%LxbDU;5Ib44GnHXgWJ&HHZ-^m4Q@kq+fdy$RJV;=1-GHWZRCk<C~_Mb+=lA5p|fqMXB&FihF-Rzmu=`}8+zG>Ubdl^ZRlki'
    'dfA3vwxO48=w%yv*@j-Wp_doAC#q;g8LN16QqhWvR_30lq7`MV;;l+WD=JxKeZGi3UqqiTqR$u6=Zom`MfCY%y4yS--!E0PD&sr3'
    'UQF+;$j4XcyvV)8FQS4MQNfFGV;rj|_AhRegL+cyh;U1IyjC7tho?HrC044lf|b?Mi`*CVA{@QQ&0a6U*h_TcFVTs=ltH3wCF?RT'
    'F$4J$z4uGZIljcK?MsZuUSeJ5B}UgTv3m6qb6qddQNKhl{1PMKmvS+jwSy*d`Ij=dgulynu`ki7z6>regUid{@-n!*3@$H&%gf;M'
    'GDy74Jj2W2@-n!*3=%IhUU`{$hL@RVcsblCT=>oK)KUIr5PTT~UuI_EW$=7C#xulNKK_&}x-Wz7%ZwOa2J4r>`V}(6D`bXOi2hfI'
    '{#S_bSBUUei11g4@K=cNSBU9Xi0PtL8K1U#g$RFzyT)H38ebtAUm+S_AsSyH8n=@_x064&gVJ_T+Rlw`+j%>~c5Xb|&fV?X$-CRh'
    'yW2s2JIHS*?`|jWZikiau(BOiw!_MHSlLeA-3}|;c~`@BSlP~f@Y~74+sVS)c^|`e-p8<=_c3fIUvDR0Zzo@GCtq(TUvEbt+fm4N'
    '6tW#nyh<i|l}z+1ndnt=&#UB~SIIrEG9U6P8TwW7(yQd2SIHW$k~Ll>PrOQIc$LiXD!JfQa=~kO`x@T9hPSWb?Q3}Z8nZvI;rna&'
    '{u<uCMizbz-(MrszDA~fjZFI*GefVDcV7d+*Ff+!^6qQk`5JlmHPC$xbYCOyz6RE>f%WTTl-J29uah-iCu_V;W_X><@H)}|I??|+'
    '(f>Np|2onCI`RHG5&k+6{yJIsbz<ywV(fKd>~&&n2l;ac`Ev(I>;Q=!<iQ=}!5tv610;5U#14?y0TMg7NplBp%-O*$lskCW#tz0+'
    'I~Z5(U|h9>an%mSRXZ40?I7>&fR!DvvV-x_4#r12$jLj%$vb#|&JNz6vx9uSgM7V%e7yq|>|jK+15NB;WU~W>>_8!JkeA*dFTFut'
    'dV@LYH+YN08|17v$XRcYrQRS*y+MY4gPipS8RZRTkl)}v4sY-thd0PQZ!m-W26M)5FfaTDx#taX&l_Z$H^??SL2xGs?gYV|Ah;6*'
    'cY@$f5Zp=D-wB>O!E+}F?j*DCWX^vlbN)NY>^sTqJ9%TrPFUH=EdNe8+R2+YcEZ?B7~2VBJ7H`mbN)NwZzufiq>}7}&7H8hlS;A^'
    'Zg;}%o8-th$&qi82j3(QzDXW@lRWq)dGJkg-J9gPH_2yjlF!~GpS?*wdy@?ICK>Ea>dKpBlsCyJZ<0~oB%{1ZMtPHr@)m1nZ?PW!'
    '7VF_}5jk%WId2g;ZxIh~q4KxrZQi1{d5e|ow-{l*MRdGH-}4rI&s)U9TSUNHX!k8Toww+8-eT?gE!6rJYJCf}zJ*%fLalGHLiHBf'
    '-31T3;9(a$>|zab7p&}pm0hs13s!cKrFM~*cCj+K3;uS&-!Ayu1%JC>Y!{5}g0WrXvt97F3;uS&-!Ayu1%JEXZx{USg1=qxw+sGu'
    '!QU?U+Xa8S;cqwm?S{YI@V6WOcEjIp_}k4I^lnz2cf;*&xZMr6yWw^>Z0?55-LSbEHh073ZrI!no4a9iH!IS+;dVFN?uOglaJw6B'
    'cf;*&xZMr6yWw^>-0p_k-Eg}HZuhXiU=RBX_Q35PxZMM{d*F5ty~ZATjXiL?2X6Pk?H;(@L)`9xzddvpd+09qz~3JD+e3G;2mbcZ'
    'UF@N|*ux%zJ@guT=r#7xYwST2d+0Ux&};0W*Vx1Uf<1H|d(g`s^s)!N>_IPk(90h5vIo8FMK62N%U<-d7rpF7FMH9;Ui7k;-6?y?'
    '413YiUbM8Atg#nm?L}F8QPy6RwHGbzMN50p(q6Q*7cK2YOMBV5vX?xu7oF{8=gMAGw-?pzMRj{o-Ck6;7uD@Wb$e0WUR1Xi)$K)f'
    'dr{q9RJRw^?L~EaQQcltw-?pzMRog_1=z<dz&^U)eRRM3=zjOn{qCdt-N$HtAEWtwbie!Pe)rM+?xXwN$13SQR!R5qCboU7neJoF'
    'bRTP``&cF2$1K1;W&!pw3$Tw_fPHk^`&cF2$13SQ)<yTRF1n9((S7vn`&bv<$GYe~)<yTR61tD>ejnZaKDzt2;r(rRe;eN4hWEGO'
    '{cX5?8*bl*+qdENZMc0KZr_I6x7i!>Hr&1qw{OGk+i>(Yth@~mZ^Oge@bES~ybbbigZ$ed|2D|K4f6l5fMDTAb!&xd!t;q$w|02f'
    'MJ}-l!C83Z0=fmOP6*ZTSMlE^Rw3~vKMO%tQ7ae!W_<LxZXwzWzgo0HOH>(Kbqd8Kj76i=svDRtJWg!Y4!;?)_x}qKkbFuZfBwIa'
    'X%j2{l-QxVmEj8Gd}7tDU74#D<r1s#WCgKA;aTECi{abjPl-3%)s1s&YQ^7PfF`z*Z!dg*!3rSNjjKgIvFg?iePk}NVk81b87so7'
    'EL-`C%H&zXcDK55C5aL%e0xX~u@!%N$ja})$~&;~4y?QbEAPO{JFxN&th@sc@4&-5DG!D0Qqb-@u<{PbzXS5`fc!gP{SH{a1J>_='
    '^*dnw4p_ef*6)DzJ7E0|Sib|-?|}8Yx%goUScfhlu>#iNrn`6H;azxm7arb)hj-!OU3hpm7Y`AFw*@B>EB3a4{JU`UE|K#tjJ*qE'
    '@50f$M9#ZJ&bzs|px3R8aY?MeU%=&ExP2FH--X+Eb8)dx7|SJA%2;fbBko;P@GdHN7Ztn<)9=FcyD<G8jJ*eA@4?u6F!mmdy$56O'
    '!Pt8+_8yGA2V?KS*n4pF9vr<#RJ{jd@4?D@u<{<Pyay}q!ODBE@*b?b2M_PT!+Y@X9z47U5AVUl`?=VOz(e6P6D#JS@R{$!(fe@p'
    'J{-LdNAJVY`*8F=9K8=m?}s(8B7zl(l_D6d41e##-}~_QJ`wjmY`zbh@5A5w#Mt{F_&%6@0A?S6*#}_u0hoONW*>mr2VnLAn0)|d'
    'AAs2hVD<r+eE?=3fY}FN_5mn;07@UA`47PC15o+^l>R%uLA6fZ;88yM@8Cnh_lo#kvWZo<(8-1SRsXx>ZMccGWEBRg$=@a3=HpL^'
    'Cu-{EgYy-^Dl}_#3!*N3;eQuB3Jp@p$_3C0R+>$70gL}GG93Uc{45?U)eZ3%z9AkEg>NW$7_9Ug;=fC?VnrA??l1Zmg(uq&@B86>'
    'KfLdU_x<p`AKv%F`+j)eUqmA2VLwdohw1%Al%nA6et6$ctn8=e>?a=f7g37GoBPRi`^k0t$#wh5b^FP6`-@n|Icq<eZ$FuDf02hM'
    'A3s^PI_*b;`^k0tQRMIA`+j3Z7QXNI==1mJ^Y`fU_vrKY=rdShhOi<~oBKU#{e66kZ>p?{-=p2%qut-5-QT0#-=o$Ki$27deMlzy'
    'kWBO;`uq@meuzFlM4um`&kxb(hv@S|^!XwB{IKYIJfr&|S?WWw)Q2efLzMg>O8yWfe~6MlM9Ckb-49X7hiKvtWfkNSEA=+9QcVN`'
    '|4`CI@bC{AByyF1$RLsaUET1;zi_+UA5vTj;KrYs_z*NvtKtvoQ-^*xu|gKkg(6<E!ltWyYK2#Ehq37&(kz@W{H(HI)lS|H7yyle'
    'RVNH;1K7FP3PaV(<TGm@9-gftUM%=SIrCM7Co9EfVjZ47OZ+KGuaOG@7p%C~ugImJ68HLH<|&t0DY^ldQa_)3X57!`a>;Wh{d|}O'
    '%S9h$qOqdZM;X<{R)&X<;Nc^9_y`_8$|y2eCFBeLepE(2wNh^js{5#neBs}Z%E%Wq_)!`8!e4#_@`+U#r`HM#2_L~jVuhcDsf>@{'
    'A+hQn5uP(xSynPulvrhsGFI}lB4bhbhAe*{mH8_;@eyo(RAw`Zzdgh4M`doKT-K^gtu)gH<g>hg1n(IudCsB=qJUCX6Caf|5#_R0'
    'K_P$41*p>}%OzI&EWye|@gIref>r16`0qmUNvt@tC!bl&`UT|wSkC%|RP@Jk)-U+<$8y$>lFuwh_#ewzKUcP*)CxqW{#6vMFfEl&'
    't<=AQmF4}9F#SjH{GX!l;mLCUQ}igjmNfdGq7Q+G{Qnf6I)2?~$qL_BS+t_`XX&$q&#Wj~aj{6Ox<|ww1uJDbq}EzRE1Vd?D&X=b'
    'o-?)zpHdN@tNRmA9b56w0`Gsqhd<%NpYY*N`0yuu_*44S@v>pbN__YeKKuzE{>*d!nJ4=*&+=!U<<C6JpNoA#h>rZ9iwX(e7Jf7P'
    'WPj$#{>+p8nJ4=gm4A%NKPD@FOji7utoSk7{TQ`=Om+I0>hv-7=ws^9$K?@2K`$Ruojyj_AEWD!$wVKMUp^+Id`tv<OlJ6m+VKgs'
    ';}dZC1YAA=mrtk`pHMA6p;~-GefWg>@JSho!dHGmwfF=iJ|VMz0xqAB**_tBe*$KokfA>T!B5E0pMd8l;Q0v|`V+G7Ct&>-^6p<y'
    '<X=$aU&yq7A-Dd8-1--C>tE34U&yV0L9KrwoBoAtTC_qmMg=R2{9nNOFCg*PV)Vyvj{a*g`U`C4^M5Tpb$INO6?ayDEyjBkRR7oF'
    'Q^)U${%bMb<M%ojth%8Y4yy>^@6t0rwF2~iExzj}e#`S;(_2K7w>%fEFh0pu{H?@8f#}M=@zj4SAs^QD{)P{KEAbFUU4O%)zv0o}'
    'N_ZB&q1NB<;cxixH+=XTKKu<I{)P{qqMlDt&!_Z!pAyBN62+eq#h;>{PtnV#<q=pRFMV1ZX#{s;tDN~hr4#>@%=amo?^8O!PwDwS'
    'rT6}np6^o>`6-J0l-})A;{8+lvrmclPl@nP>8w5_ia*WOiI;5iVY6SYU<H)&wZeI>17y<!WYYt%asXBiz{&wwIY4ebQ0Ac!a|g;i'
    '6#n!8dG`Q)`2q6o0rKtvcsM{OegIYu(1{;_l>>C*2jJ)c`T78i9UxyHpc6j;n+M3{2jKPqo%jKmK0uy70PhFL^9NAD0lMu2XyO2Q'
    '{s0R3jBfigvi@hp?PtX8XLQ@2Q3F1s+y0D-@EH~1Gb+Mo#PnxWgwKfZ&*-*4qdt5_efSJ+KZDKBh>p*Qj=$5>{+%xN@AR#Ir&s(t'
    'z2e{L75`4(`geNoztbHStng^@lciSSXW_|$mG}^*HNt0>tSGiJUFF~DD*sN;{=XUj^11)b_?M6VH{)ME|GydkqFVo(@h@NbzZw6+'
    '&&vMgEB-g*Uu9yY{>4_wztl?o3s%{`@R?=*Vyom|*@}CxtX25U&*ATLdi~E~^K&}?&*AoSxcwY%KZo1T;r4Sn|Igv}bJ+YGHa~~I'
    '&*ASMF!qm(N3oUR?;jbD606MSKVb78u=x+z{0D6QBjZuoO4$4d{QU#|{sCkEfU$qV%0J=ZpCJEFkpCyh|C15eKN*4j6CVBv5C4RR'
    'f5O8*;o+a~@Gp@67g+xbbpHjq{{r2AWu7{p|5xUz!*6D>{ufyP3#|VI*8c+Qe}VNE<nk}b<zG<Wzo5Q<L4E&%4E+T;`3t(PFX+0y'
    'D9`T}^4S;kU|-O6eL>gt1>?;x$mL&<%fFz)enH**f=c-X_3sO6z!%hjFX@oJq(k}=%)SJ(FTw0fdZI7siN2&K`m&5t;bXs~L;8}Q'
    '=u3K{FByw|2})nm&3p-FU((HdNyqXfcz#J&@+IhgNmueESbs_9@g>NAMX&J{`uqxgenofj75&6l^b=pvPke=1zoMV`3hjPH2k{jh'
    '#8-?kzXIK_!1F7#^c7nAI_%gjd`uKJ@J7K3E`|3@=5w)Ca4BqY$ya<05?_PF*YxFIqrtDy;MZvIYa;Gz=6k+o4D>be_jNk25q5m$'
    'OI9-9^EI9L*Yw_BGa~w$-ur71{2BzmricC-4St>Oe28)hX4$U!YZUo48vL4Z|JQWJU!%yc)4fLFa-@885XKU#?h%C%Z9cKe{3TZS'
    'S*Xkh$r=aA8VBL;Ap9MKzk~31kQ{Q5%y5u7tAmWB4w5Ghmf0+P%t7X?4#MU^##IO5_8{Y`gK&G0an(VXK1e1y2=52UL<bpH9Yhlc'
    '$x;VV$icEgqI}khIm(W?4x*leWVeH8=^)wdAj&$3vJNu0c98MdK~#5;tauO&9xQ7x%4e;D2ERd(-=M*7$RXd5L%t!06s$V6<G(B9'
    'sa$Nue^+Qc!rx`|`3?H~27P{mKEENqe3L3N><O+cSxL6}hHUc<+2$Lv%{M6W8#MS0`Q;ll_zkN22AzGA?kFfcS?qgOS>K?gZ&1%S'
    '=;a#}@(r5!22Fee@87`mH*k9hZV!=d4#D&xvdtl~%^|YQA(&3A@OR<l#37hI1k;CL`VdSXA`=}V6CEn^Uij5R<fTL8r9<SUL*%7H'
    '@P3F)bO;q3A`=~oPl6;!R3=tQ6Nku4!8#&UYx0{%r234lctc8MykFx`y1yVFJAVje9U`9{LT87_XNStFi@zbO!9(P_Ln!hPx$Y49'
    'JVdTLgjx@g>kgsaL*%+cDESb%?hv{@gsu;f>kg6Y4x#x&<hnydz#($oA>!fR%yj>ox$S>5oBeNQv;SS{`HEI~w*KGD*8iKC?te4W'
    '{cmQv|6RQQIvlSmS;@TjznS;`zsytDs{FsqQ`gG>U*@T6<^C`8)Rh(gmwD>MDn50s=>IZL9saKT)U|5;U*@U9-<6*_wbG}~m#pyA'
    '1qP$+szPj)ur64cRfX6pAs?*rszPj)cqmyh@<l63t?U{@Y?Y8NSQ+GlRYpFxO2`+j1o^}&BA?566bAHJ9&#Cv!q7j<N-pD3ttb~|'
    'Im$&@j&f0!qg=+LTD5XfmX%zTWhED7S;<9NR&r66l|qzfYCy2cSwFT)^}S$a>U*%t^}S$avVLrp>U$Jrvwjq1vwjq1vwq2nvwjpM'
    'c|J@bg-^*=``9W~`(Typdtw#qdu)~JdlY5!e6Y%yJ+?~qy<lZ>c@$-{aIngGw_qKfK4<KEHq!>HoLdvCm`!7=ls^krCSxX6F-OK$'
    'DJur6oa+*+nB8Kll+U85PJBwN@FelG)QL|c7OVnhd3aB(V(rhPg2XD;{(O|J{rM<c`}3$Ev5K`nj|%drAdd?2s32J7+Mh3LBE)f&'
    '?F8~swiC!l+1j6vvb8@SWov&PO(a&a_UBPZVijwDKFZeqJbFp2V(kxBx%L;VOtsIWtc(>UR#|5mEBRSbb@69rHJFdGwLgy{^HH|;'
    '=h0_A%GUloYRyO4+Mh?e`6yfa^C&qVWov&PUFV~0?a!m~e3Y&4c{HDovh_Vr1mvS^ea{mQdEz0l>K>7=6;3TzQjaRBK$X;-N@`9e'
    'H78i*+Fu!EYkwsbsFDg)nda*tq+H2L>QN>2sFDg)85L)L;sq8eP%UasEvif{s!T1aOsy!}3Dk<Roj@&WPAzIqt&9)(l9g1TT2!D~'
    'nWwI-IE=pFFnBnOzThxeIgGyGFgQ94jt+yP!{`eRgO$Tz<uF(|3|0<<mBV1=FjzU9F5z%EI-D-ya2PwBF5z(aI~@KFhrh$=5)Oy4'
    '!(r@j7&{!s4u`SBVXQVB)rOVY@K75bYQsZqVx=~*Qn2D1iDKy#elyEa?bL^GNkFcmHjLGVvD$D{8;)wjQNcPQ<eu=EQN<B(bOfv%'
    '0S`yO!x8Xs1aWi(adbq+zwnz`j*iIqm#;Vi#*TooBjD%=I65NZQDsFPVyq7Q)gi{}z-Ap{tPb4Pf!jK8TL=E?5OH;2vkq+5fz3Lw'
    'SqC=jz-ArTtOJ{MiNCsVTbKB&3)6Lpzq;^V7vAf_dtJD#OElJn>AEmo7pCjNbX}OP3)6LB`bfI;Bk9tQqz5~a9_&bZup{Zgj*POa'
    'Y_V0RcHDbMB`aBTORT!d?Uk`r?%9u|OFxn>{YZMSBk8)1q%S{`KC58W$)z1<{F`-h>9`~OX123Bl3uD{9iI9S|6Ot(sPHI-PUlE^'
    'q9f^oj-<Cal5XZm`j;c=SdOGeIWo$w*#xV+W>b&;x*q*?J@~5!fA!$69{km#hprc8R|D&n*(~(Q^`h+BV7)S%g|4|C-F7|t>w5Ip'
    '^<c9e9d$jptw%>)4{qzxL)U}p#7f2%!OAjSj~==nyw{_Lu2)t;6n{!a6ZOiPD7aJ)h18>mu7_Ug(L>imJ@x35>!GE3^vU&5Rz3RU'
    'dg!bkeR4fiSC2lq9vZAqo~TcrsE^L-qqF+xtUfxcpDHUf^ZAPUWR3b{jr!z?`s9iF<ca#^iTWt3K3b|zo~VzO>Z6|e<ca#Ir#^bA'
    'A0?*<3mz55IrULUeKb)Y71W3K`Y>G|ZtKHlefX>YAB@$ho%oPEOP$(@4*}~2WQ_)7jRvsU05%)IW&_x4K-Oqb<~A3;FPlRekV6`f'
    'H5!mL8jv*_kTn{>Z3D7K1DI|=)@T6J4agb|;JpD^qXE1(AZs*01r5j=4a%A*c-R1iG$5liKrao*C=F0g12RejwA6r%(g0;OAfq%u'
    'XAQ_G4NzSJGD-t9*no`E07W(+qclLD4bW#|1+2qeTmKbhcgFo!l-&#WUr~1V+kZvbJy<0x-h=gDQFgyu!HW0ug(IkCE7`pmTcv$g'
    '{}pBTS!Jv!wlce}z7=KnyL~Il?r{57l-<+ztth+e>RVBE*VVV8>@K!%WuCKaCA$#66=io;eJjfDtjbtXY-RRYeH%Q#9cA~leH(PY'
    '9c6d8eH*O54c6ZV>u-bgx1;Qywr_*{w^JX&j+e5PApdQU|29~E2duvnWp}uJ2jssKW%s*%2Ohoy58r`@@4&-%qU;X0@4(7;GCq{8'
    'gq82W%6H)5yCDBvu>LOSeiwAV8)f$oemBbQAN(#@e;0JW3%cJ0-S2|#_rUXeAox8n`yQBmFUsx_{9csZBltZK{2rKn56r#?X5Ry|'
    'qv$-2qVqV4>U0#<=_snxQFIqaF$y_~?xJWV`v8xk*Eovq;wUP@QPhB=$k#`ag^wb)9z`}iiX3?qo&QmE{zp^8kEVtn4K7E6%hBL+'
    'G*$a(>h#fc_eWEwkB+kY0FS0>A5EP;8kCNvZXOM0M^iVCrv4obo<~#Tjt1SMsbfcj_0iO^qe1>?YSq#3&=3taM1u|Kml}e6Ly&I>'
    '@(t;J8`AGKM3D_y*=mR)8`AwYM4t`mkQ&kxHKhA(NKe#|E~p{hZ$sE@2!9RfZ5q<eG=#r~tUolQe`yGt4e3!D!e&GGYe?tO@IUy='
    '&g3^_Wvd~5NJIMMM#NYnVyqFoH-h&@@ZJdC8xe7h=#v}K88;&08nKquh=^-MpWKM}YlI3K(I+=T6OHJT8?j#12!%AFYi`7PRU_7`'
    '8lj~|bkvQ|QX?`$Bb3#M%+QFAx)G{tL`U5S4K^a9G(wS$SRZSIJ{!?(H$ttA$V83MZX>$wMku)vS*j7bZbX)9gvuMyZ8t*mjmTh)'
    'h=4{!KqJ<&8W91F=)}JtrDw0gg_xD!FZE!B0w1j8d{sOl`TbH47N#J-UyP2>w?^MD^<W|0e81FB)GB0@k`+(Xe!mzU72(?1??>qw'
    's_^Z#zF+Fk3f~^Ac>OkRjKgonYqZI{aM4QUg})#7Znf*imvh$oeyNj-l255q2*3g^QAK5H)s64tOn(-CW<hiXD>xKBGZ#Nu(F)Ib'
    '3@9A~O2>fGF`#q|C>;Yz$AHo?pmYo<9Ro_ofYLFbRI~~{6iU}IpmYo<9Ro_ofYLFbbPOmR11>*^viJA=Aj;m~^MfdRf6ou1?EO7I'
    'h_d(h{2<ESuJeOpt_$CuT5-fxL?tV^E$jzT_O`GeMA_S)eh_7EfBHd`y}#}UQTE2jA4J(3doospRav%@8zX-ZW$%bQHp<>>bS$_W'
    '3ogfk%dy~cEVvvCF2{mP(MoPnI~H7y1(#!^>>XLhg3_^|bZnHp^Y2(NJ2uMRxp^!I9t(oUg5a?rcq|AW8)fg@JQh5Ui?X*y9S5Gr'
    'f#-4Hc^r5i2cE}8*&CjY1Ks05_c&B{9Oxbgy2nM?`^b(1-Qz&_xF~ze*m0nH90(o<g2#d2@lp0}t>Z!Icr<uCm>myh$Aj7NV0Jv1'
    '9Uo=y$T}Vbj|aiyLGXC=c{~Un4}!->+56p&2hZct?(v{|Jm?-DWp8vl9;}Z?*T;kW@gRRZ$R7{#Cq&sB&rSgO6Ttceus#8-PXOx^'
    '!1{zJdso>BV0{8up8(b;pw<(>`UJ2(0dG&hzZ0YE{cb1X?TM)FM0`IH)tv|uCxXO@AaNo{oCp#pM%g>uP6U?|QRIoBbRsC72udfS'
    '$P+>7L{K^rluiVtlkoi{ygdnTPr}=i@b)CUJ*hY<$cJ+<CzVG91vXE@zmxFqB>X!G6`X`eClOUA5l1HxM<)?ECxOICM8`?saxw}z'
    '8I(>&At!^`$zXOen4Jt}Cxh9^V0JQ^I2p`N2D6jF>|{_nnM`ytn4L@}IvE5{2EmibL??si$>4c1c%BTNrx1UqfafV7cnS!f0)nT2'
    ';3*(@3Q=_mc%Fg=PXW(U!1EOFJOvG&0=lQ*`zd&PD!J!Wd_NUsoeC1CqO4QF<y3Gv6<kgQms7#zRC3R$pmZuIor>yC1*KC#=~PfU'
    '6<kgQms7#zG>|wA-%rEa)A05*ygdzXPs7{OQg8F|8&FP5z0Jot@-%!u4c|{gA*bQ(X?S}Ynm7&LPs8`q@cnc&aXLtxjwVhAm($V2'
    '>7aBvD4h;Ur-RbzpmaJYosL3I2c^?N>2z>89b8TaiPJ&ibddOAl)XLnhnab)T;&fl^HNb_r5;83A7(sC{;udzu(CJA{xF?wikAvX'
    'R&rnL57XJ7Ts(8~!*up17td1tFrCxM#VZaOE5fQQTglDGKTI=i{7TVU87so7ELuT5;Rb<>6=78-R^UB;p=o8tim)n+R;tLX6=7AT'
    'R(SVKI02B)SP@obY-R3p{$Z58%lU`pnW5y#O0z~-l|?I_CrX~IG>3#$nOdn{;%_fi60G>ik~N0#R{{B=Rhe4xn|I<p_+=|h1)qWH'
    '&WN&i7M~Gi?<_te%HCOAvf?|7&xo?O6rX|W&Omi%pt>`n>@CG-puyNG-LQQIij1w&4aR4nx-;PD3^+OiT+RTA#!>cm<HqEk#^j#H'
    '<etXlp2p;!#^j#H<etXlp2ku3&f><@oW|6g#zj2C-tUr?++f_8Ow_oDXFg11Hjc7)aW^jFnUCVX%ieC>ILhA4-I#u<G5u0w`lZJ7'
    'ON}#86?`v86;@^0N;<2?QT7h+#`IZ@>9ZO~**m-&lUp0pbu}i_HqOLK_`Y&<<SLs)*&Dr^5FJg($xX<~O~}bj$jMELtE;tg$!BIV'
    'bdxB1qjwV`rwNhMgve<^JTxIgHz6lCAqzJl?=~UtHX+kCA=5S?w>BZSHX)lfA)7WKe>NdUHX$oEAuBc^4>lnWHX-vhA@emM!h;pR'
    'Z869*SGFpPRw*ksAs3v93eH3YXObh&BuAb}jy#hbd1jQo*ZoW~=9#GAOjK|tDmW7roJsyX6HS~+jyw}w&IE}w@x5u3y$`-A{aI7`'
    'v!-Osrew^fWXz^y%%)__rew^fWXz^y%%)__rcw4j_@;DgP3hK}l3SaSTbq(wo040bl3SaSTbq(Uo0319lKGmF>zb0Knv$2Al9!s2'
    'm(F7C`YhJ2&teVpEY>j3Vh!^w)-cavH^o`3U7y9?inCbBK8v;MvshCMR`4QTiwss~-S8~dpo4XI{F~uri)XQlcvdD$r9VsaQZBZN'
    'nJ9ciIrroeE5$l^n_Yc8i&ez4ST{V2RlT!V$2*IayR$MJh0o0H>^O^^9nDyEZpNx}GZ<?IW6fZ!8H_b!)wvn_JeslU+>Bix%~*qO'
    '#;S8O_-n?Ra5LCUtaN2LSQ&1cu_oLMZWAl~U3e#CGnj71dU3PN7$N=5k_wt-Mg_U7Rhd}DaX@&otU{V)I{#eOs!Xl4D+yR<)zb|1'
    'G-K_$8SB%{P*yY6r<<X(W~?PQLv_tqOKye+o3WPM3`I6Wk<Bt$qoP)GvPN^VMsqaS91S){gU!)kb9THmCx<jAhcqW^G$(5`M|I87'
    'S#y-toUG9tWi`)qI{A{7FxDLPG)FJZQAl$%(Hs>tM+ME<rO+JSo5OT-xNQ!b&Ec;({55A4zd8F@f|d9lylp{#X+eHz0k<vSwgud_'
    'fZG=2mlo`5X+gGWLAGf@erZ8|X#vwM$S*D6y#@KD1uAGkerbUUT998_WacOGS*x;aC2Y1J_p~7Qv_L&A$UQC4QVViV3zXG@+|vS`'
    'wIKJjKy@upT?=wg3--;lK#?uTOD)i63-VG6)Y^i))B^3cATPB*$t}oBEzorfblrly)B=^aV6RGx|4@0I+6lKI{C~tQ=O3}J`A6)$'
    '{SiBFf5hJ9AF*rvN9?ZsQIUsSc<LXq*Y-#3A^#COZ+{fkN#67tPpSqhetUC#6#qv>Bm(b+XNjd-J8rLYKW5MKkJ;t?V|MKRm>s)6'
    'W+(HH*<b!+cIEy!<5BpO>>k}8v)lZ~?AZNr#-s3LWsky>l|2g2QuZjH`w1NVgx%3Ufw7;!*iT^WCouLC_Cx;!#(n~0KY_8Iz|l|O'
    'D7K0_u4Ajr*iT^WComRU@w0@zVrRqO+3dJJ8#d2|&9h<iY}h=TJ=SN#=Gm}$Hf){^e`mwr*%@yWtIX!vuz5CYo}KYFpF0OO&w;;l'
    ';O`vvx}U>d_j6$L9N0VuHqU|0b71ov_&W#2&MA&>LmJGVQ_MZ_MGoh{-%nxer*QOBIQl7j<bTQ@`JckrPhsq*F!oaz`zeh56pnrh'
    'D?iP66u!OeQT($EN9WS>olDPmE}g)+bOPtn37kt`cP^vBbLs2OWvBhQbb04eZ_lM}o=Y`6m-=@u_3vD2)wxulbE!G!QghB_bapPI'
    'vzByEE$N<Gf>KLRY6(g$>6cp4A+=-#){+jXCHwAM(l50HvzGKIE$KsAf@e#5jh3L>l3t@FShoc0mh>7e=^0wWLreOCmax*2zMv%>'
    'wS=RV^aZWZZY#9gik`L=9JPX@R&dmc@k%R3D6LR(D|YC&LdmV@Vq4L-wxUyQ#dxI^ooXw((N-|sijK1t+_s{tYz4QiV6zo$wxT<1'
    'ML*aIHe0b*x)mK@E4Xb1o2}T9+=@N<tzfzpJzpzEHm&ISs))@hVzUYrRH1?@R8WNqs)*DoMmAN9WvYnOD)#GF5vf(|t*=5MRg810'
    '*jrzPda4-pRI%^A3T0I>2C70?Rg8hE7z0(Ix++vxMSiJb3{-_8tH?c7=(CD3P!(#eA}>{;-74}@6-ur`$yMZ~D#k!nsJx0XP!*c5'
    'BA-<e0actGs3IP!7#~#;9aZGPDq^LIJXl5KR1rB<?B%Z_a;nIYRm4#hW2dVBh@<S-={$C@pT`dN^Vq?D9y{32V+Z?r>|j5S9qi|^'
    'OZ`0d@}I{p_4C-JejdBj&tsSRdF)a@k6r5L#T{<CV?KXgso%}V9)%<v|19>X*ze|JkBXgDKK3DmQFxZX^?9Z4H|+WkR`M)`DxO;5'
    'S@IR>&*En(kP@uSxq`Bl#|kK&4-e<V!};)VK0KTc59h<f`S5T)Je<#If%D<ve0Vq?9?pk{^WouqcsL&(&WDHd;o*FEI3FI)hllgw'
    ';e2>FA0Ez!hx0-He2{O=I$mp5b6c~T+nUwf)~x2XX8pExxsnw6yw<GTwPxk6HEXo3*+tWu72DSAXK2m(ZEJSXv}QH8HLJO;*+tWu'
    'wcXaN?Y3qYO>0(qTeH&Jnq4%lS@&(tx^HWC(X?h2xHUU8TC*nHntd~^Ss`xC3UO=p&9r8{xHap=t=Tuzn$_dhtRA;!m9#Z0#I0E+'
    '{TW*N8Ee8nV@>#HtO@^&HQ}GJ3j8y)^fR>dGqm(G)_s45UVa9;Kf|M+;ll;2(O$r+>;<gKUcjpC1+2<mz^d#8MIYk*ZWpjm?gDlb'
    'Uck!h1+2VYz*_4C>^ZrBT_zW>)_MWEOfF#M^#XR8T)<9}3s{xCfW0FZuts|UYqS@zM%#w<@HVW6w*l)mtcSM&`8FWm2ISj-d>fE&'
    '1M+QH^KQeMcN>sz1M+P^z70Ep+OQL-4Xm_bCr}$WY6C}Y;HV88wSl8H>;!7VPM|jM*9QLDz+W5qYXg66;IA!=wS}>^FxD2v+QL{{'
    '7;6h-ZDFh}jI||J+QL{{7;6h-ZDFh}9JPg`ws6!Ij@rUeTR3V9M{VJ#Ev&SKmA0_b7FOEAN?TZI3oGr|i_?z0+m0IEjvC&M8s3f?'
    '-i{qv?WpMO*o)JSoZOC_+>V^wj{4q?ir$VI-j1r>j;h^`I^B*s-HyuKj>_DQTHKCW+>Ywoj(XdU3fqnf+m4#rj+)wzD%y@J+K!sj'
    'jy+iI*m=~B3fqqAbRoQ72=5nCZ!e_YUP!&Yka~L|d$2B~`d$d{7sC66@O~k@Uq~&!5Z^Dv+Y9mUBKA^UM7Ftz{BjZb<s$OSMdX)@'
    '$S)VM3+f`W%|&FJi>S;Ok!>y_+gwDpxrnTB5qaVwqW>b|{UYN1BI5mG_MctM{<Dk0>|*Ne#bob`!SiCW_r;)lG3Z_lx)+1)#h`mJ'
    '`_C?B|JlVLe=*2kOl7{9Jby9BUkvgWgZ#xHe=*2k4DuI){KX)DG00y6)|Y_wC7^o==w1T4mw@gipnD1EUIMz8fbJ#Wc?o!40-l$k'
    '<V(Qw67akPJTC#yOThCI@Vo>(F9FX>!1EIDY)=MjPX=pG<!VpmYER{APvvS)<!VpmYM&}HnX7D1K5I`tYflDiPvvS)<!VpmYER{A'
    'PvvS)<!VpmYER{APvvS)<!VpmYER{APvvS)<!VpmYER{APvvS)<!VpmYESlVPvvS)E^kleYENdr6y7g|_e-f<mr}VdrE*<L<+_y0'
    'bt#qWQh2`<-Y<psOX2-eD%Yj>ektBwihq}p87?CiTt@U?M)Y4s^j}8wUq<v_R`e*|U3(elvM%HF+GS*h%g79ukr^(d#$84(xQtwI'
    '8M)vxa=~Tfg3HJSmyruDBNtpwRlA%_dpUSsPF1^{yn8uVUrye=9ON$t`O886a*)3q<Sz&L%c*gflant8`O886a?rgTbT0?p%R%>Y'
    '(7haVF9+SrLH7#qyaGJ00KqFj@Cp#T0tBxB!7D)U3J|;k1g`+WE70y0Ab14`UIBtvpxrCL^9u010z9t(&nv+53h=xFJg)%HpO<Ey'
    '!_vslOEb@f#FQ^tVc8@qT9u`r#aSxAR9Unt%T_!`9d2DOT9v7loSCeQXU~70o+S-0ji@YH$$jZRFU?<vRfV6YJ1uI3H&N93c{(dy'
    'vf`W7qxj~epQksg=i)`apQksg$8UBmSjAcCT<mReRyr5^m+Y;m6<^T)^K`DcWE~NzOh7FDyZA=-@O|;$9dUT<Lnxy^FV92A-qwxf'
    '8h#dhs2htSikp;R#m^ab$|P2J&Uok1mF4w-!gF3(UJocBe`R?+pzzdJmUsxyd1ZNZAQyhKxE>Hz2d)J9D?$EBkiQb-uPh-SRsgOn'
    'A)i`xLkNU9;)>`>c(^j=q45228om-%u7roOl`mQ)R?1dBu~LrmvA0>qt}HQ@$4Y;e;je7vi&lxvvXxJ*GPh+bU$m0%i?Pn~er3#i'
    '?K=5<f_zp5SH>zRU>1IsyAn-Y8Ec||SxCaERa8ia(uz@7Dd|Amb|7v$5VswO+YZES2jaE^aod5o?U1S`yg(*j(E%-WKuaA^PY2?*'
    '1995{y>vh!9f;cwrM0D8?0Z%{9neb$G|>SSbclJcoxBq(*8xp*Km{FQrh~U39y*|c4lvyTZactchyUO&8{r+x>wkqm?MS?LB;Gp`'
    '?;VNvj>LOM;=Ln`b%e2wFxC;qIuh?4iT94gdq?=|NW6E1&5rO_w(=#b$Yw`!K}WdlNG|9|F6apF9mxe9Q9(ykP`2_VtEh>N<cW?b'
    'q$7EvBYG)Y`I1#sPe*b{M{-C<l+}?O(h;3?B!_fFbsfne9noMXa!4m~NGEbgCvr$9vPLKJL??9C31xLE?F<NO(4Ej(Co)4PGD9bn'
    ')d?+iA~SSCS)I^QC)Cpkg>*s_ozO%lRL}|DJHd1(xb2kkm%Nvz6Kr;ZzfLgL=|4Ei=83D=CvX+}1g>JAz*X!MxQcxOSFumvD)wt!'
    '#Xf<n*b8tKdjYOuFTho-_g}?&|5dE_U&WgKRjlb>#hU(A<!H>spIMB*Tt2aqh|9&FS&Xs516);(s=@<YRpKG&^D6dhT*a<|tJpQr'
    'nVj62oZOk5+?kx*nVj62oZOk5+?iPEOssS!Ryq?aoyp0a$;q9`$(@Ou&gA6I#8GD=r!zUZGjY_JoZOkH>P$}VOiu1h#C0YocP9Qi'
    '6Mvn_$(@PD&gA6I#Aau5a%Up7Gda04aod@k+?gmYTltKY<m=8vcxUo;XX3px`MNXF-<f>fnOtx+(SJ43e>Ks6HPL@H(SJ43e>J;='
    't|t1gCi<@?`mZMXuO|AhCi<@?`mZMXuO|AhCi<@?`mZMXuO|AhCi<@?`mZMXuO{BFCf>Uc?_G%ZF2s8m;=K#;-i3JYQo=f*+lA=w'
    'LiBeb`nwSQU5NKC#CsRwy$ccEg(&Vq+;$;SyAY{eh}14bY8N843$fXSXzW7#bs^%q5My14sxCxT7ow^QQPqVw>O$oFg1OjVF#Gxo'
    'W?z57?CURzY{u{9{ROkHzbJAW@8A6e^R2&NrSKQr*6<7FTZ>jM-k|&oZfp1@PyNf{j=}g<dcQ2ay)JzFFN^0_;!P62#J^wS-!Jj#'
    'mw5C`eE20k{1P92i4VWThhO5uuZr)Y2%A<be^q?WFfEn;RXJ7)$*yF@FM$44IdY=#De2oM!l%^wRq@H<mxBMQxYiTDKKxh3wVwF>'
    'c)u#nn8hyzFIsWxiLH3l6TfKuSEX5wiumu6eZOIKrK0d;b>pp#6=9k$vBHzZ+j4)MjrZu+WgiOv{<`Qx`kR5hI?3h!B`bNBVAajl'
    'Nxwa|LfFRl`NvjxXLsyTVkNIr%m*v;-oRh;7SGrUpAx1+6RY&*?_Z~HPz?G=J|%1bP0;;y@I86Xg73dB#8LdSz;xxW%SgoD){Qr7'
    '#_I_A-@x>5VEQ*O{TrD64cz{w%xxi~{ie)qA>aI_%x%Hj-;}v6ME`Hf+!k`{Z_3=Jf0uF_|6P{bjFk^ovimf=GdG`Fb!&(B=~gCI'
    'k_U5%bwvCPwetDY3f~aU0Q@G+Zk1shcg1hg>{j?$W%%~2maaiP*PxzjP|r1}=Nj~KO{$mpZQ6-d(#tieUg8~?B`Z<SHK^wr)N>7b'
    'xdy#lgI=ydFTqNmC6`OA<l74^;WcRK8nko`TDlfot_7EC!R1<TxfWcm1($1ys%t^%T5!1*T&@L|Yl*6BLFrmhx)zkK1*L02=~{5P'
    '7F@0cm+QdgI&irTT&@F`>p<c<G;tl?UWd2WrQU{~A(vPsZ?DU|g*7T!iSO6p`*rw!9ll?OLaqae>p<c<khmTst_O+hLE?IlxE>^~'
    '$M@^;{d#=A9^S79iR<zGdVIeg->=8_>+$w_yuBW8f1Bw9Dk^_ld_zINKKI+wJ8r{>;kU&s9FGxx%SpQ5a+2=1nSLUQew*nha*37p'
    '6Ny#q8FKmGW_pJBSz;?HTgi%a`VGN~QY(G4LA=?$Xoc0Pd}^idw@9o|5rPi|D|=Gux10z1ZTXJ*f^`EZ-2g5(fXfZwas#;B01`KV'
    '#0?;E14!He5;uUv4Ips?zTbfFMJoy?+Y+mU#0?;E14!He5?y)Ab64K$+?984m#jGcx|Yr}hs@BGw>5Xo<kt9SrTkg6l8jPOvZDCi'
    '&0Tq~b64J^-Zc|PMJtJ;@OS0RP?76~N8RwK8*iiThJW4guN(e#!@q9$(2b|=##49Wsk`wu>TdYZ4Igggjd3?}ivC7U(HE_#WF;O|'
    '6zIK?GxbF)D*r5g(|AD!wTf1hTG@BY6|JDis9+`PDSTi-J>7|;?nF*^BBwi%)16r9PONk%R=N`_-HDa%#7cK!r908lo#-f9!Q1e&'
    'Y^-!AR=N`_J?L9|(6{!WZ|y<f+Jg~F54zYMj5~TT?&y(@mh$ma_h1y#gHcG2ble}NL!yF}?OS`$NA_S$auc=jCTinN)W)0Q+L)`8'
    'Jj+c~%9|LW+!RND?K+ilhjbHtR%{g>Ey)Ep(P!P1&Pc=q_S7oY+ndt)iORTc-bD3{t?-#~jNL@_y@?8Y6BYI*YU)kY)SIZOJ>k74'
    'y!V9np77oirh769>B%UhXPN2LDvwEeGA8L+X1bv3o-o~$5lT-+C_NdW^kjt6lMzZ!Mkqbgd7FIUXHl>+<CUI_S9+#1E`{H$3{RF-'
    'T`zRj3!U{sXT4BXFSOJPE%ic6z3A3@p{!mgs~5`Zg|d2~tX?Rq7s~2|vU;JcUi5Cg&{;2Z)(f5W2BqGh)Eks~gHmsN?~S*;@wPYK'
    '_Qu=Zc-xzvwl}`_#`oU%-W%V0<9ly>?~U($s3d*pTl>(T^`Xl2q0023%JiXc?L)WLhYHk(3e<-R)Q1YxhYHk(3e<<bwGZ{E54~F-'
    '>QNsmP#-E#pLAbk98{HkxRazWnDqsvzM#|>l=^~FUvTLQE`7nJFSzstm%iZA7hL*+L|>5TOP%fuE`7nJFSzstm%iZAkM5}--BUlh'
    'r+#!#{pg<h(LME}d+JB`)Q|3|AKg<wx~G2JUDS`;iu%!6_2<pJ{ke6hKerC`&-jp7MIWNd{@g*-KjTCCv($(5?@}Lvm3@bA|BMfn'
    '!OGlL)Svr_`e%HIY7Ic215o4u6gdDz4nTtg(BJ?xH~<X}K!XF&-~co@0M!jZbpz-Q2cW?LXm9`;9DoLIrf0aBp5bPChMVabidIzq'
    'S*dd@T2X3cyNjEPyFtTY{EC~4yFtT0B`cZtzL|ONo9RDqrpLUQ9`okntr=lMLGI?_JsIILt=KB}AvaU|Z>HlM2rdJ`Wgxf=1ebx}'
    'G7#SfmVGZkKd|h3ftG>H3lC&ocpx3wK)SAhbX^1SJ!9oltAs?x$|qJCmx1(W1L@BO(w_~aKO0DYHjw^oARXC2I<kTAFbL!af&3tl'
    '9|ZD)Kz<O49E2hV!O9>MIf#{*K`3$%iX4O@2cgJ8C~^?23<B#x|KWR9gM&e0Fh~priNPQ-7$gSc?O-%Gn6-()XmBtZ9E=7Bqrt&w'
    'a4_BuMuUU#eK0y3jLrt5v%%<WFghEI&IY5i!RTx-SPuc+A)q@1bccZM5YQch&W50~As{~loed%L4Jn@C2)E#stVCx+(Af}_H3Y1O'
    '5aC0Lw*ZA(PhzW#{E+`ZBC*16rdCOVMJqg6WyMfB|DkmLMJxG~p^O8HR`FA^qk^G~mWDD$7@E$>CAbV_g<~jl{zDl*3}wVHl)3Gp'
    'j0%P_Dj3SBAhwckFCaLSdHtb`7=|)p7|MuY7&;q<&W540Vd!iaIva+Th7rZXs3gP6S}H`qFrs)EQ9O*e9fp>M5x2uo)-Y<vFm#r&'
    '@`+Ve-7w;P7!f{<2p>jF4<m|)q1|C<cX+YKtPBngN3FwA>u}UM9JLNdt;134aP&DGeGW&F!%^gL6giwx>+n>c;i>Z_D^crk)})4`'
    '-Qj3=INBYKc88<g;b?a_+8vH|M=(b{f;s9D%u0`7R(eDR-P9`0QIE)=8?5Y%^$2F<M`X~=m8@hQWdw8EBbeJB!QA!;=C(&<aLMIH'
    'Fq=Ix<87_Vkr{7m<ws_`trd;Tcw3npiIzrYysfMliIzrYyscGhB$;m{S{g~N8;O=iqNS1OWhA_hg1=GlH;OfeQJKg|tTMNw;C2+;'
    'j)L1!a61ZaN5SSO_!|X(qu_5;COUE@D`9gKD;1;Qb`;!>hTG9_J350zWyNT6$Y^*U4ez7jeKfp}hWF9%J{qP+!|iCe9ZhB!4b!7x'
    'dJI)&3{_?fRb~uTW(-wk4BgBax|uOlpfPkaW9Vka(6Nju?gI?>S(U7$PaZ=zGlmK@hMF^mN-`#WCvqS<{484$#?Zfv1(&hlG8SCM'
    'g3DNN8H?{@slH>WzGJDdW6Qp$KPz|5W2wGl@qH}ScPvPZrTUHqm$6jXv7nT(;=e0)+u<+A(tD3BRpzkZIhHy-wp6EcxvW(ywUWL('
    ')S$6+>0?V3J?ya_OMM?(>e<6=?^rtcv8CD{G(VP3U@W|kgXwWFJr1VF!Spzo9!CU>BLc>uf^kH^I3i#i{rouMVI1)=uCy;Um;Pos'
    '9>$@Gaj0M%UDr5NFb>|wrEd%mN(#SOH=b+`R%K#^xuEdwyu$a1XSTB%M^uetR4|@CYdn3{cyi=;`mFKf$no@9<I~!h;4+>{Ii4PD'
    'JlS+SJ=l11>v(eOczUVv^ish}zrBFjcsi@`<lXUfR^y8^Z85szi!*I8y5s4(#?y6;r|YUl$<-*i8YNew<Z6^$jasY8S=HpMYDNsz'
    'WUy*7San&g>2H=ZST$;`CWBR@-D)yeHA=2#{7{XqtI2NFsJxo&R*mK}R{WXS>{d;7t0uculijMxVAW)>YO+){S*n_dt0u;(iLnWE'
    '9utVF2}IQdqG|$BHG!y_KvYd2swNOe6NsY;#L)!eXhIrC@zt&+D~YNJjBF;*zf52(GlBS<K>ST0{w5HA6NtYF#NUL{&G@+(!E7{6'
    'AQ~qSjT4B*2}I*WdgzJt&=cvCC(<WRq)(nmpFEL1c_MxC#0*EdiiwPfCelMsq=%kJ4?U3{dSV98Ty7$L@<jUNi5bkI#7Z%XDkjlG'
    'PojsOM4vo~K6w&qokX8J3AIk5Po9KYCs6|?q1H+0a}tW2gq9|uo=GTV5(=3N?~~zuGGnL7jGZQ<iOFbUGMbo-CMKha$!KCSnwX3V'
    'CZmGMs9<s?QgbCM(ZpoNRg)P>O-3)1(aU7?GC31*;WM-9nT&d-pq?qHX9^>*DdfQ^C~FGJnu4;XpsXn<YYNJmg0iNdr737>3b}3y'
    '%9=uUn}W`!ptC9Dr75Ux3aYEY_Zn(I4K<(!-)pD=HTYhz!XewVPS;QoYCxifickYCHB^L}6s6=2jT$hk0kaw^LJgSJP!VdV2sKoM'
    '8qlqwBGiC&4HcmV<ZD2_=0A{6&T}O-yoUNvLw%^BK1?M~OeIfDB~MHxPfR6GOeIfDB~MHxPfR6GOwDi`tZdepO4gW4)|g7xn3`cT'
    'SF(~EGL;-Mm8>z9tTC0WF_o+_m8>z9tTC0WF_o+_HN#3&F^wEDjT|zK95RhKnnn(pMh=-q98DvKOe2n_5l7R=DAS0eX++L6Vr3e!'
    'GL2Z7Ms!R=^V3lIG;}=;T~9;T)6n%Tj4f_qY;g-?i(435+`_o{7RDC0FuuJd-6I$egk!5b-*XG&+gs8-g7KiBWF>n;Zz;ZcDqPfC'
    '_=fB_AhwckNUii!3jf?fe|-z1*6H{@9p9(p`*eJtj<?epA5AZNn_A@=p6QH_rkA}f#MpH9M^4Av>3BPxQO|UI&sgct%1C6ae6X_f'
    'J=2-*na+r4IwPX#jEJT)BAU*8&vfQ{rZZZa&S+_RX|HC;2GiNOIi0zn>C6R9XOuOaQP%X*uFjArrnAR$I-0l@72JvnZbb#RqJmqA'
    'fLqbTtwg}BM8K`=j=q(6xRrRgl?b>MP27qmZbb#R{)c~A&Cj5Nm_Y|IgPvhVx^p^t>KW{#o<YwrgWaw(=*wrY+jRzeJZF&kVyjNk'
    'zZvZKoI#&8gB_nU=n`hcT|)fS1tezBGt3C*r^7ddi@7UjP|;^l(PvQ6XQGgqC}buInTbMXqKTR0iJ9byne3yUN!FN2)|g42n29E4'
    'qKTR0iJ2&5CV65e(La-TpGkzzB&KH)#WRW9nMCSLVsj?ZI1{zbLZ7qH=PdL&3w_Q)k+V?bEEG8_Rb<ll%tD{D=yzwK)>)`^7HXY^'
    'T4$lwS*UduYMq5zXQ9?vaZejRXCZsfqQjkql4qghStxlHN}dh6vq5(@=*|Y+*`PZc1ZRWUY%rS*X0yR;Hki!@v)L(TNmn@=1ZOjT'
    'm<^t@!E-iv&IZrf;5i#SXM^W#@SF{vx3OdQHg@dZ#*W?F*rR(JdvtGOSMF`>!@Z4nh~CCN+}qfPJBOXObJ%%1hn=@`*lRn7y|#1M'
    'T|0;Uv~zg-=N$Ia&S5|8Tr%cdGUi+|=3Fx7Tx#lE^5<M?>Rf8-T-H$LQd8$rQ|HoS&Lw}&C4bH(W6ouEc`lvRTr${P>g_y`m<JN`'
    'Kw=(9%)|G2)Q)-7j(N<;&!cwCqjt=r<D7@@^YDEhwPPMg%%gV91DAQsy3YfpdGw$2=s)LCf#%VF&Z8d9qyL;ob(%;2IgeU3kN$HW'
    'm1`b7<~%CbJbKJ|)UkQ+J|Cv%!}NTZo)6RW(foXPpO5C}qxt!0em?7l^U?f#G(R8S=fnGan4S-}^I1cg54ZDK)0odH;{5+WDH|ON'
    's7DK^M+>M&3#dm6s7DLZYM+m1Ko&6aUO??%K;>FM<yt_kT0pH@Ky_L`%~?RrSwPKM5Rcg7Co3ShfbshR>d^w~(E`Tr3mCsIpjIuQ'
    'RxO}bEudB{M4t=M=R)+k5PdF0kqgO03&}(a$wUiT8(c^xT1X~Zh$0uF$c1F0h3Io3nP?$uT}UQch;|pU{<jb%FC<GXBoi$p6D=eY'
    'EhG~yB-<<`+bkrbEF_~WB#ssmIg5yuMa0S?Vr3DrvWQq&M64{LPhLc<EFxAG5i5)6@)i*}i-?>>ba{)2qeaBgBI0NfakPjyT14b5'
    'B61cH9gB#LMMTFUqGK`WE(YDjpt~4!7lZC%&|OR>S`40x!E-SPE(XEHDT48}cNL47A6yKci|Lvd(<d(m>&0Nb7_1kA^<r|?Vvt`9'
    '@{5^)TucUAOa@yFM~mTTF&r(1qa|>(1df)#(GoaX0!K^WXbG$=ft4kwd<h&afukjGv;@sBfukjGv;>Zpz|j&oS^`H);Ajb~EP<6J'
    'V7&yamw@#WuwDw*OTl_6STAK3d@0B;1^J~Qzm(`$3J*)+VQI=kd<|r36=%<v!pc%uSqdvliJYbIuoNDa!oyN{SPBnI;bAGUvJ_U9'
    '!pc%&Wht?;lvr8HZ2eN$Tnd{@VRI>LE`!Zwu(=F2m&I(x6``Q{WpKL;ZkNIBGPqp^oByAy`;N1!y50uP+%ppuvBZ!fB26$xYGTya'
    '7<=p$QKX8di0IGw+H35JqQ=+}h7L12GYmK|jb4Xg=;RlpzQ(B0#2Oo7Mc#YPz31Nj_0RRWQ|^A&^E_+qefHUV0@<8EHYcF531o8u'
    '*_=Q&Cy>7h<ZlA`n?U|1kiQA!Zvq*cK*lD3`~;An0P+(+eq#DYcyinC#PnU~<hI|5#f~hKM8SQ@6S*&WVzFDx<f42wv)^=LF`L=H'
    'Gm*1TC#G+9$N#--V)_Pi{NHm?uCL1^QE*D?M9xT_$SJ84xl4H>cPURSc5=DD8Jwp&k@Hk1a-QnMd?!~LKQ}CynD4>juB0Rzr6+Kf'
    'B%>{y$C-<Q(~T!`zUjnbR+67A%saB5m6MfnvQkb~%E?MOSt%zg<z%Ittdx_La<WoRR?5jrIaw*^?Amg&QchON$x1m{DJLuCWTl*}'
    'l#`WmkS_=8a<DE3>q(sPIf?tgCUGCwB<=&7RCs?ne)c+v`@kj@P9}|??oQ%V&q<u>If<K~CUM5+r1%`q+-FG?-VQd2`@kk~1K1?)'
    '{F=lqUz51kYZ5nkP2%pZN!->oi95I^aVyni5S+}}r;|DRbTVhVPUa-k$()2bnX_FdgWzNkoD71KL2xpsq)rCU$()ipnGsE4L{kdq'
    'U9`)}YD(c;hxmI>DZEo3zg0g4_Dq32Q{c-K_%em@O<{af7~d4eH-!;Rfgw|1$P^ed1%^z4AyeSQ6gV*j7EA%NsbDshvvQ|$R_;{J'
    '%AE>droxx0Fk~tWnF?l8!E7p+O$D>5aAGP5PK6Uw8Q(NkB&M+<F^v_8X{?w{V^wS#YroT22b;z^*fgH5PGb#X8tV+xSRt5}i4&IZ'
    'E~07a7~;`pzgcb-Ad{@IOv}&a<8Ck>LvB^9B)PI`8gu(;tcpzsiRmCQ9VDi+{xY4l-|4KlOlQSqI!_U&Gxq6>eL8C_(?Mc7YbDdc'
    'WjeS_XSKH&MMPzVC|z+WMiEh28Wpgf&T33CiipbcQE`>H7)3;7g(zLcDMk@dSsE2~FchPRs4N!+Yt6+dA}T9H={iv{iipb6sIb?e'
    '7)3;7Nfa`2Ivkt<>t?{Z8L(~!`kR6NX0W?q25Ovv8fT!t8E|k09Gn5OX27f&uwVw`n}OnHd}p+w;$|{Gn#ufVCiA12%z<XID`F<A'
    'X){?(o5^$Lnap}-GV7VitY;=`2{Tzsn8|a|nap!$7EwyZkiYdVL1Jcns(jq%#dDcxW)ZVw?BP6TCNrB^Fk}`CnFT{;;Y+jF-7pK6'
    'nuSZv!k1>jiCJ)B7QQqKhRlK?vv8YPxXmp5WfuN23uev2QD)&Nv+$5vc*rbVV-~J43!j*UPt3v@X5kF8@Pb)*!7S823-!-J9kb9w'
    '1q!G@0Tn2q0tHmS`3g8+!74xn3aCH<6)2zr1yrDb3KUR*0xD2I1+)1I^iY8wD$qj(dZ<7T73iT7%qqdG63i;WtP)%*L81~QDnX(W'
    'Bq~9olJ$^EaH#~BN^q$Jmr8J{1eZ#1sRWlwaCw$}5YMs?;#u}VJj*_aXW0kwEIS{bW#_}Q?0k4ORe!u=BJ*rIq8Q!m-^{Bx*`e_q'
    'yCR-rSHyGdig=D)5znzJ;yLy~JjXtW=hz4FT=31}|5yBG@!u?dv#6vBZ>_>xtMJw;s&5t5w~A-NRaD<9s&5s&a1~Blh0|8?T&;=@'
    'unOO;!gs6i&nmp9ippGt6ID@}tHGrjT&lsPnwnG1v&d>{PBk^Bn$EZyB&tE8nwnD$F4a75tOliO`s8Xbs|K@b`s8XVS2dNZnm)Oj'
    'I#x{`t0oWC^vTs!wQ8zbHGOh5HLjW(S52Q>O~tFG;#JfAR#W4usd3eGztvQ{YARke%&LY<HL#}!_SC?h8dOz-s%lVG4LdDrP*n}8'
    's)0*2aH$6N)bM<|2KLmzmm2s|LvCw8qK0S5H7Krz9U3*?!7S9@Y--$WYTRsU+-z#xY@P?q=2_2dx`f$O!`alo+0?(;RJ_?#wb`uX'
    '&*n+YY%1PtD&B0Kz09Wm&E`qWY^vdGs^M&^;cTj5EgY<cgSBw576+@v!D`t}QHz7s;$XF~t`^qS;$XFKuoefag^{)Fn5c!HwYXa?'
    'Y^{Z@wRl!7o>hxy)xzsqJgXMZs>QQvaiUtBs1_%x#b0Xims<R#7FE@vs#=sY2d&IOD|67w9JDeAt<0gLo`Y8App`jvj&o4X9F#MM'
    '&T$SpnuCt!prbh`XAa7lgI4CCjyb4f4(gbLI_84eTrispW^=)8E||^5U*>|+TyU8SE^~RNIF~2Hb3th?{q<Zhn+s-h@t(OLIG5+X'
    'bHQ^iPBa&E=i)?j!Fn!O&jstbVEsH;KM&T=gZ1-Z{XAGd54z98!RNvHd9Z#Ste=OG&x7^zVEsH;KM&T=gYNU-`8)_d4`$DU+4Erb'
    'JebviSsj?wfmt2T%IiR|4g~99YaMvj@pQb7y$*GtTL-#zpj!u%>%g-PJnO)-4(`^0ZXMjM1M51tTL<!WaJP>A40U9sj;z#?l{&IA'
    'kF3liEAz<8JoYopBS-Vd(L8cAkF3liEA!y|JhC#6tjr@T^T@+I@-UA)%mev(U_B3X=Yiln5S#~s^FVNZ;YoJ<$Y_3{M~Rz_`P_G1'
    'h~k6Kqckebe-_@WKA$^1=NEdEn7i}2(RV(#U(e_E>-qUUq%?WnKR@4jB-Jn%<@W-VBvH)PxC<$X=I7ssjlX9S#lY;E>rvupm)zaI'
    'S)h_AcZYTo#jqr|{U%7H{YyznF3KTal8imqqr|6smzK;g^e8ds=W~bX{K7r2aUU|DJ4EMm`|f;h%8jFVgvokx_V;#A9x=xMFBk2S'
    'yBjwXf9u^7nBx4EWa^9i60&2cFLs<Ixu|$wYkjDdsGb{I>&a$4*{mm<^<=Z2`&#R{ueCnkahAmo5liaHZ9TcIC%5%^J;a@9yQrQ_'
    '*C)B%HLsj{GF_i!I=K<Hq+O<-yw{WIVicuOA@9W~%11>O)Q4(}qkt2|C`zLOLyA!pM7djL>tRnl>?uZ38WnD*t%q6lFsq(BXY091'
    'wjS2ihaOT^pKvhw$s}VTBkMzd$^O6HlLz9lM<zcRu(dv6YjQhnCeB01-TKgpN*fA0Y~nSt27IXjUuwXY8t|nCe5rxEh8y5@1H5j4'
    '$qo2Y1HRM%cN<`91N>~ji5lQ%1B`6Ii5e0{CU=r2NQ7){fS(O8vLU}R6yJjpl{CP}1~}LN&l(DMQ^)#ifOQQptAX3Z8{k<3Txx(X'
    '4RE3X7Bt{sjm3Rd*|9g`XN~w-BYxJ1pEcrVjj*5*7Bs?wMp)2@pEcrVjrdt3oM?m-jW}2%3~9u{8evEy4%P@?8evE=iV9K6mqy&J'
    '5%x6VZjErM5qE2ZS;Z(SL@Cc2alS@a*NF2q;(U!TvJplWqo@$2{A|P(8*#-(xZ4PK8@ZRe5hgd{n2k7QBP?&kF&lBrMikJ9V>aTL'
    'ji{p$$81C^jW}i#j@g7`HsP2}IA#-$*@QZp&_fgVu{WWPCOonUk8DB#O>n*mS8RgwO|ZNPS8RgwO|ZNPUN^zyCb-)KTbtl#6C7-U'
    'gH5omDbK99W62bv!tVt<Yl2x#g&W^v?`eWdP4J}&PBg)SCLFUF$85$in{mu$9J3k6Y{oI0;Y2f>XoeHbaH1K<Y{oI0am;2I(u_wo'
    '!<S|}vKhWK<B`p<ry0I9<B`p<rx}lIhD*(OWHZca#v_~ISu-Bl4C|Wl$Ywa$j7K)(k<IY48Gbh7k<GBR8INp+yTvF9qT>H6^12yb'
    'H{+kpu)G=nY=-m2C`zKxTbt2CGv3;aw>G1dX1ui-Z*4|L&3J1ws%pkt7qH)Z0sFldu-|(D`@I*i-+KZ3y%(^HdjWgv7qE+a0lT;t'
    'u#0;EySNvyi+cgPxEHXCdjY$+7qGW}K~WvaXbXBsMq5xoCKu&7pNy}-@@(Q46nUMc-GU;MGr1_w&vvExC}Bvu{AW2%B*=&R{EJaU'
    'l*2mQ^<Ru4q8#!Ch9tjNcm|gHEZDQYfIaIA@z#ZS>q5MBA>O(WZ(Uf(d%W*yAx^sxr(KBCF2rdU;;jqu)`fWMLfmvA{<#pxT!<?!'
    '#0MARd<*fqg}B>7{A?i(wh#wfh=VP}vlik~3-P6e_|igrX(3Lu5bs%t+bqOw7UC}p@t1`-%0e7vAs(_2*I0yWEW$Mw;Tnr@jYYV|'
    'B3xq;uCa)BKNjH{i*SuaxW*z}V-c>g2-jGIYb?Sw7U2_%@QFqE#3FoR5k9d9pIC%XEW#%i;S-DSiA6ZWBAj6nUa$x+ScDfW!V4DR'
    '1&i>4#q7IZ%o_-cc>`fF@2@Q8eT2olkFc2cR~EC=esOv-ca~YDg($c0elh#*7xO;CV%|qs%=-w7c^_dh?;|Ycjg`f`ov@g<6BhHv'
    '%3|JCSj=AjC1AFMHxQQa2Er2FSXsjR2upY$VF_=nECI76V73IzmVnt3-cDG;w_eJ(Udmf3OL;40DQ~4Lg%eBR#8OzW6c#LH3`-fq'
    'QpT{9F)StTOUe6E^1hV3FD36w$@Ee(y_DQ81*K)6w2b#qmhm3SGTuX31`C$Kf@S1=8F^m@O3OfL87M6SrDbG#8Dm(^7?zX2<>YTU'
    'nqE#emy^xqXnJ}6TSv)zFUuLja>lTnZ@rw{E+@Ck$?bA-yPVuEN7Kv6^l~!298E7L@5{k#1(>ZMn=8oX3N*cf+^!(EE70@`Fk1m;'
    'E5K|8n5`hwEBMwc`PM7Z^hz|n5>2m!6D#4wN?5QG7OZ3pD;dK|#;}qxtR(L%$@@z3zLLDJB=0N9^hz?llH9HYrB$G`3Qey<)2q<*'
    'Dp;@z7OW!gtH}E*P+A2_t3YWLD6JyXs~E#-*1=Y@4z@b|W^t>L{A6)eY&EN5t9g#Fnl<Cqbm^;kBDR|Kkkzb_t!9mEHLDz}SruE&'
    'O2%r|!B(?&v6|J2I7*%vC-eT*tX8b1_g+m8y*hpxze}<{QJVZ-Fq>b^tbBF+EP1zNK3!T;5=Xn`X3$YS%B@S~qF{Etnl-ByW>PK8'
    'q*@9&$~NsKEzGN0m{+whlWHMHE##<$9JP?67Uoqg%&S_MNwtu%7G_c{WUPf8wJ@)0A!9AfvRcSrF^ck0F`F&S$6A<WwUFr+=1wi-'
    'y@k9NqbMI0S<u3~s)d<U3k+#tUe&@(swH7hGLtH8SJDEPS`scL^Qx#_K1!L@!knuGX0<Q_Tf>_88oXc)Ua%(htav(BvIb{ZgEOqb'
    '8P?zoYnZ>UfrD${;2K!B24`4<GpvDUYjB1&@N5mvu!a@SHE?hZtXq>XEBVP}>>=ycz_T@QX$|aIlkg>3@hnaLO2DNxtQM|;OKafE'
    '8d$J~ysyDg){yr#I7%xkHLdtdEB?}2$a{Q9NGopBirci}Hm$f#D|v4v@2%v$mAtp&Hm$f#D{j*Y3tDlTR#?zV-dkDIX@v!?I8iH{'
    'XvK+IVMsBG3Q@|JR$QtT_O#+st+-Sx%xcA@TH#qMJS#>~Axc@-ii5Sn!B*CZT47`>?$(OCwZhg`+^rRNYsKAK;dLwS)(Xp8ako}j'
    '-io`e#iiD!{dIhKS7t4qwHD7>i)XDZ?2L<DaV^|k3wPI2H`l`CwfWtPF#}7Izmj*UTokz5THI}IexF>jOFjO{WQSt>-d8@#`B@T$'
    '3RsH|u7!hZ^LrBGzY>oq<lx%EKDm-)v?1%(!n3t-X>ERoV*EXm-wXJ%7EY`s(`(7?S{$qmw`nWnFJ7K(!+YBBp0;o=WA-OQCu$>q'
    'ZRD?w{I!w4w){TFl4Q!zMmF1UsWx1yEx+qAc{?G~MmF2>`y5N+4g2{h&21a*)<$mI$YvXk(nfBJQIwC0nQp^v+Q@rbxLY!g0w-#N'
    '6KyzA8w_cKA#J!#8+<87Q9dfNrwzAh!)@ANRvT{9hTF8^Hf?aQ4Yz57k!?82I=Y~B_{%!{WgY&q4u4sPzpTSw)=??f!Pa%KbshX%'
    '2P4<vFYEA^b@<CV7`YA(uESr}!NGO-%R1`cI{3K`My`W{>tNkFn6(Zrt)r@~gIVj~(mLwcI=HkBzN~`<>&W{$oM=5=(0Y7nJ-)Oa'
    'Us{hZt;d(v<4fzw`+D-ep1iLo@9XiU^{`+)zO)`+T8}TShXw2LrS))PJ-)OaPOOIo>*<2l!-@5H)_NGS9?x12U)JMU>tWA&JZn9k'
    'wH{`z$FtVMv-R+7J>AoKShpTOTMq}<<7ew(<a#=*_3(2&Ubh~vTMu{F<8|xty7hS7dRV?5uUil2*W+~?m>X_jZn%ND;RalB1FpCM'
    'AKZWsZh-R}VEG1~=5B!V8}PFY_}K;+xdE5jz&v0Bv%w9_3N|ng*g)sM0hVuo*BfB#23WTNo^60<8(`K3__6_pY+!%L1~{>SOm85!'
    '8}PFYbj=%>8*XH7xRJTxM&^baam9_e;zoRMBR;qh=i3MiHo}69uwWxB*oeDr#N9UHQXApKM&^ba;lxH*u#vgpMmVvNx#30_vXQyr'
    'M)<N3SKJ7DHsXpK;nGH&ZzJxu5uR<t-8RCyjj(Pb?zRyQZp7U-!pMy{*hcud5eM4{TQ{=5U?c9f5hicM-8SNG8*#UdaDF51wh;wv'
    'WZt+D1#HCmHlct`C}0x`*n|Q$p@2;&U=s@1#2%MT=wTCj*n}Q7p@&T<U=s@1gaS6f`AzV86HML&cQ?V-P4IIQjNAkxH^InFFme-&'
    '+yn<V!MaWGY!l4d1eZ3!rA@GB6YSXpdp5zBO)z8=oY+i_+f0qyOy|Fuinp1Hx0zmlGnw8@rZ<!6%{bp?y1dQw`kSeZo2iYP>GC$y'
    '*KMZP-;85!riyOH&o<*=o9W~><6xWV);7bC&2VBfF0~n7+DxCd8DH9r6K%$OHsddwagELR#AYhx78Je(g>Rwr--6z^p!Y3w{#(%d'
    '7Fe(a7Hok9TVTN!I{z(jVhhf&1!veo=f4F`Y@zet0z<aoC|h927C5m5*VqC>w%{RK;L8>||1Gd*3vROoE^VRn-+~iufoEHAqAjp)'
    '3#{9MFKvN?TX3l@Fmel>{}%YU1wY#YTeskDTj1^%ylx9#w*_8r!TGk}d|Pn7Ehu0MKDY%vY{3V&qKB>MVJmvriXOJ2hpp&gE7fo-'
    '>ez}pwxW)$sADU7*op$SqJXU^U@M&83d^^`<gIXbD{S2gKexijtuS&cjNA$%x5CJ+aBwTE+X~ON!mO=uX)Em63VXJ~m#y$+D}31s'
    'L$<<+zp@YFuk3^PEBhe+%07rfl=LBgWmm*s*%k3u_CfrWoezIyH`8A^Rrjy#d?3oCQM{=o{>ku+-Tw_n)UNb@({s<`=Dy^A({s;b'
    '$IL~^h+?f|qj&>o{Cg$s%Hk;APgIBsxMVW_8{krsi}JVxQE9xzG>tNaC`BUqX1QCJi&3nqvMB%ml3SPaQU3Jwcns~*C=+j}%}4QW'
    'nAk)9H$6)|Ii2%=^E+(feI)T;$?cFTM9D6ws9n7K=5O4T^tZyT((w}3-#E?ZZ=B}yH_njy8}}ytEzNCAkakJbe%Iub)F>bAo<CXP'
    'Z`}EnMls7ulBjs1+ut~Q>Tlee^a5jefib+m7+zouFYv8jD1PfKeO@Sj>nzqU6u))W!Cv5As27UgI!l-rIDPE}&Mtc4JKs9I?db(h'
    'JbQr?f?nX<pBFff>;+Exd4Y4qUf^t>zjIgn-?^*(@4?DYCi8dhWB)rhu>YM~*8d)y*pqyg^t8ECFaORh>uHopZc_g{x2*p?I1wcu'
    '#eXGPMg4pJmi0{1J^h`V)c>BW1;sWP&yQYYd@nM-7a8A++)V!>qkWOlzQ|}_WJE7Ah8G#bi;Uq#Zi;`A5xvNWUSvcsF`}1(wY*H`'
    'CC2v><9jKX=VVG=Vze(YqL&!MON`+q#_$qjc!@E*^qp^=96M5yt2r+vt5kW+GB4xMFXPEC<H;}M$uHx{FXO^5<H9fF!Y|{(FXO^5'
    '<H9fF!Y|{(FXOu}<GX2;iO<!{MFkgr85e#T7k(KR{(s!9`u~Exn(d-A$`qsg&dnf7P9II9OyRS1A7{JLG|CjC!a1dBl*vcoovdjT'
    'Bat!6{*~OG%eVz=my43Wl8wq<A=9sr+gHf#E9CYSviS<xe1&YjLN;F^o3D_~SIFioWb+mB_X_z-qZs-4voM>lkj+=f=0C{hKgifW'
    '$k;!~*gwe1Kgh~II7>E-GR3HHmTVej@==)0e~`_8kg-?E*sF9;ucFjf$>ytM^Hs9>D&5no==N1I{VJJ$l}x`%re7t~uafCk$@Hsq'
    'Pp^{qS5fh+<o#7L{VJJ$HNVmp_wVsH%bx`mzjRajYI^!pS@uts{gbZbpL8Yvq$~L+UCBS`to})l@=yAuf6_1glhf$`N%!<mx~G3~'
    '8vQ@%N?zkzzs9$Ijc@%L-}*Ja=WBFGuhAjB#tG@K(J#G5zw{a>q`&r^?-_PauhBidM)&j@-P3DyPp{EEy~e5JuhC1rMlbamXN|v('
    'a$ZL(ucMXM(aP&+<#p8YI_h{Gb-a!`UPm3TqmI{6$Lpx$b@cE$dUzdId>wVXjyhgP9j~K~*HOposN)Sh@(n898&teE@Xt5!&o}VT'
    'H>h}TQ1RZtTi?K2-@qf^z$1yWe<eJbn<)EP?(KwRik^!Kr*^+VrF;Y5{TFwc|BLrD{uLmRj|y*X{EPFw{}mvS`>gm5$G-w3@=@U='
    '@P7qJ#8G$$`oDs)ml|dNN_Y}DQTDSU5}907I3@gF0TRh)1tc<MZ=$0&QO=tv=S`IJCR%wDt-Og=-b5>JqLnw%%A08AO|<eR>Ua}%'
    'yh+dSCR%wDt-Og=-b5>JqLsJM%3J8+E%fjfdUy-YzXj*tqMvw+e&Q|qiMQw{-a;#Hp_R8#$6F}iEja&gIR9^W{cm{vZ+QK0xchIo'
    '`)|&)|93E=d{j8o{@=lf;wa?&zv2A9Vfnvd^1tEkf2f=Pp>F<%x|v3q!e_-QnnsyoROkfKD3g!Edi$UBJ)(HR*X}?0wTn!0*yDd#'
    'fB6sVFaM#R_zyk9f9M(hlSv-3#s4AOP9;(9KV)h5A1d?PAn`UxybTg>gT&h)@is`j&1l~)jy5Zgw~M3AO6P6XZQf?x=54x?x9L3I'
    'rt^54(FReJj|yWCq9_-INQ6Dg+w>@J)1$mikMcG>%G>lPZ_|~$O;_>`$iD;f?|}R}ApZ`?zXS5`z`=Lm;5%gH9XR+7Yk=>-!FS-`'
    'J8<wFIQR}6e21*O1J>^{_IDZkyNvx^#{Mp2f0wbp%lO`fb?>rT_%5t_7uLNC>)wTR@4~uw8Q;6G?%nT<He}YjFza2I^)AeM7iPT+'
    'v)+YS@4~G2K=(b+eGhcs1KsyP_dU>k4`#gwv)%*w_h8n0xZ8VqtmF4Cqe7Hp)_XAPJ-GB9Sigs+b5Z_Oi6kl_|6cwXO8i-AE{eZ('
    'yuYs9`=InbD7_C#?}O6&p!7Z{y$=%a!@>7)zW0krWb^kv9DE-Rz7Ol(2Z{G#-TUD3K3?}eC<RfJi;9@N4_n`dpYOxZ_hIDwaPWPQ'
    '|A4j84_FQTfYs16$`qpFYHu24icw+hH;pp+C|o!FfOYQ=^6TEY^OHYd75oF%j6Yz#^#j&hKVZG}gZ%D|+^NVPuuA+veh*|O*#r3j'
    'tFQkJa49SOZ-7f#^k4RW{x`rS7p1tAmi#xsB_HK+DQ)-P0GBu_;!;-jUrzA<Z-7fwh;rKeFDFU=mow4-8z2!!MI@r^cPWlN%6te5'
    'K7<7y!h#QB!H2Agr%|R56&dm&4EYd-d<a86gdrcoi4S4Hhp^y7Sny$f?74HZKZFw>vIhSl4EYd-d<a86gdrcnkdI)<M=<0g81hko'
    'S!uhE0?cwzkv$*5o{wP9N3iE3*z*y5`3Q!51VcUwP>KpsjxQg<myh7f$MEH2o~WczrWh5t^f6re7%qLx)0Q;K6r%#qK89x>!<UcY'
    '#K&;rV>t0KocI_{d`#XyChs5TcSt3xg(V;Jl;-37UgCtUnU8s9^9g+UgdOFd1eoQc0+&94OP|1{PuPj~Nq|{CD)8(Rc=ic=`2>c1'
    '0z*E5A)mmIPvFES0WMMYzZa2+GM`e>Kc%97N=5&aivB4T{ZlIXr}RCa()WBywf~g9=TrKgPw8zw<<_Q8>7hTR@A;H!|0(tTQ>yl-'
    '+?cZsB({OXHjvl`65Bvx8%S(pwA<)yw$a;cqkq}PZ9&`UsJGGEY-6<B=xw$!_HFbw+dyI){mZuR;1b>>w2eE>w$Ybw<3^xubV1v='
    '^=BJB(KhZT+eQb!jXQw0(LHVB{;_Rz_uIG;Xd8XjXJq;_GW{8u{)|k2My5X_)1Sfl&*1!Lu;4Q|{~4VBj9&jU6z~}e_>6nYK0^VY'
    '!HLgc!DsZepTUC9$ops98TA=AC4I(?W1rEte#VSpJ6LZA>+N8@9jv#5^>(n{4xZal)pk_1of*S+G`1a$ZRbX=?PzQ}cy32y+d+3b'
    '8ru%m+nGOX2l?&jZ##L|j{dfjmF?W*wH^I!M}OPV-*)u39gS^AW82Zuc678IPHcw-pVNnYPOtGfy~gMC8lTgfeok-tIlbxU^roNF'
    'YkVHu$y3tqbLKLi)3<(3-}*T{%IEYbp9i<;l$3l<Z~8gC>F4=(cao1XpVP5?PRH_jx<Vd*ltk&hJMn0XH|=EFeL;`%1%1dD^dVo+'
    'hkQZb`UQRK7xb-P(6@d;AMyov9DTtY=nHz<FX&jlpkw)h`-r}vi~S<NEXsUA|MEqEQfU$uZzuYK`-r}Tbzj1|FJax6u<lE`*e~f~'
    'zl4!r!pJXS<d-n=OBnejjQkP~ehCM^go9rOcR!UBq8uZ?q-*|?KKV=7`Xy}r61IK`Tfc;@U&7WeVe6N{4N~!U3Ay_v-2Dpfeg${G'
    'g1cYA-LL4AzoJk63SNH&ufKxVU%~6I;PqGV`YV|H6-@q$JGj1r*I&_ze+A3Gg5_Vq@~>d|SFrpm?&tan&VL2xzlQT)GvoW38Q<6F'
    ';cN8pHG24(8Q<5;_`XIfU!#?;;r!Py`D>W`HB9~*CVvf+zlNV*!_Tkb=hyi+#uC=$q5@mL&hL?rD`h-}kh@>!-z&(SL;f|h$gi12'
    'ew}|iFHv#kYvz<+GpGCp&VR$4@*C!q-=K$Y(8D+A;Tz_Z-!P~A2CaO9R=$Dr-@xl{;Pp4~`Wtxt4cz?(?tT*>Uz&>wO#UW7KK`B|'
    'ufGY9k4nB_p88FIb^IT~S?dlszXM+HfY&?V^$xhZ1Mcp?=Xc=qJMj4(`23FG7P>eJ6|e)>-+}Az!1Z?ocLSCbqMUMepqw3OWd~Z>'
    'f$Q(U^>^U<J5bdQRJ8+D?LbF6P|glqe+RC=Be)wd)9zdJ@GYGG7S4YQ=f8#5-@@x}sR7?o1HPpOd`k`ZmU{!gMIGN#5x%7&e9Qff'
    '-=d>$(b2ak=UXbmw^W30QPsDo>RWX5Ez0?pitsHJ;ahHH+=*7=C?-t2mXImgNwwHXwb+TOcA~1CsA?zGVkgyNCyLvN;&!5(ohWA~'
    'df15`cA|%!=wT;%*a^#b!t$N4d?&SIC!F6&?bwL|cIMxHiq{~L&jQZx%)iT4n!L-llPa^5DzlR+vy&>blPa^5D$_0sRTW2RZnL08'
    'Va-XSOff3xuMj1QOQTF7D%PAd$`qr5Hq$7RMuEoKMWM#BQJ|wV%IPSMiaJW7f{xlnp;nTppp|w}Sb>tLpqw}=R-hy*=qMW%@|S!T'
    'D5qUi%wLvTQCO>zs8Fl2QBbRrs8Fj)qHqPIBnnqR3Q@8G5=X@~k0dIrD3wIvnnyMYR)&(OaKC*V71u^{QMxjeM1>pe(<rw~HX8*u'
    'jh95>`a}{H?j4V#;*H@M#+PAy8OE1kd>KZRiNdv+OcdUoo{7Ts&rB4q&19nRw)9LC?x)Q#q6{Mnq9`8~#ur5S&%)7$_oHW`a5c0T'
    'l@+3NHKrJqrBPuurWlpwqvC34F)AxW=}Jv8DodkXbGxH6K~$EDf|b%@R91-66`o>LmPWb1S(*u=cne=d-XroJk@twaNANm=1rfZC'
    ';B^}1c7I2(Jc8vBypCW&1PdbaUdo6{8Br-CDrH2ajG+`Jm%`-IDBKxd3a?Aybtz0PWelZ^p%f;UerH4>lS|=eDU2+IgQc*p6rPpB'
    'tWvmC3VTZ7OIZ}|@hpqN{m^AmxZ|@BB|ARLqHxc1SrqR0EQ`Xunq?_U@wFd?D7ROWDEn8!oy<v8*vI+3DBQXEy(rwR{JkjL$N9Y|'
    '+{gL7DBO|!y(rwr`MoIIf%(1QdlsYI4osr#UkUdae=iDmXYK-?yMW*>Ah-*d?GlCiVt0wcov^!r=Puy63wZ7VX1jvfuAsClDD4U^'
    'yGG%T)?K4;59_XAwkw$J3TC^4%WkN6H&nbED&7qh?}jh!hNgGJmv+OKc8kL2GP~hRyWvZ_QGItq)4QSR-B58H6`u#}Mm=iJXxlT|'
    '_KdbYqixUl+T&U6@vQby_?)CYp4A@DYELb0&-mIizV>)ldq&$H&uY)ugDA>J0TN+lZck-ykMp&sGPlPE+f$j_<BIL6%<b{W_EhHf'
    'IA(jQZ+jfGJ=M28{<%B3-JRU-PHuN6x4XmS-O2RsFnM>FygN+ZJqn*N?hcc8hsnE>>D|fn?&NlNvYCt0XIZ<G&E2E$*-{b}=C>Wd'
    'r31Kh0GAHn(g7qo!1)evz5|@^5QWbMJHYu4aJ~abbO4DCaJ~b$bb#|6K&b<q?*L{&6y>7=f*sI92RPpW&Ub+G9pHQic-;YBcYwPc'
    ';BE)<w?~wJ*D{%A<)U~_8BfUeC}uO0M8Vx_dqm;gYkL$kot;_j5rsFg?Gc4HvF#CscdzXc<=>Kw|9e?3%HMaEi_-hf;wZSKZI39t'
    '+cAxDYY=-x;Vo^sD7~d^k0`vQEslz}wB@4ombN4++|ss36yDOdM-<-exJMM;r&x?~qYZCREJpFz_XPPpL4Hq=-xK8b1o=Hdeov6!'
    '6Xf><`8`2?Pmtde<o5*mG|JtNw<pN&3G#b_{GK4cC&=#!@_T~(o*=&`=<W%gdqv@yGJ8eg4Mcm<EAB-Xv=?2_UQu`-(Oz_pdqv?5'
    'M0-WynKIcZI8$b?D7;OFD3eCH^Jeync1<=Plq5Iw>=lK#6D3jMcA{LA-cGbv6y8p>R}|h(l#PPhiE>eTJJDYG^_Qe~%M_#1d{n%-'
    's2Igd2YZ9=-cfjB&)!jZV$a@Dcw$c>N>1$AI|@(i**gkP?AbdCPwd$nboU0`y+M~Kvp4AO9fha)5M_TdL_UcMr}^v+E_;K-_o-^%'
    'r>cFQs`h=V{r9Qp-=`b>J~jON)bQ^!XZ}8Q?EBQJ?^9*I9~I7JOukv+7Rapr_hAhCFot~?!#-5sedsawq2BI8z1@dd@;-d)efZY<'
    'P+|9B4Es<i_hCf)&_@=dh^VX(r4_aqMMPz36rdDV-(nOImF1&i|5=P8qOwAiR_$UG5tXG;Vb!P@MMPz}DClB~QAAW$h|<2G7)3;7'
    'X;fHWDn=1e?7KgJOFw{1KY&X=Ko37a4?kcH=?AFe2dLu*=-~%2>jyCF2k_+w<hCQ<x+CAZBj36s3h2l>QAhO95j}K70Ui0C9r>Oe'
    'Q9wt&bw_yJ5ngwM$sJ*G$M1|b<Zef}+Yz>QgsmOnXGi$i5k_`|ksaY+M>yCK)^&t+9pPC=c=kiqrGCh&$`4sp`6264KV*&Nhpe3Z'
    'kd+gn?C*suQ9oo=<%dBPjsIUB>twy>NAwy$qSyEly~dB|E`G%N%a2%9`4OusMA_d9SE7Ezip!6v_CE@~XH@cI5d1L+{us=D%(~Q%'
    'S(o}Tc>WkXe+*_n2D2Z7*-t>}C!q8baQO-AQa@o`>L+0K6EOP;xcmfMegZE0;tc!Z4Ey2?`{HN&;%ECZW8W7)+ZR9EmukN+KCv%8'
    'u`jdFeW{fD;u`y+{!Waj6C>)xh&thQotSHP!s|NWb)BgFoftzW#?T3`>%@pUF`w?l_&U)EbYirf=ma|9n4NIUPILmD@Xt>8XQ%HV'
    '7<K}kaMMn>X(u{?PIzl4ytNaZKqs8G6HeQS`rZj|?S!{>qP};+X*=Px`@xC*;KY7#Vn0~EA1vPwmhZ>9)PAshKUlsW4A~Ec><1_I'
    'V^w88II$lr*pH0u$12ButWtGm?422VXU5(cJ#<D7omqS8j2=3pht7<)Go$T{9y&Aj&gh{tNOWd>sWZ5AMk}2`sWS@bi~>5NfX?9A'
    '83lAk0i97mXL#KiUU!DqondQd*xDJkb|#zqvwvcLc1-Ngj)^oXEqqoyXFZKd^HF$z&i+w&YViJ1c+1!RQFx~I{!w^(`u<UPdiwtP'
    '{FNpvL;L45R+>C$-9MkBc-5#Rj^bl=cg^K*|0uj+V*e<-b!7i2yi;QTD7-~t|9t-9N8B+=Y5sDUg=YxwpU*>X-^Kn>c!u!)QFzMq'
    '{!w^ZbR5OsJGWCN8zl=A@&C(3#rqNVkHQ;5x<uiP2wjT$%VwoZ6yA@}B?`}g?h=J3J9i;RUC2=va@2(!b&0~0ox4Qg$<AH!`iplV'
    'v@7XC#=4NPE@Z4rlCk7O=#qB%D9vA&D7-tN3)$>K{)$nQMult^qbL^zxh+Of8Wl2KjG`dQofh2%7Ic9H#VAUn!YR{TU`Q7jQjDS`'
    '3Qvpf0(-h7>`6XLunxJ@CE-$Xc66p)K1!L@B?@m@=mO8WM&X@9U2%r4I73&Qp)1bN6=&#*Gjxr@^TfNt!LD$yE3E5^Gjzony27)r'
    'FsmzE>I!?h;ssr!@a~zeFsmzE>YDF@k_|2;UExw!*wYn;bj^1x$x?GkSNPHuPIQgJbL+dpkgl+xD|zoqrn`P8x1oo0i^4lry5T6@'
    'aFlL1N;e#(8;;VA+;$_k-N<b>a@!3@>4u|p!%@1C>274Y8y?b)ym!Mxy1{~O<h>Y0g(zh~H~gg=oalzXbb}$qC@MrLU%KHv-C$2Q'
    'yr&!9(+y^IgIUEWDnu#Iy5URR@TG2Wup1mKMo}S38QBfb>V{`^gRR~0tZs0(8=ln-CU?WLy20!2cvg2jt2>_69nb2HOLd34-C=9@'
    'D7@#OJKXJ#FLlS4y2H=zFtR%w?2Z$4hmqakV0T#89iDZES>54MclgpBzI2Bn-SaGn>vX0N6@D+^M0Z%wJqqv4=uY0dlj-i{w)=Oo'
    '8M;&tT&f2y)dQF6flKwkrF!5}J;-zqGTnnr_aM_faH$@+R1aLL2YK&-FZF;0J@BO-aH0n+=z%ZwfD=9Nr5-S(2fow;zVyJCdcd9@'
    '_)-tJ)B|7YfiLxdXFcFq4}7Tytm}a<^?-xLC<>zD|10vd2mI`TXZ3)sJ@Bj^aJLvmNfi274|v@JKkEU@d*Ek1;Cv7KtOp7>falW('
    '@O=6Jo=+dZ^XUV4K79bsrw`z%^8q~XKY*vs2k_MS0G>J@z*FY~c<OurPn{3osq+Cmbv}US{Rb3zos71?<Ycr3?k3|aur-^&1B(32'
    '(&vC8BQv=u&$D)=`6$VByZmRl+-8wEfZYbgC?d+?8SXtOMiEhrbx%C2C!W<4&+3V1^~AG!M&X@2J#ny}I9N{{tS1iE6VK|2XZ6Ih'
    'dg4+&@ui-4Pfy&YC;rkCN9l=&^u#rK;u<}1jh^^KPn@AAUeFUS=!qBfMEyO{druVJ6NUFg(>+mfPjuT0rS?Lpy-;c|l-diW_Cl$>'
    'P--vshx9_Jy-;c|l-diW_Cl$>P--uf+6$%jLYuwNW-qka3vKp7o4wFxFSOYUZT3Q&y-;H>)YuFC^+JCKvbW+ucCH-A)1(7=PI4g6'
    'Ne*P^%7HvvI*^?!2eP-~!2I5dY);yh8f6Y--^GFKyCBN`WVmzXKz6Pi$j+4m*|~BcJ68^5=gNWXTse?uHV3jp<3M(<9LRo+pMvgB'
    '*}3vlcCP%Cohv_O=gLpnx$;wXuKbjpD?bI@pMow?=BJ?hQ_v+!ezLfag(&-3h{R7B`$3HTAeeO!%sL2W9R#xuf>{T_tb<_ILHV&q'
    '$(|ab%t7FC5V#P<KN%oFl>IE^*+KB^Ab55VJUa-U9R$w~f@cT8vx7kQAb55VSpN*He+JKf2G4#5&wd8aeg@Be2G4#5&wd8hM46v~'
    '_0PbXDE`R+Yogp|1=bN|KMQgB8Au$=jP_t=v<EYzJ(yLvgL$LzU}n1qvnF>iD>VnxPaMoj@WIT84rcCqFmvC7nado^{PtjGF9$PU'
    'IXDV$t2~&#;9%<e!BKc8<iT|J2h*h=9EEo+9vp?YD;^w$w~Zc5Cw?$<(cW}&z3Jq7)5-OY!dn@8)7SN;lj{xgy+OV=$oB^M-t=|7'
    '>FavayY(gyy+OV=om_A7(3`%lH(4o0Q7#HPx!z=~H~m>}^4FXE6{9F06|>o!-mN#?T5mGlI|}bi>`mT#N8t^My<tIb`nuk*pbzUy'
    'eNbZ`)Yu0#_Cbw(qVWFWK4`NK+U$ci`_Sw6fiHdFOCK202W|F2n|<I!AGFzrRfj(Cr4J106NPuq_JJXNU_l@9-X{w0dF=xW`Y?a*'
    '0}J|)=|1GP583R4ru%#+o1v!rGFR)1!uz7|z9_tJ6yCzx7rpmI?|spGU$WVkZ1yFaeaU8D^xhY}_eJl0$!%Y<*_U}-Uvk?QFX&6A'
    '`{D(C$$K%13Q@{}zW796e4;N5>5EVFg)e>KOEHQHQOcgact~Hk)R);{UzpVwf9Z?A^o4bO@t3}EurL177e@BQU;4txe)vm2{G}iM'
    '(hq;>hokhvQTpL1{a{@`c-D{gf_|{BA0E;V59tTb`r#q{U|m0W)(>X&gG>EjPd^ya4^H%h6a8R8Kl0v>O!s4*uOGSXM>hMBzkWDM'
    'zwhKPbd>%$N`D-sKaSELN9m8F^v6;9<0$=cl>X$lKe_EsZu^tl{y0j19Hl>w(w|KCC%64^l>TJ8KaSF$y!XdZ`on_$I7)vw(H}?Y'
    'kE8U5Fa2?p{;;P%?CFoA^oL9Rag_crt3Qs?AD;EcQToHW{;WOq$8Gw<$o{xZfB4xSx9JaC`{OqKVe0_+IRJhRfS&{4=K%OQ0DcaD'
    'p95IA8~|Gfz}5k<bpUJ~06z!7&jIjr02~|u>juEH0WfO-Tp9qE2Ee5OaA^Qs8UT9+z?T6qWB{BP01F1df&t`x0GS>@Zhszy_iX(<'
    '3U7M+c@*AW_wy*cgX`zPd+fQt(muaqH;ID#x#FmJKiAKr@J6mQ$`qpFja+GzDMp1GxzZ?;kHWhh(<pa87g6TtQFyc6&!h0RuAfKY'
    '{ainf!uz>?9))*${-Su6P?iY4;2qmvu$S={>|Xo@J2!v9JGQ@w!aH)3sBlM4E=q4Q`33JKr%~?S$6v6o`4{Z?`~~mW9>N$7VGM^b'
    'hC>*`A$;pYqVVRML!$8Jn?s`T){#Sahxm{vyan<Qb}}Er&do!<^R2@-gAZXZ@geM%JcK=vhp^N45OzHt!j9cT*ys4mC_EADmqnDa'
    'U*MNfc+S@^qwq|;Uq<06c)yIo^SZK8aK>&D6>bR0Md?X*X_UJs`<GF8vez%8@KnfOM&UgGxhTDn`Ik|6n%ys>@GP%5YQM{_$<ajZ'
    'qC*+&p^WxWMtf)!o>g`zV?UI!AIjJdWqgM+qC*+cp^WIzC_Jm|P{wyC<2#h`9m@C)E56g4ZIlmVw1+X;!=muCx5F6wVNrO7+hHJa'
    '7^6Lm@g2ta4r6?WF}}kX-(igCu<wj0JPqxzC_M2jj*_2D9@89-&mWGnAC9vhj<X+*vmcJLAC9vhj<X+*vmcJLAC9vhj<X+*vmcI^'
    '6J-v^%hM=#4<k|TCksA*I6i+kK7Tkq|9=9M+GWxxQ;hPM1yS<$Od4g<&w}@)(kN4m3h(@+QKk?T-<nFJOff3F50plkd=#EclSa8)'
    '8HqAP*}oayOZtDJ@Q%hKV9yco<p}t41bjIHz8nExj({&mz?UQ7%MtM92>5aYd^rNX5M_>lAw;>)3Jgi3+`XMd*`EyAa|G-;0`~k0'
    'hWrYK{0fHr3Kskd7W|4#|B6iiiub_MC{v6IZ-u2%CLe_i`4tQy%6_wu1xLbyBk2{7#8HlfAxFZHBVovqFyu%WawH5n5{4WJLym+Y'
    'N5YUJVaSp6ibuj1qRf%_%aJhTNLX+rEI2X>?{Ymd3h#1FqQYISzorNKH9gp`>A`+Y5B6*N$Y0Zu{hIFZ*K~)!=AGVO(<}a(Uh&tw'
    ')B9_Bu%r0aNAazX;#(iZw?2yRc@+KNQS^gH@lNkibcaXL9UjFyy+?iLdxpK@QS^#O(JLNBuXq%_;!*U9NAXteQFM++(K#N)yRt{4'
    'oTJgo(P-spv~o0BIU21TjaH6ED@UW1qtVLIXys_Max_{w8g&q5jz%3v<E=!wpDZZnXq0m_$~hY49F200Mmfh&nUA3|AA|26gYO=L'
    '?;b;CK8DJC44!-po_q|I`4}qmG5GZ{`1LXP?lJf-QHCh{H^aAhi84glpA6rTK8E*wkD<OFgR>tS;F-xB8{nCb@^}VO@^0?20iMZc'
    '!48IFqwv1+W7*GeY!u$)d@MT{j*Y?_%8%u3<71=nmgi$R_wLvzyseoiLzMlS;hV@r8KUe@hVOD8%R9@*M&a${$421|(8r<o<52i<'
    'DEv4SejExv4uv0w!jD7Y$D#1!Q222u{5TYT9117O9EYZfa-S76eH{G~QT8W8y&s3(k3;Xrq4(p^`|)V{cr<-Hnm!)g9*=I1N1Ml^'
    '&Ex5%j;EJ8o?hyBda2{l^zmq#DErMq6%%DY3zd32+B^aMoq+yMKz}Eou@lhP3FznqbaVpm@ShNcx22!J8~rCl;ce+BpuZE)A5r$3'
    'g^DA}eio|g1a$NpdX3-EYot*o{VeD_(kN4iihW2LWr|UumrA2dJ_<XQ-$dbUWWR~R+sJ;ydfjhWulo%h*>C8&enZ#wn<%_JD~SsC'
    'W&MWU=0tEg5nN6LmlMI|L~uC~Tuua+6B+x7QFwFMiBWiS*omzAoye-+iFA1<(#f4jCwC%a527d^6_5y`C>MpeggxJh^n54M^PNb~'
    'cOpICiS&FY(&e2<mv<6*IEg%*L>^8e4=0g_lgPtK<l!Xvc@q3Qi5#5-KTl#k`6T#x68t;~ex3wBPlBH(k)xA9{$!9i86-{yiIYL%'
    'WRN%+Bu)m2lNs&FF!E&9p-+a9C&S2-VdTj$@?;o!GNU~iMxOkgv4^ZX8P=T)>rRGsC&RjvVcp5F?qpbZ3Rs^4)~A5=DPVmHSf2vc'
    'r-1b-u<jICcM5qp1=gK{E1nXCcQl>?>rR1nr@*sQK>ifepNrC)0#6|ir$phsdP!8c$>dZpI~B}M1+!DZ>{Kv270gZrvs1z4RQP!+'
    'j(KVn-nDot{5%zYo(dyR1(#D{<f))^Djs<%m<3Uki;4)I3X@NTyQjk4Q(^0=@bgsia2o6Er?JkSMwv7U*4a;s!kbf0;~7I5Wr|VZ'
    'i9;G?@=>@Ve;UtTPK&}@hEC&2%xOHSIE|J3(^$zrjg|b<qVOi6(|9&<S`^-@avJOUrzPw9B?%HG(P^ympU&MSrw0g@7Cy_QQLw+~'
    'bnYiPJqqstIz0;S06IMi?*KYI3hw|qof}C`kHQ-bPmjV|e@>6WTis9RwvyAM@V>0mqwo&q)1&a7pVPUm<n#cSC^`c!odK85fJ<k<'
    'r8D5t89cK&BMNWYIRl=Z0ng5WXJ^2(GvL`7FzXDsbOu~H11_Brg*Wt^0kh8F8POT=><oBz20S|ho}B^D&VXlU!m~5s*_rU{On7!C'
    'JUf%SZqDScn=|3ynQ-t-ICv%;JQEI{3G2>;XJ^8*Gr1M#Ojvg&tUD9doeAsC;<;fOWr|UOk!QikvtZ;|JX1U?3U81)3$~sGThHQo'
    '<5^L7XVh6R`7D@x7K}U#)}00G&VqGk!Md|x-B~c}ESPl`%sLBZofU<5IGx2)%d?{J)~2&~hIv-<46`J`I{usC6V0=Otdtg_Off1j'
    '`D~bcHcUR7-I8Z>_tV+1{A^f$HoGOy=C-G^QNY<K;B1(DHrzcM?w$>I&xX5a!`8E5>)G75bT&6EogLsAMd#2HokLG_4n5I1^hD>-'
    '6P-g(bPheyIrNd|&_|v_zjO|L<T><_=g=#j!x?AiFkd-`KJpy;rE}<z&Y|x)hjYFLg3CZ~83--|!DS%03<Q^f;4+Z052RNdNUu1M'
    'esCZso(*L7GLT+zAY&g$uQ(7S2GT1I1ebyIg9E>VQg|BLK+gOd$Q)=OXPgbBs~pHVW&`Ol2Xc1bKxRt=In`_+-RMBh=NrgOY9MEv'
    '4Ww^9m%N`#-p?iP=aTnx$@{tF{ao^XE_yf@J)8?C&P5OBqK9*tSDlMG&P5&PasuGFsN-B1axR=Wml?ykaN=B8a4x6doy)m!=W@#5'
    'xy%aAWp*|Q<OhNLAdnvf@`FHr5XcV#`9YvN2*nLTaf6th4MKl|(BB|V92|uH27&G%^fw5s2cf?~AU}w?+92{U2yG4`D}&JHAaXQ_'
    'lL`l+%|U2$5ZWAsHV2`<LFjJ~8XJVh2EmX)aN<0Asq^Ti&ZCz)kACSq`la*e;LoFjKaURnJUaOE=$Fom!ux2?W8Qck-TirV_vg`P'
    'okyQ_UKHLrdmbJ9d35mSMd59n=h1bYN7r>8UDtVZUFSvN-JIt|;SIFsMd1y!=hH8pPrr0N{nGjLMCa2JolkdvKHdHKbob}e-JefS'
    'bbb`xD|<fk&GYH}&!>AjpYG}WD7;Dbe0u%!xgGO-da3j2rOxMe%=4r0CfW0&@Fv;8aCb1=9SnB|!`;DfcQF0@VEXyN@Om)39t^Js'
    '!|TEDdN8~m43h`L<iRj`a1`DoI~ZOMX8tgk8N*;WKN!vrhVz5r{9rgg7|sud^Mm31U^qWG3U8nti~<IufD2H-1t{PG6mS6wxBvxQ'
    'K<9q}o&N=>;{w!i0qVE_bzFctE<ha@poa_4!v)+AdjaaWfVss5XypR5asgVo0IghrRxUs*7jSp%1t{kNlrx0c^$=#)Lr~QaR5b)u'
    '4PkaYgxU2F6gLFL4PkaYgxU2F)Hnn+4nb8z(8>_BG6by*K`TSh$`BMV1O*I10Ygy05EL*Z3h!qgf*yuM;r+}*P{)ucymfg9Gxj0O'
    '*oQ>nt;<80zYk&lK7{%E5a#bgnZFNZ{yr2n4n>VaQR7hN??ait4@Id%QR-0U??ait4@Jd8QSngJI26SVMR7w>+)xxZ6jcpHRYOtL'
    'P;P4;ipGX=Tk}v9H<UY=hq5LxlslM*vO+MF6@p>tZy5R;hW>`3v0-Rz7&;n;j)qayhEdgqQPqY~)rLjkjp)Nr<1lL6FlyW|YTU3W'
    'ygPjuDjtT4hoReH=yn)2ZWuLg7&UGf3Ll2ThoSIcD0~<SABLufq2giGxM9?|VNrPJ`fxNh9E}Y}W5dzWaC9^rtqeyi!>M?~sd&Sw'
    'c*Ci9!?_WCIEoui{TojG8_sR%!_nq&v^g9#4yXPNr~VB`sl!p~aFjY6Z4O6`!>ND6sei+{Nqq#>a0JzG1Zo_C8b_eU5yAcTnUWFI'
    '#u3!U5$JXVx*b7n96@ayfu={G=@Dpi1lk;d;zppj5h!j1iW`CAMxdh+=x78w8i9^Rpra8~$`Pn)1eJ0G8XJ*+M>AeuN<IrzH6s6x'
    'ZE5n3?Fee>2x{sGYU&7T>IiD;2x{sGYU&7T>PTwpNNVax^ga^3k3{by1NM}bjHJSjq{5EG8Ajp^BdM?>sjwq)jgh#<NYp<P^^Zj1'
    'BT@KB6h0D#k3_{IQSnGrJd%1l5>1b!-i}1!BLhw(p9Pv88E_&h8A)XxNo5{MWgbao9!X`skQK8FSuwkiHL?p?6}ylX$O~B&yO5Q{'
    '3%Ob3Le|+YWF_%J?h?6>cLy%yu8j*>!Mc!}H!kGPj8Tkl6yqDk_(n0lQH*F5t9PTgJ!BNC=c8D?8^wJgqj<|;6eAkNh(@s{H;VC%'
    ';%1Ri-x+OqL&zxB(nqnDK8p3aQLNXEV!dt@>vf}8OCQBr`Y6`&MzNMRid*kS@&3ao*4am~&OVAYz)`FLj^Zx6QM@T}5qZCeykA7#'
    'FCy<3!Rw1)!A0=;B6xif@5EdL%P)fE7s2a`V8KPO;3D#VF(bN|5narPE@ng*Glq*{^2IRuV&0dz7+zltuP=tl7c+*78N<ae`Qq=4'
    'C}i@*@bh9Ac`+Qk7}i}3&n|{p7sI8CVb8_z<+r>E@>}+a|CW8?zvXR@-?C5qx4hBuTlR_nmL1-|<$kr_vZtFULzMlS;hP!1Wxx0D'
    'c>Cga?Dzg1`@Mh18y3G~zxVHWi{f|e_x>F_wSULGY`<e~Hc^Hs`!~b4A%4fc?cam^??L|eVEud0{XP5cf6q?)--G<`LH_q3Pn7-d'
    'A-aD6&p&|YA3*RAVD<-g#s7hQ@P7c$KY-^Sz>_HZ-$TqU!5J>W87{#YF2NZt!Rs!;CoaM3F2U<A;o0CNc-<v<-6d4?OYn(H@QF)s'
    'hD&$~bqO_YG@~8OXh$>J(TsL9;~R|+j>ZQ^^K@=BJ~$d598G;6&G<$$zR~#LXhu649~{ltNAm=3^mmX5tNm!I{b<~DG}V4I-a49U'
    'KN_bUO|>75?~bP0kH&>ZQ_)A`!lS9^qw(ZR$?c`&_EK_tDY?BACSOXXFNMjM!sJU~@})fGz7!^33X?A-)0dLzOUdn}Wb;y<pk7Kg'
    'FXf5mr9AT<11@90Wem8C0hci#F$T_$f%9YF{1~1{kAd@J;QSbn7y}Yx;QSbH83X6XfYKN^KL*Uk@YHz>2#!GyW8nN4I6nr?kAd@J'
    ';Pn`IJqGTMfxBbK-(~4r?a4&$vf_L?`$sP;W;1K_mld;_Nj?isYrl;1*)QXK_RG>Y(BuD5c3Ju!ZTuf{QF<nN90e!2U&fsamvNH&'
    'Wt`-G87H}4#!2p%agzIGoaBBPC%Iq7N$!_%=fY*&dT<#ht6#=F2bXcO`sJW|Ip|&vx|f6Q<)C{x=w1%GmxJ!*pnEy!UJkmKb58!{'
    'pnEy!UJkmKgYM;^dpYP{4!W0v?&TnOIhg%V@-FG_?Q>_NCDHD?wvSI(E6qpk^DBb?le|5e{A3oVB+C6{7K~h!{A3o4ILfvm?c2pi'
    '%w%#=`{bOqD2`${+h@OWrZgY5PtJFXicxZRLK3x4*8u+~Ipccw_DNe;mPFbAUJ`%LeAGU_2KYZQ61%56Omk7XvX@4=vv2+<O4{9$'
    '_`J1tC0BsN6(Dg1NL-PuVCBb`kMiS-qnJGL__BZYiu`I*?#_iP82c5B{R+l@1!KR0v0uU1uVCzP6o0d1fcYqY#8VsvxLg4)SAfeE'
    ';PS`f*t6RFV=>d&n)k<IZnJd#V{t?!K~x&Q5uQewVw4+S7Vb34<fFofvgIO;GKv2FnCz^|=BO-QA55Y+N2T$B>A9%=u5nGv{bW|B'
    '?UNJvN^?>BEG8xSC_B9N$*aKmsC~S!mPW~22JNzg`eXiiPS(h?gZg9gwsH2;vba<xQSysfX~xkm`EQmTeG=uqSr+a;=I>OB&*zKB'
    '9zSB(B{?}T9&P;ZcG)%lX6?$Z1nVn{%*rHD%B3vwSAzAGV0|T6UkTP%g7uYPeI;05S!7Qp`7A*9O3=L$bgu;6D?#^4(7h6LuLRvI'
    'LHA0~y%Kb<1l=n^_e#+HzbT%{qqP5<ayNc}TAD_gV$?q8`pNGlQ6`OYd5D+UGygY5K5mIh3sGX<X_P5`7XQuowZXD9%H*Rw*6}xM'
    'mqu}pGTA6z?2VC+pY<kD`(2Ve#J`stUyNtFva8_BRq*91_;M9|xeC5q1z)a$FIT~kt6)eP#Un~S3;1#se7Op~Tm@gQf-hIWm#g5*'
    'Rpk9D@_rS0zZz9tje}i{gIx_uSA){kpp-_X#i)SU)nJxJrTHjS+|}TDHSTsb?sheJUJagCCr>SRZJ!);kdKn57}-Hx4Z2r@=hZ0g'
    'Y7}=hin|)cT@CVAgZwpMeGQDf21Z^3*4KdbHDG-WSYHFy*MRjkV0{f(Ujx?Hz};&=_ZrZ>26V3h-D^Pi8qmE4bgu#3Ye4rJ(7gt9'
    'uL0d_)6OH=!Eh~pb}fE(Eq-<_es(Q>c5T|RBu{0p#oew=JC>vYy%w*#7O%S&ue%nnyB4pzHtkX3F|<pgY>Uz^%15aWUW@Zxi}PKZ'
    '$0g1~E-L!qb>MOxxLgM=*MZA*;Bp;ET*uh2W9-*4_Ujn?b&UNwMtdEjy$;vEj<H|I*so*k*D?0%QQY+??s^n=J&L;?#a)l$u19g#'
    'qqyr)-1TVedNg)D_2GIHcRh-`9>rac;;u(=*Q2=WQO@-!=LWj_8|dzDpu4|;dCm>Yb8cXsa|8378<^+ZK(BuTz5WgK`ZpAjPoqNT'
    'e?t-LBnsyNH!u&lfqB3U`CdP_yWs{p{~PH1Z%BImlH|Xal-xk)e<PUP2xd2e*^SJIZe&JuBQv5KnGxLxN;iViji7WRDBTE3H-gfQ'
    'pmZZB-3UrIGF!Tl+0u<5cq0hj2!c0);Ef=76V>phJhS54ol4u?lxJ4<KV&6-6J5zobR{>T+ndnsO=$BbD&9@>6F1RM+?3Z}Ch4?p'
    'LX9_}#+&HYZbE-I(XHKt8gHUoyNPOe6V>o0s^Lvk!<*3bO=$Wiy1bjg`euCaW{|%b<Zs3!ZwBj|!TM&fz8S1<#_Mhd-J3!8X3)JE'
    'bZ-XTn?d(x(7hRSZwB3)LHB0Ry%}_G2Hl%M_h!(&1$1u#&s)Ir7MOesOuhwlZvov~s5!TQ^(|DHTR{F6SbhsEzlA*9LLP1*54TWr'
    'ZlUJfLRM}e54V8)Eg*jj$ln6;w}AXDAb%@Z-wKm&1^HV+{#KZLD_GwO*0+N7tzdmCSl<fPx5DyULHAbBy%ltC1>IXg_g2uo6?AU}'
    '-CIHTR?xi_bZ-USTS50v^n-t*1N;+R-k<35{zPB*r@U@U;y>9gjpA0ZG>LNKi~G7i<yD-C(~ygj@nzD_@^EId(XPpdCGn+&CD|z1'
    'Dw<qqnEfo*50)hT;GgpSU`f&s{wYc*QIfkE`%n4(rls+d>|B)l@7a(4l;3?CB~Q-(l;1rZpAMLbqZG4bw7ETPrE!!=qFkZOV)3W^'
    '4!3O4PCrY|6OShef6BW?j7##((kM%V+d%#{kiQM&Zv*+;K>jw6zYVN!%VQlMZC6@|a>(BX^0$HfZJ>J_=-vjNw}Izv;CUN(-Ugnx'
    'f#+@Dc^i1%2A;Qp=WXD5J9yp>p0|VN?cjMkc-{`4w}a>H;CVX;-d@=29?xZN2hZEV^LFsO9XxLb!P`Obb`ZQB1aAkk+rjL1FuNVh'
    '?f|np!0ZlYyLW)#9UyoI2;PzRy0|kfZFdKF-hngRQS`y=$9I7B9eE#&(T(y^%H2BxXNbR9=o5F~6L*089Uy;4;uFdDOnxtPjXRR8'
    'B;PCx=pE!JiE`g8`@?sjfIIT{a+j6mFbgwwNB$n1(j+T)kiR5~|7Lu*YCcN!a0mIjgZ$k|{_Z4ycapz5$={vi?@sb}CmFkw9NkHd'
    '?j%QdqK-Ss*qvnTPO@?*S-BJB?*#cfLH<sVzZ2x|1o=Bb{!Wm;6Xfp%`8z@WPLRJVKO4*>_4cm(Y%r75+q>vW?xHKXi+=Df`oX*C'
    'QSPEgxr?sku5?xx|M$#Y>8vjP?{O4#fOpXW-bIgc7d^^d^eA`HiQh$6au=QWUGyk-(TU%c^eFj$DRWnv_xR%R?D*myCAUsglEp0S'
    'QSPEgxr^TWZjiql<nIRgyFvbLkiQ$`?*{q1LH=&K!@J4D-E@a{la;&4%H3q;ZnAPWS-G36+)Y;QrgOZT&hc(?bT?VKn>^f29_}U&'
    'caw*^$-_Ok%{{oyJ^0H#_{%-`%RTtZJvhoec*s44H;%I7D@3_^dk^*Y9vtN!9OWK7<Q^*QJ@~{uIKw^E)O+xPd+>sL!R20XxffjS'
    '1($ol<z8^PxA5*&{4eeWrF%i?UQoIhT<!&zd%@*iaJd&G?gfc^8T-AA{XWKiA7j6d3Y12fAWCt$4_wkHQ;Z5I-Iv!xCOJy_K6;J&'
    'K=3{)*L@&(AC>FAq&g*kGx=u4sI=rhD%XAV8uul=M)H%%e-As4`#}CakiU=4<31|hePrc6D&Bq6xckW1eR-wExFr7}jWW5YSpV)L'
    'xA#&1?jzIpk?FBydMue9OQy$?>9J&bESVllrpJ=$v1EEIxgASx$CBHz`P{~OC@n;}Opir5W6AqiGCh|3jU|6$$=FyjHkOQyC1YdB'
    '*jO?)mW+)hV`ItKSTZ)2jEyB@_w#%#jWR)$J{3x%Od185zMo9r&-1Y~$^=pRj3|vVg{a7o`(eoaFyww1az6~YABNnYU$KsoXJ=_t'
    'nmkRqKfg8;B~O#?C)4+n>H7l}$73j}I2Xk!OWyEpmqfcH%t{d4H7O8TE+tXOm;2$%{p9w3o>$#Z#vULm50I4y$jSp`<pGd?0OTJ4'
    '-3LJT0nmK_bRPiE2f#CpN|UE^4>0xz82bZ^{Q<`Q0AnA=_{K55aj<6`>>0=S#xcHejBgy{8;8G)!(Ybb{Uu7O=s4VF9BwlXw;6}O'
    'jDvOKVBI({8wY0N@RxD;%Qzfm9F8&$M;Qn5<8YL5ILbIYWE@#}kgPmNRvrZT2SNTpkbe;59|ZXaLH<FIe~>QdL6CnC<R1k22SN8i'
    '(0vd*9|XY%LGVEkd=ShY1hWUh>>-{MKE#v4hj>!>5KmVh;_2!`JY9W=r>hU~bhQx04MoXAX^xV!8y@2M-$OkAdx+<M5Ajs*A@)GV'
    '(eAsY=QZb|^jwED%H5p#P?T&Q&b=dD@-Rp|3=$86#KR!*Fi1QM5)XsK!yxf6NIVP@5Ay`|VV;>j3`!4!(!-$iFep9Dv(JaY>|s!P'
    'm?xnRgVLW<B$8t+{+y0Bw*AbX(O)4-Hd+6f-5Y;Kn}25a#-GzMBqtoEQPK${QE{impV?{gXLefrnY|T%j^B}vqbPod>k-EA2zBfc'
    'M)U|HdV~=@!iXMWM2|3{M;Or~>>YW85k10)9$`d}FrvTkt^dOJ{0ranFMQ9x@IC*+_xuZ$`7e0nU-;I4;amTOZ~Yg(^<VhbkMex%'
    'QC2w~WtHR6qB^q1m`0gml+#K{@;7s1NTXmq<Wcs<Jj!~=qwI!xl&58nvK!`6)<Yg;J>*eVKptfU<Wbh89%aqrQP!m%Wd-C>)}<be'
    '68W`{t-LfJwNLQNNAd5)eO*4<HLh?a@$ZFC;2z}(+@m~!dz2?|kFu)rD61-uvbyzH>XC7oE_n=9J(jv+TvRiUp{mDHS4>{Gcnt17'
    '26rEWyN|)$$KdW`sShSEf~8S%xJN!p_4gP%xgLYNkHOu?=l~ys$&W?xp%T07nw0k>D*DUgAn`b3f1J@i&S)QJw2w2|#~JP8jPG&A'
    '_c)IEIHP?W-9FCPA7|{3Gxo<B`{RuLamM}xoOl8xo?wpm1P=BDe0c)Qo`5e;fZ!7#_yh<(0fJ9};1lrW2@rgOeU49n;1l@Z6Cn5m'
    '2tEOVPk`W);PNC$JjvLfWVBB*+9w(9lZ^IBM*Ae=dy)}7$%vkWAx|>CCmG+9jPFUt_Y|3ait#-~HlJdAPcgoy7~fNj?<vOj6f^y&'
    'sAEqtAA5?b_7s_Z3S6E7m#0ADDUf&yB%T6^ry2XxjP_|p`!u6{n$bSZXrE?$Pcx#Y8N<_z;c0UFG$VSN5k1X_o@PYjso~?P;p3^{'
    '<Ei1}so`l<T8s)6eLNLCjY`ufsPE&c@8fy;F`jBao@zgyXCdRM{o|?q<Ej1Qsr}=r{o|?q<9Yfqo~Iw<=>*18`^P7z6=i=fPG&wz'
    'P6#T=e^%%O##8&pQ|-r7?Z;E?$5ZXcQ|-r7?Vn*r^b9kiXP6N^!;I(|W<<|0BYK7z(KF15o?%AxOpz~XRG1$<Q)EaIg)^dOm=Qh0'
    'jOZC=M9<`Bin$X2pJCqk3^Sr<k~vWRY^{=Km=R3?r3s)k0hA_y(gaYN07?@;X#yxs0Hq0_Gy#+*fYJo!loQyMJAoPI1a{?40Nn|o'
    'I{|bju=92TSWjT~IRWG+fb|4+<xXHOI)OY)AP*DqrHMRUoygPGiFnpTJZmDJH4$H$i1$pyUnb%q6LF1+xW+`Dpiaa?CgLFznLkX#'
    'H6}8Dn23i=Wd1M_*O<usVIm$fk@>?!9AzSoG7(3ah@(uzQ6}Oj6PZ7hld*C#R!+vs$yhlVD<@;+)Rl7bS574<C!6Kej&gEaPPHf}'
    ')8%BkoJ^OK>2fk%PNvJL7Ufina`IkIrpu`o<y4Du@?K7+%gJpyxh*HR<>a=U+?JEuN%S_8=xrv^%}k<WnZ%mvBz9d*Vik1~`*bGp'
    'jC~Tj*e3DpGmhfHXMZe8qTt!*BvxN1vHCiReO8lLi=D)do=H5ZpTu6cNvzsVVr6y`dw3@C6n_#s<0i3&JBc;iN%<LAJic~ilgYzm'
    '@-Ue^OePPL$-`ujpUjH&Wb!bXJWM7JlR<Yf=uQUD$>2E|JST(aWbm8}o|D0IGI&k~&&l9989XP0=M?aq0-jUAa|(D)0naJmIR!kY'
    'fZ!B%MN9$DDd0H;Jg0!?6cC&Of>S_n3J6XCvngOU1<a;^*%UCF${cSh2u=mTsUSF&x!P3loXY-*sh~R**O<yPu&E$Fm1pczVe(X-'
    'dQHVcrUo98`>g0FQ*o53<Y+26n#yj9srbuOo}^7Bn^SpGKNYP^<tf`#ayykLX;aDcRG!UGMLAQ+^i(oEl}t|~)6>ZGG%`JnOiv@z'
    ')5!ERayyM|P9vMs$mTRuHI3X(Be&DY<}@-kjf_nrE7QozG_o>{tV|;-)5yv+vNDaVOd~7P$jUUbGL5WEBP-L{cQ~DWhtuh^rqgFl'
    'r_Y*BpEaF6YdW3Pbb6`jbWhXSX*ivohSTYurqex5r+b=C_cWdEX*zxKbo!;~^vTodo~F|$Pp4m+PM<uT?rA!G@^tnqPG`U3boMJw'
    'r+b=C_cWc(cn0~KLH=ftzZv9j2Kk#o{$`NB8T83B$mR_C<Qe3427U4jGChMnc?Nl(LEdMO_Zj4U26>-B-e-{a8FbAv=$dE1f*Is}'
    '23_+Ey5<?MU<P@gL8fPr=^12t2AQ5grf1@jGx5loc;rl6aVD-f6Ca$3^UY+J<xIMZnRFL3alV;2-%Px2CjG=r{A?x;Hj@rwCZ07D'
    '&zgy6%>tKM;4%wbW`WBraGAv}j9H*G3zTMo(kyV91unC|Wfr*10*P55F^jR!V(haRdj(ZAjWR)$;!*)FX_P5O1(YhNuodh>ssO<X'
    '_P<oH<E4VGs{*VmsLT~$T|s58V0TdkyH+cx%oTK96-k}W{$z3*ei)^nr8T^Qj;w;+t`+oW738*p+*Z(^RZ#mY$a@8~zk+IC0VgWh'
    'r&GZ`oeDaE3fNOYCr|;GD&SH@{&`%COD-xhs}g2a!mLV|RSB~yVOAx~s)SjUFsl+~Rl=-Fm{kdvD&bNkT&iUER3*%+MAMb<tP*Bb'
    '!lg>sQwb+3;Y1}YsDuTTu%HqaRKkKvSWpQIDq%q-EU1J9m9U@^7F5E5N?7nLPi5066GZ8=$TZ5NQSekYjWR)$KBr8hOd%?=?pav('
    'EUbGL);$aBo`rSK<~xYwdXjc&RGK^ie>T4+ms~-TM8(~p&yx3N$$K_RE?r12e8}XYgfIDMw|GBoa+Yio?UH9!NiNDWD;tIEc^39O'
    '%agQc$<ebsM}L-#Jx5laBP-8={Bt1x9Oym=y3c{`bD;Yics>W7X;hj#C4CNbpJR9Jb0F~?NIVA;&w<2qAn_bXRKeXUxLXBERiISG'
    'Gw3RIlvnXowu-&WRdBuv&R2na706e?`6@VHMOLcFN)=hDA}dvJzKX0=v7@|-tW>cBx(WqUp@1rOjaRX2yoz1pRcNIOtyH0vDzs9C'
    'R;pk~6%46@AyqJ>3Qkm$_iFN9O>V2nZ8iC;CV$oBsG1yAlcQ>KR83Z@$wM`Hs75Q*AW;nx)gVy~64fA41Iue*c@0R^fJ6;!t%0pI'
    'AW;JnH6T#~5;g3?sNsE!8ul#Iu<O5uexincqK1B=hJK<31=N6i4anEf7u3)f)S!+U)KSCx7B#$YQG;@7P)-fXsUg!fWV(h<poYBH'
    'P~U4{K@BXJO{Qm)>Dgp+Hrbp_HfNK~*<@@s8JkU3W|NiK<Y6{>n2iEvgUf7inGG(p!DTkM%m$a);8F|AYhigUxYUA6Ex6QzOD$}z'
    'g{`&VQVTA%bicK9zqPzcP)jddOD|kYFI-FaTMNr;VR<bquZ88c<e`>4)YARd(*4%b@7B`q*3$3RlFeHB-CFwHS~}cXGF?liYsvH+'
    'vN?xr&LNv~$mSd}HiwMOA!BpM*c>u8hgF9;WNZ!@n?uItfczYgp99u&Kz9!4&H>#y;5i38=YZ!N@SFplbJ^80mt8G$+0`<a6XfP{'
    'g4|qAkeka1a)qcg?r!F?J7q5WQRcD(WiC5V=CT82F6Y9{<y^SA>_?f)ew4Yq4KbHJCv&6Z`kXk*qV{}<OD;-r$wzrylBj@7K1%oS'
    'JRjmx@_dL(F^X|%_k1|^h^XxO5Q&H=|5+ZFh$#82fKo)1|16JLL==CPzgI8+&GPry#;kunT`4Wg6r%Xw#aHd5QM{U6l8ur>?Azy9'
    'UdJAgI!?^0<5aA=A}(2mrctI471yZi*cDjE8g(7}0PEPxQOC}|I!?^0V;#DVb?7>tKh&}ET*vc=I@Y1<c>Ykwo{T#7WYn=IqmDfp'
    'b@?@`>~|?Ci|X>v6tmwYALYMGc7%2LCsf(*l191jlC6hz`6tBL?~=`X9qZS1tY6phq+%YO$2?qk9y?m+;k)zL(K;{9Z7j`b9-T)T'
    'WeT4a-{YId`K|MKb8jB!x6WfH>^yeD&SNL+Ja)p)WAE#H_&Fbb&WE4#;pcq#IUjz`hoAG|=X@ABA4bmSRMz?Mb3Xi>4?pL_&-w6k'
    'KKz^yKj*`<`S5H$Jev>C=EJl3@N7Ojn-9<C!?SvPqMkg|lZSfpP){D}3wMa7Q86p^WTl?xT=nFro*dQl)T<sxsV9H+<gcEL)swM$'
    'o@~|gWUHS1)swM$Jft2EsmDX=@sN6QTVL$?vN@_R^da%}xb<YZp4`@x&3dxgz&y19*J!{s8gPvUT%!TkXkfnCfQK~TAq{v)10K?V'
    'hcw_J4R}ZcZwoZA)4l<JX~0n$aFhn-G7b1kBe*nzOCz{6f=eT~G=fAUNHl^(BS<uYL?cKvf<z-@Z)EI^cxxj_G=fAUNHl^(6AEua'
    ';Y}#K357SI@Fo=Agu<IpcoPb5Lg7s)ya`P=q3I?(xe0|gq3|XY-h{%NP<RsxZ$ha}D76WtHlfrel-h(+n^0;qoqsc(e>0tbGo61k'
    'oqsc(e>0tbGo62PF@O1}I1gxMmwGd^f@XH9H`5t6(+fA#{WjC@Hq+rYvxB{v8ACHOhGurDH#1{sPG$@xxf>}n&CDMbFn?IU{9ys}'
    'hXu?Z7BGKU!2DqW^M?h@9~LlwASzqH{DCO{Svr3pN<J&jABggwrSk`(__JXCuz>l)g2KJr@eFJMvxx=FCKlxDSbSSnN!bEs6AM9i'
    'A?Pjy-G!jL5Of!U?n2OA2)YYFm#AzZ=n~~WOVK4tJ}aV2l>aP6mni-$KzCu`*7Mk-7lQRduwDqd3qf}w=q>`?MWDL~bQgi{BG6p~'
    'x{E+}5$G-|dU+CsSQC{k0&AlDXDQZ1$!A5ZiSnPNSQEvc<?ox1ePR*FF9P{RV7&;e7lHL6uwG2RyO?UYm>pn?*#WkgO1YRyxtMCW'
    'n2NWUzI8EGZ81Bt7E{$0Q`HtT(^yO$Tg*&jF;#6bGmXV`v5V<q7t_Tqri)!nZCuO@Wii!oF*B6K)W*fkP!>}u7gH%0GecQI#+Hz='
    'C1h*~8CycemXNU}bTdoH-xB(lC1i669m^7OyM){>A-7A&?GkdkgpOqi9m^6jy@cE@A)8Cc<`S~GglsM$n@i|)meA=eA-7A&<`VL^'
    'g#0aKPO_9|XG`hCm-0kqDSi1;I`O5<NtW^qY$<*DQu^|xJYQK#U%r%1d?`=8mh!Y^DNkFL^7LvcPp_8p^lB+jua@%kYAI{fOIf2{'
    'N(a9T%$9-KGB8^PX3M~38MrJ1mu29x3|y9h#4?ar#&f4-jA$7nTE>W$(+e-B7hX;;yqsQmIlb`mA}-lsET{WjPQSaH4tF^<ZaGzL'
    'IdyC~m1{Y*YB^o(a=O^%ta~q~i(O9N8b|R)q~u-8Xa$|X3Oa!mbOI~r1Xj=qtO#)_SwZbzLA56;TS2ua%72ztd!ppCVznpAf0kBz'
    'qWH6*zOSH{T0y6}g8IIKb?+6__Z3kx*m%Eb)~8m&vz72{B|KXR&sM^-mGEpOn5_h*mEf`xBvvx^m5hBQV_(VGS2FgMjD2M|_Utzc'
    'xwP^-NF;KIqq26HIBK8#WOfkIDk|(MD(tGjd)j4I1>TcHK}}u7dci7c>MB+UR#8(|u_myJn!1WL0iw(*>g_5jEK&TELA_l?FSUva'
    'yNX_F74>!%z0@kI?<%VADyr`)s_!bQ?<#t!Rn*&6^ir#+zN_e^R#A&rQHxjQ_c<o}?lY_M@4X~%U*w{67k)m<zkQKJ#U5;Rz>s#C'
    'G|CjBlrKS)RHrn`q@Sg4QDo(jMwvoXtYfQLlUq$yTg{r>YSzeBvqnag{qMQA4B~sL<Np_~pRH#7Y&9!pE$E>IJ+z>Q7WB}99$L^t'
    '3wmfl4=w1S1qBdgT2Md>Yh*<6PX_8BN<J&9qXl)eppF*Q(SkZ!P)7?aZ-M14u)GD9x4`liSl$B5TVQz$EN_A3EwH==mbbw2H86P%'
    'OkM+%*TB{_uyqY=T?1R!(2=cS&3Fwx*c#T1*U*uzVa<3A3Rr^zh_c^0<op^qzXr~?QW08FKr0GpMFDA4nnr;hTG2x*Gq6_F(TX}+'
    'nUA%il~%OU%IvI_O45psh%&9{s1>ac#XlKnrIndmD>JuNl+%h<TB#ka)Q(naM=Q0X6;-t|b8BVh){4ejQB^BCYDGt_=?<cJGfbv6'
    '-SHAn5pq#MW38xaE%jk7^<gcu!L?{?EgD;k#@13T)>19jqQAB1Z!P*;i~iQ~q-iZrTZl4iQPo;%$69o>79Fi+p0gHJwSiI_D7Ar0'
    '8@RNAOB=YfflC{>w1G<-xU_*w8%Pjk+CZWWe<8~LWQbB5D7Ar78z{Ab(mLE`9d5G@w^@hVtix^A;Wq1Vn|1%6tNRYHsyf#OK6B0)'
    '%AkJ9wcSK)Q2{U508JEPL=@1dj3Ocu1?eKO#2^?eq*zmEBDT;4q7*AaiX~Qh8G0E&U>J(1pkU+MYoE4%T>rUG*5RC4&-1+RdRN(N'
    'lWpdbZRV0~=8|pZl5OUaZRV0+K&iRpm${77pzz5=?g7PZ#oRNO+%uQlGnd>mm)tX#95R<2GM5}OmmD&e95R<2GM5}OmmD&e95R<2'
    'GM5}Ok32Dtc$h~#%p)G=;rV%Zejc8mhv(-p7SCfWp2t``kFj_jWAQx3;(6qkc|;W`HIJy8N36^vR^|~a^N5xCurwc*=EKr_Seg$@'
    '^I>T|EX{|d`LHw}mgd9Kd{~+fOY`9cl$sAO^T{@#=#xp#=EK>1IGYb=3s@6az?#4U)&v%?Ca{1tfd#AyEGXusEK00IEnpvZ0qar='
    '*oR%fD%Aq^VHdFKuz*#E1*|$OVAWv(s}2j;hh4x5)&f?r7O)SyfEBC-?87c#J!?U{29di-EWLmgiG{3gEo60TA*)*pS>0O5>efP5'
    'w-&OxwUE^<P}xFOw?MhJ{OT4cZY!>CfpTs6)h$qHORVrLWQAuTyH^WY?^(!t&qDUH7P8j0Fkaz_pR|rL_CnTs7UA+mxO@>VUxdpS'
    ';qpbed=V~R1iOpia}f+Kg0n@iv<Q|K!O|jFS_DgrU};g3rSu|J#TMbnML2R13@$o^!T9m2&{kHOTEzO<qImr*w3Woamt0L-jLR3}'
    '^2NA(F)m+>%NOJF#khPiE(et@#^s<~Ti)fMxUJ}NP_8ZSa!_bX=(m_X+Qq237&RB8-(p<87?&?j$B)N_X8<CN7Ngi=6kCGlm*Dv&'
    'czy|<UxMeC;Q1wZehFMJf!!tWxdaB6z}XTwTLNcG;A{z;ErGKoczy|<UxMeC;Q1x+xdc9!9KvV(xMBEY6ah<!hb6?r65?SA@vxM5'
    'SV}xBB_5U%4@-%MrNqP1V&$JjiRf6$>4v4m3aD%;u>#7q<zodDw-sXrlxxe!3MjNCPB$#Y1xs<kQgmO6?n{Z4rNqk8NWb_O(qUU~'
    'DM~Lz>7^*WjL2C=<SZj{mJvD2h@53a&N3or8Hz1Kqh+YF3>}ui{4%&+2D{5(cNy$1gWYAYy9{=h5mn2Gs%1pgGNNi3%rAraWiY?&'
    '5ayFHwu~5CMvN^Z#+DIdm8{oQGJ~#U23^UCiAqjPR5F9EWR_gXOt_M@wMyo<m7IL2WJU{0RWhTkWaYV%Icy~>&y~z*D_ME2WNodI'
    'wY5st)+$+Bt7KkW$%=I)GvP{BtSgxpSF&PV$t<~&S#l*a;YwDlE14HpvSMAyiuH1IUykm}(S12<CChQaa$K++7c6JxWI3K#&RWTG'
    '9I~9%k>&VhIeuA=UzXz+P-;1TS<VW`a#lc=<DTXCWjPL6jzgB?kmWdJISyIQ%E@w8PL|`B<v3(Ho>-12ma}rQoRyR1_+>c`S;4yE'
    '3f56paQbEi>jf)VFId63k`=5nu3+_G1?vSXI5)F`(;_Q4EwX~MF)KJ5vx2iRD~dOQm4#nVo-0|wxsnyk^jE^fN_xAJ-mav#E9vb@'
    'db^U|uB3k}>EB9D!>ptaE9t{Z`mmBdtU|w4=(ma<t)fS(=+P?ru!=scVohfit2nDzw^@a@tLXbG`o0QnSE21Hv|R-gt6*XkOsuB2'
    'tLg1(db^t5uBNxE>FsKIyPDpvrhlvH-)gj7O&?a%ht>394VBdzDyubAR%^J$ehs(Sui+N^HO1RDQmND$?yX<LP4#Q2tkzIjt)a47'
    '6LM>|(uq2_hLxc;oMu|Xeg12>V}1?qfm_2p@(~JW_CkV;eqk-Vtc91g@Uj+O*22qLcv%ZCYvE-rysTvvZY}F>YvF7yoUMhkwQ#l;'
    '&epP;wiX80!r5BZ*4Dz=S~y$BXupm-Dc2SI9+`Jt@dlP0D&A1Jj`xME<A%z0ydh*Aqy0MeN!BsiuVZIq9i#m^c1G55L*+Vds9eX`'
    'zmCy<9o6AF#`kqphwB*a*HIm=;}*(w+(o*MJ1N(37wI}`hIP~o>!=ylQ8TP#v|q<)zm7_7T{;%JJY4RWNoP^`fzmt*e_1$TnnQJh'
    '$s&`i=f<A(jAQG$m1jLWh3m<f>)8)jPySrbe!zO(c(k5(Vy$Pjem%Q^>shT|&uaa8*5}vr-m4AtZv$h%270@J-fp0`8|du@db@$%'
    'ZlJdt=<NpfCN|L94fJ*cz1=`>H_+QEV!Dc$t|F$Zi0M4a6i_k3tBCL_ZltXu-m8fBD(<JPBKoU{{wgZ}Dsn*;xuA-9Koyyxip)?&'
    'W~d@FRFN5~$P87?1FDz@RFNmD$P887R$IkwwN>PaDl$VAxuA+%P(?1NA{SJV3#!NkRq=X3^tXgdz|vK@)q@cIsVpjFhAMKwM(%Li'
    'NUUt+zO{|S%0^;kBeAlPSlLLdY$R4T5-S^d^V>$=q_>ec+Q|OjMj~e;k+YG=*+^xzkvQ7OO?Ml~A)DZ36HIJ^iA^xE2_`nd#3q>7'
    '1QVO+`zHFniHx}kCN_~#Ho?m#c-aImo8V;=yljG(P4KcA_iTox&CEhJlXo}ctj+Mb89q0|=Vtia44<3fb2EHy##x);b2B^co8faa'
    '`Fb;aZidgz@VOa2H^b*Au=EMMd;$}nz{Dpo@d-?P0u!IW#3wNE34Q;B-hM)FKfz0%(DzU1`zQ4M6Z-xMecwXOzJ;273pM)|YW6ME'
    '>|3bWw@|ZhDUNYDRIK2)@J6mJ)bm?-Bi9xx_$^fMTd3f-<i?zc-N-&$sOPs(&u`()T3eU{ZK0mu!n?G#P|t6P>-o~`Jy@wNRQFq9'
    'cPs2}h25>NyA^h~!tPes-3q%~VRtL+ZiU^gu)CGH(^gI}Y-J|3l@knGQDrNtY(<r=sInDRwsL}DD;jNO&b1ZAwxZEiPB(022DTOb'
    'wxZuw^xKMl+o<HWvBJ8I71nK3dE2P+wo%D#qgvZWMYfHqYa5l-HfpJD)Kc46Z{0>^wT;SZ8*{F0)Kc4+b8Vxt+Qyt~8@1Fn=3LvT'
    'thO=d+D4tVjXG-^b=EfOtZmd;+o-d)G3VMwWwnht*EZ^`ZOpl<QMwwXt5LcdrK?f8nhL%e-K(kDt8qa!ReCj^sHQHj#v#>I;??-2'
    '8oyNImumb{jbEzqOEr~vHI;ZZ?y1Hv)l}luRN~dRry9Rh<B)0`QjJ5ZaY!`|sm3AIRN~cC;??-28i#D>%_7@*v&eQFvK@zP$06Hs'
    '$aXxj9T#jz_w6XXoi~JR=M5p-QF=Q{Z%66vD7_t}x04yRqwRJw!*-P3PG;DSw%f@J+fjNunPEHc3)#*aLbjvrcC_72^lwMa?L`0f'
    'L$pmse+^34pmYsN*PwI_O4p!t4Y{BO-D}7NHMpRLTu_52YRCmOIHZPLP=jA;@JkJTslhKb_@xHF)ZmvIGD8iSp$7NV;FlUQLk*ds'
    '2KUt9ml_;WgF|X?NDU6DA^K~G{u=yJgF|*OliI;u>N}V*?BGuA9n7S5a3}f>W)nM@P3+)??H$Y}b})a~!A<8oxQ%`XH*D`<_hSdQ'
    'lJDSF@*UhtzJpuIcW^8D4)(xyuxqk|U6UQmJ9aQ@-3fy`VQ?ob?S!SBu(T7FcEZw5c-aXrJGrHQCoJt`S7;}_-AQkE(%YT%b|<~v'
    'g_m~WrCl(w3nq3kW8cNT;V$N>yVyJ1g$H-x!CkPs3wC$G?k?Ef1-rZO;4awR#SY^x*xkhr+%9$)cd^5`iyg*Ycy|}x-Gz5|;oV($'
    'cNc2zLd{*MxeGOSqtR|O+Kmpo(P1}S?}qE$aJ?I@cf<8=*xe1EyWw*;-rY@achlS5^maGB{ghejr_5SEW!Cy>k(VfAe#*@BQ|6+d'
    'GW-0LdE=+d8$V^<_$f2RPnjEj$`0J8%-=s{ZulvCn4cC;fJGF3%53mc=6?Z&&z8nx_#SxK1222vWe>dUftNk-vIk!FFc06u%zF=<'
    '?SZpBaJC1|_Q2U5=F@v%a1WgAfu%jnr}x0w9yr?rXP?2@XK?lzoP7popK<Q+GoHTq43<8FrO#mLGg$fzmOg`*&*0@Vc=-$_K7)zR'
    'cv9js&JTVD6Q6Tt_H)k6e$JWM&y!4)e$FY`&p8+SIVWL3WuJ2r7L;qtpM(X4w!|sR&pEsNIp_61=al8=++y)LXIMYyeB>8+;tM?S'
    '1)lf<PkezVzM!{X(7!L}(HHdS3wrbgJ^F$keL;`Dzy)7$iu4O~{{r2=IHd2%^PgXE;&U%+5PK72PDyHSV$6wAVy3Z|UBtc2H1@J@'
    'xR;s6UUmxiGSk@0-r!zl8hhCd+{>!NUiSY$(O;dMO@QLI;@n~{bJ4xbCiXHH-OJo!FLTko%qI3S7v0O;VlQ*iy{tj(Wes94YY=-`'
    'gV@U~WG}Ojz06bhGVj>SJasR#kiE=P_oicGg?|^3pGEP%%cJbSOQmus{&$hQ`*7AioV5>U?c;>$KAz3p$0^c%JdL{#_w2(x`*6=b'
    '+_Mk&?87~v=+~3(0mW@a_w2(x`*6=b+_Mk&?880#aKS!Yun!mP!v*^|Q@W2+$NM-%x{p)G`#4j&k5k9{aMnJYwU1Mz`#5#Hk29tF'
    'ICZ=aNAAN}`*7AioV5>UeaY#}FR7Ei<Z1XXsfE8}@9aye-!Iua`;uDtOZLvbWbf=t_F+M(FWEZ-MQzEQv@h97`;wisFWEc$lAYJD'
    'VB#y7_zEVzV#e?lynF>OU%|^)@bVSBd<8FG!OK_dB7OxEpy)44GVv8md<7F<!Nh*@%YO39e)3BmW%4L7j_qe0+t2#henz$ZjB5K?'
    'P20~Hx1TX?KWl6I$yxi!S^HUO+fN4DPX^o1y4!y8*?#gFDC&DMpMm1GVm{l?O51)`+V+#(_LI-{v(mPomA3tijr$o5_mlbdllk_O'
    '`Sz3f_LHUdlcn~v3b&tCxc!WV`x*cC$IsHl|1Oenf9}beke5<fRLEKT$x;V!<N+Lc07o9ckp~$64lw>5;CYJ!jD`mo4G-{y#Q}VF'
    '0G}PeX9w`v0ep4<pB=zw2k;pv`a6?81I2AcpB=zw2k_Yee0Bhz9l$RK@XG=Gasa;^V5B_2(-#ML`r-iN<^e{^1Gw%0t~<cf7YBIy'
    ';sE330Y=ILxb6V1JAmsB;JU9_=lhxw;cG^OuNe`(W(@e6G2m;)fUg+?zGe*gnla#OPS||S`6W>5YetK&Ie`L-KA9XJzGi&*n(^Ul'
    'R+PSGwD_8}(XSarzk#!F;OrYX`v%UwfwOPm>>D`y2F|{Lvu|Jtl==pizM<9t#h)xP2+FnPM_*9XmSp!E*!>1}zk%IvVD}r?{RVcw'
    '#h>58^|x^SEnI)gI`p^HFW;iWx9IRKI(&-`-=f2}=<qGx{TAlG<#gD$a1Ba*OWpG=?0yTo-@@*<u=_3Seg|jY!P$3k_8lyJ2TR|<'
    '(s!`*9V~qZOW(oLckuEZOn_3~!NhlX5EOkf$<lYQ^c^gH2TR|<()X<Je9sEc_pI=I&kE1?#gRFS66>blbJFR1R#Cs_q|^7TseaE%'
    'r|(%c`kqyz?^!kao)b&ov!?nzYlq)+D(QRHp}%KM_50$J$kG4uJu6Dzb4KZVR#?C1jMDe4w|*b5HkD>?eNKPR+S5UFIEW4h(cvIE'
    '97KnM=x`7n4x+<BbU26(2hrgmYq$qFadwau-GiJsJBWS<(eEJo9Ynu_=y#A4X9rR9AS=NK(e@x}9z@N9sCkgnXa`v{K8Vr>QTiZC'
    'A4KVcD18v6OEO8NV^mN&i}FerP^@hpr3$FH!kR~^JW8y==TWMFifZOjs)!0|=20q#l4{1Npk@~3)r?R=u{_EumPL8RN-{}R0xGIf'
    'l1ZwPMR`>sl(+#Yi}LIG0Tpiv$fEpeZ-f%6WKmv~(xfV>(xfUmlwb2NO{x;spA&2TrAg+ak0;msL1m>$2GgKiTYk+S6xtFi<N*~|'
    '$YWHvSs{<I>*ZOLUoS7sByX`O%_MgKN;Ap(60#`2CZ58(DZHD)yD7Yz!n-NFo5H&(SW3Z53MNu8k%Ea7Or&5U1rsSem`d^zqoN~I'
    'NtPm%^jQj@rSMq_pQT_obqKr3`zNv}zyA<W@&1V{%I`*`@opOLrtxkX@22r?8t<m@E~qSxcR{(fymvvNEumOCle`rqjecqLOQTpC'
    '@22r?I+MKlBMsMSxX$3@3{KAA<P1*E;N%QW&fw$>oMm7s11}kP$-qknUNZ2KftL(U&fw$>PR`)u3{KAA<P1*E;N%QkXW%+>2-nG5'
    'Rx-FegUd6xJcG;2aCsRnFT>?!xIB+C1yuBW9%b?<5dnFW$)RLCfXd2<2T-mp9}l3=mbf#g3>TE)f--b3L-#V`p^SJa%Ovl`DMPU`'
    '6e~lqT0}=JqN5hkQH$uPMRe4H`C7zEEn=k>I@E&sT5w$pc5A_BE%>YjpS9q#7JSx%&sxM$E#jyaaa4;qszn^tB93YiN41EfT4+=Y'
    'jcTD$twS_QMpZ4MsuodIi>RtaRMpNTS6^#qlB=%~N}Q*SQQ<so7UlN?0xGWg$EdKbUptdrQ>~pzuAA1*B-chGlsM6vN7>a-P%5C}'
    'YG@YacM$_Bu774xeit!Dh1Jk3%I_l9&Lr2_vnam@T|1Lpb+4UC?m^eiB-d19R9I83ok^~##;CBS8ll8$Xp9Q0p#c?l{Ay>CtL|Bp'
    '--E85Nv^@y&LsDsYiE+{pIMaODXg7Iu7=jmBzFqy;E6hTqE05c>Rtzj)WIQjGRal<I=G+?E~tYG>fnMpxB!%@gA3~5f;zaM4lbyJ'
    '3+mv4I;dF(HS3^e9n=h{xI&&q`Mu<TifiIol;2B^QDKEVi}HKPb#O=>91>7*O+1V8d&w~>tdM6>elNKW&Z>h$>fn$%IHV2^sf$DE'
    ';*h$T<StEJ98wpD)Fp@HQKo>386}T0MO4Tyd6dbcgwOIQQ$z*V<xwVwk{+y!2kYWNP^vB-45+v-lSTP`nYuW#E*`9#N$&sE%_R5#'
    '>XMi0l8Nf#*1EX0E^e)hTkGPix;U$DCb|DtH<R4|t4k)TOYW(gN$$kd%_MhX>f*DyIIA2lmE)yyyi`u^DbFPL_{#BFIX){V6P0I@'
    'JAUQ(r5wMM<Ck*$QjTBB@k=>=0j0|EOF4ci$1mmhr5wMMqkB2Jm!o?*x|frs0xIs~Wl??~ubiA!PL?XiJ>|G3pyEDW7UlQx%E?*f'
    'WT|r8Q;vJeaZfq!sh3IaljKn<f$}>5^)ksFfO?ta$?$ra<eGoIOmdaKUM9J&UoVq9O`k{ECl~5vlBd4|DxUtXmr0&{k5S>|dluzS'
    'zSqkn&w>Y3JPRJ9!ddWondG{Dy-ad9=`i|!7=1sCz8^;452Npg(f7mX?P2sbkFra0htc;e%Aa*VjQ$-){|=*nhta>o=-=V!emJ@x'
    'PTvow?}yX(!!ya<vOG#9P<~hF@J#Y)fy3eKa5y_0&JM>fhr`+7ndH+Khr`+7ndH*~hi8&cU&N^J^hFlspT0O8pB;|R4##JQqr>6o'
    'a5y>~jt)n_?h&wi1neFGgGa#N5iocJ3?2c4N5I(;uyh109f8k|pnpfuza!}15%ll>#Un|1y?EU#6`}HwGfUzV=2=uP>TMWj3Mie9'
    '2B8?$3!_DZ;(r&iR``;D;vuzOJOL{SC`xDb!VEK$MdhW@FN6tM9)-pD&{ijmu%RuQ4n`=*7f{?5#(?sAnULtCUx?FZ_=U(8|1X}I'
    '#=j8%ySS_i-x;AF#B=+&f6*s@KyQCQZ+}2<e?V`4KyL#Il|l3++3!sB{Ri><J@<E(`~W6?024oei66kk59s?3=|hC#?SZi1m`=qg'
    'vPf9P$)aM9en^jgNRNI<AAZPR{X_ohAM#iKkiQy~`XPPzA$|CtBJ+_A1B!mWP66fq>hSabQ~0aH&lgbml1v_@;^o2rDX0>)mE}>`'
    'C&{9qN~$a!|3bD8p?_s1pv?c|{_1pCSt|j>ZPDOcFT2r|M`6)BEy{f|Jem;-`WV#--x4`l6n(NzX}n7m{ne>dK=IyBCR|V(qfnS+'
    'vcFfScIZ>+U*M$>0VSbFb%TI)3aEDO?~K1CCO-TvQFRlcFa?U(&3#LGY0Pf8v?E6K!p?an`z>MNq+Zwu34d8Y;aj3lrjATRPD$C3'
    'Mg6iUq2H0{cO?29iDE|<BBwO|mVzqLe@7N|$e~>SqI7;_k@@JqBa6&OS@Fms*U`T`60Wl-8Zg41LX3*cXHjSiiT6mD&!T#D<GqLo'
    'C3Q%kR2CIgNuX?7UZYg_g`{Ff78Q#+aU}X3S=28T|9V2rBa3RLN|Pv)Lj`RUDEqhMl}-gFlDZ#R)IC+2M3D=Q$^<%dzh0U}x!(&Y'
    '5#dJ>;YY<eE6z*NFC3N6V4;68%H^zx-J^;*D_vSdal9Wz^dD8s$*Jrw6r=yBVookCqErqAX>+|T$)ixsr*kOR+kg^z;wUo1QAGby'
    'MEFrS<S0CG6sjBzXGg=?(Ztcw#L>|(aWqkNG)x>#-;X8_f-*;w2SIULG4p|PZTZZXNAcsZqU<LNSrHVqB{@49&W<J?j>hFjAHrwS'
    't;dkFjv;3q1G~q-?lJIr3|Z<JveYqTsbk1X$B>tfDKZiL<S}HaW9a)aWRzoI;utc@F=UNnVCfh#!!dAn44fT9W;llEKL$RJCEkz4'
    'yT{_)V~Ox%iRojB>0@#7vBdPTIQdv&`dEB@EKz(cQJhDq_=wH1c>Y*iek{H|7VjR5TaQJtW6|hX*!|x;XYqc={}yVus3=PPZ^DBm'
    'ng30Aur!@VsbX8;CEgawqf`#%dK-SBB#+|rFQQD0qFOO<mTSwSsIBObk^&0HYe1<SivN}n9eEUd4T}EmAJO+1#g%Gs>yKdKM};aj'
    'xb8>r@*{Zp5xo2eUVa2GKZ2JZ<$4=NxFX6j0gApe$;6Lf;z#uTNA&&2h3E+HC;4%{xADH=j|=e-bvOOvd~c(Fmqpp$h6=ub;tAl7'
    '3-J)B|8c?B;T<GD&i5$Z4g7Io|1Y@w$Ax|L5Y#^|oCql`p!}(%Jjy;%{Nuu&Thvy191(sT5q=ys-*IHq<H)AR5#h&?TaP2ck0Yj!'
    'E6zfq(E^l-QF)y>Zqp^8xUD$Gf#SAeJ%1dd8YuV4{HS&ub>wkWj>l26A4lbQ9C_k6^2BjefX9)&kE6;vj_iFL)!K1n=;Jcw@ltR!'
    '#f!Nv4+{--(qW09ETF({I9gCrR-du4K4W8jw5^Y}_0hIIYSw3@tY1_t%7pcc8bxDXeMZsxRQL56Me8$))<=i>)bsUGr9Sn1eN?GW'
    'JzpP<>NEP*N3r^hzV)f+>!W6UM&|lxTc3KqK1$bT)UJ>2^{LtG<AVB(+V%0o@zm_cGlm~egdb0YA5YDGJR|z?)a=JIz8}x{emv2C'
    'JmdTEME~)O@5hr1j;Cfnp3(kzM*HK*6UUPojwcr!PrM(G3yw$k<B6){iK^p?suSSz1o%9GI68qiIsukWAgWG)r4!)g1ac%Oa{@UM'
    'lxwROPSZyNDJX6$=1)-ER?L{7Tw6Y4p1?c+6n!$u^$Bo&0<m%e5pV*&J^@uuK$R0v<wSDbiR8KyQRPHbIT0OBB)gqRb~};mc4Cpw'
    '=xa|T*PTdqJCW>mB6EZjVd+Hj(ur_(B6;aVa?gqIc_R7cMA$u%9C9LDpG4L;374OQ%TFRtoJ3|giOg^ko<E7qa1x$BiOg^k5pWW@'
    ';3RUvNmTwP5gjKH4<``;C*k>%aQR6%`6M(t2~|$QpC{qZlkn%s)X67P8J|ood@{B0$<)FpQwyI=EqpSy@X5>(K$(-Nj6tC-bRzCU'
    '+*U-{w&;_gN4d5<irT_fR`khKIJlWWsT>Nt#E1J5C>5hbC4MrM_{q#kPNptDnY#RB<|IE!aGfswNrLNi>L&@VQ<<M6xK5{klHfYm'
    'mg72A_LBtH0TsDUm;5BbZbp>(NrK&6TONhB0=scr5oOzQ?B?3?C~7Nmol2rq4&}HGe`k^F7!|mVKUv@!l**wT*SUX};~Erw=PCI5'
    '6y|@Y;PO+L|DA&8Pr>u2;Q3SV{3&?;6g+<l^S@JYIVk$hq?18WThhs=;N4Sj>nXVP6#RJ#{yY^&o|<4OMhSnOnqVo5if%m>x1Ney'
    'PsOdL;?`4f>!}HriYV((Q1qQi4}zk$qz6yMb*JL9Q}NlUIO|lLby}vhPM|5AVNIt33dDpHFX_@4Mcob0;G|1VV{|%=(djg1Hm5Q6'
    'pT^jK8e{)y)I^}nX{?)q;<n;^^E4`?({d|Hk>TUNI=MCqioPW|>p6{i&S}g(Ph*~Q8l%%`j83O9Upb8`Ax7E1EM_-3LphC_;WXB|'
    'PGe4T8Wlv0;_nRlH9*ZQs#iBv7F^x{ZL=t}h3IHNCD(vTt^wLMK-&gr+W>7FP}en}T5G`iZUg424XE836xEErrUC1_4bZOvv(^Tv'
    '*??JV1JrE5thE8!HlR9efYJ@94jV9QZGa0JP&qch6Ag-<NTrh~)+jlnZGc}IP;oZEJq>VA1J<D%Fxzc_vl>vTHo#{MiatxFlPL08'
    'LtNJopEV?hG$e;KB!@((yiWY@!Xq#-ivL|y=Y@Zl@L)qc*bomk#DfjVFQ81roCm|HwM<DvvJEKyWHH+`B-=D3+cd<H4e?+@GD<@{'
    '*bvt>#Agk2=Pu&MYDyd8tcG~0A?|62UmD_&hB%}lE@+7E4N<xgN;e|EG(z`A<d;U|mqz55M(CbJ;opS^(i)+ABXn<s?v2pB5xJ)k'
    'xu;Q4_voXI$V83EM2*NqjmSieP`VMhrxCh0BKI^3y4TGzk;$Th3mTD$0;-#HYxa|MbB>HrIFJ?E;yz?ggrwunH^NJe$Y70dRwFW4'
    'qoU8^Ur4&H5!tN~9&AK*YlI^kk=+{M&qidoM!2;R*{u=YZG?9lk=+`R-5TNRMr5}}xV#bBtr4C-o&AT?*?%~l{fE=pe>k1}htt`A'
    'IK41OFQCG1#OZ}OdKM-3CQfH>;&k>VPG@i8^un`AAxoXkPQ~f$RGeOTIw;I0PG_g${}O#K%lu!W?=dR$y)6BIiN0r1zVBtJ|4Z~e'
    'Q~H02zUNS`@0pVSOY}XUV&BWk{x8w@7!~>+f3nc`9Ln`QT|lAlp{>~4bZKMqSz|I-V@9sVj9iTwxf+wf8Z&Y=CWAF5gEc0DH70{K'
    '&gHBy?FiqJ9LGSJ#*AZ)8LJvIRyAg<YD@-eOwMY|Sk;&;)tLO!n2gdmcVaNiWC9b(9MYJq(U?5Zn9R_aT+o>4Z%j-#CW;#qw~aH='
    'uSGpdXR?1wgrXirC}ODzx;J4QYk~`!Fpf209BaZj)&v(cVH|6M3!319Cb*ypE@;9y)}-i(($I(GsMds0tqJ2;6UMP7jAKo3K@-NY'
    'CU~L=<5&~Mu_idA3FBB3#<3=hTuty&6UM40II9U`Rg<F6;_pnlt_kB<6Fk_2ajXfBY{EF!1b;SR9BYDGn=p<w!MjZu$C}{eCX7{0'
    '@O2Z$swTL+31d|gJl_P*XHmVn>9WX@rDrgXoxwPE2IJTnjALgoj-A0cb_V0v8H{6RFpizUICci(*cpstXB3{X4R^Pn!KiiyquLpa'
    'V`miBg-heVCBH6Q8vlC!dD!SXOV41$JA)DLOh&vj8S&0!#5<D_?@UI#Ga2#DWW+m@5${Y!yfYc`&Sb<plM(OC1WV}x%8q|$GX9;J'
    ';3fQek(cnvA}{IEGZ`Dt!Y^mxm$M2_O@(Vt&cZ!s;hwW_&sn(VEZlPz?l}whoK<+*DmdgUymS^`I;-&XcG#&n3um2$v(CaxXW^x@'
    '@X}d$DMImsQsKUpxGg*q5dU6i%Rhx3_H)j{b!XwavvA$nxbAFRcXop7O!#ENgJ<Kxv+>~Bc<^jIcs3q98xNkH;5wkBBhSW>XD7H$'
    'mz<41&&Ho;<H)md<k>j#>;$`UTY=rsR%AC_dN$rY8}FV&wRR5G+BuBH=P(wZ!&rO{WAQoc34=1{<aWJM@q_y3utN;WeX?HmEg*4Q'
    'v91HfpDb2#=TOO=!>D}@<McVyZs#yEN2t6sSEIzAjD?8rZHhjb9E;Ck^gSmNKS&pkqT%1gLwM*z<nnVEMbBZ}JcrTn9LB$M81c?w'
    'j5~)tzH`{)JBK~Krc`82smPk5bW@aWiqcI{x+zsxQ+A}A7L|@FtETKvH!W%#)mcrc&ze$^HKihJikeNS!J49NQ);lLXxo&kt0_un'
    'QMMWlD5-Q)s;;K!-ju4VY0(9#_*)X5Xj=3{)TO34q$yQbQ~c7Ds;epPX-Z|)6fZTUvTBO6no?Oc#b-^ateWDwW@L?KWQ}HcsTp2s'
    'hL@V*rDi$zq~c4*nvp|5nP%jWX5@)x<Oxvx?}~Y%8F``^&T592nvo}(;iYD{rx|&o8SZI@Uz+8f9}7<~r%RjRkY;$I87^ps?#)oT'
    '8QL~O&1Q$_7Y(TKU!DE+2*rPOV7@tdqB(h@IodWy+vaH79BrGECz=<PE)Bnz%o@$f8qLWQ&B+tZ$rH`V6U|YxIeDTv+BPRoG)LR!'
    '<ca1e-JCqp9HpC+Cz_*sbMi#<q6?xPHpdgq$sx^gNON*XbNter9MT;3G$)5N$4kx0A<c1Cb8<*?eAb*C(j3<{Cx<l0gU#_^76m@T'
    '{Q~EbU(O}JoQvzu#dYW6x^u}Ppv<{c9-v%XKBJt=Ni|UX$zrwv#cjp>axM-z7f+mve&?dfxo~|h44%u_e=cMHxs3hi5!2@p)91nG'
    'dGL82e4a-XpGVxD$M}98aeE%8(as}^&m(TngQfF`qx0bGJmTm);^92_JP*&G2fOFt>+|6HJiL1z%>R^gB|qgP$xk^u@>9-^{FKuo'
    'KjnPLPje@1QsLq10?M9r0%d;6`4CXlmOLNwQ%*Yll+z+V<)qV3IXm)GPK*4E^C3UuM99xL1M)M@fc%V8A3x)q$IlYIEu!pMBT(jN'
    'obv!hZOL;UKjW;?&p7q*GtL_Qj58oV<J8CbXnQ_qhR#Rn^EoqgKDwWe?&qWX`RIN==Yr111?T5_8{fQIKv~^E(eEX7KOd#fN89t!'
    '_5!rMfU`drp!5Zt{kZ_$FF^MT(ES2*zku^S7vO>m61^>=tnQ%b_ma9_fYKMB?FDGtf^nq<<4Ox^n-*ln7G%X1WW^TLtu3fcTQHKe'
    'V5g!5V+SbHf=aaoBS{Ntn-)|vEvQsmP|dWUerZ9a+Jd~>f=t_js-y*VNDDG;3s#p~P<gZ<@3x@2XhGg>K?Tu*yxW3R+ZOCpw4k17'
    'K~39|@vkN0UrTgviS8}Yy(PN0WHf9^P1}+xwk4xsOZFyOG8(p|rftdC*b?1aQq#7?1udy*TeAPq5>K?G!fna^LreA_TH>CTRKG28'
    'PfJGamUyWpqjpQG-<J5SCDm_BT-TD(z9k-P$$m#m9NCh}xF!B<NtMtNx3;7*Zi#nWQbDxD$t|gjTjJ}MR2MCAc}ra0lD&zRxV$A*'
    '^Uw3o*~CkNKQCnVuz2|M{IfLi66DVdnLR8z{yZN6VZ2TKybuB5-lzgfhm`X3LS~QJN`9V?fcV`yKhHlQ6Mnty=Y^~v{dz$0o?AS;'
    'hfl`)YT1?NJj$*-|2!TM>V!ST?6>5`hg9}k%EQI=ak-mAq54gg<l5rz3^#}VJls(pe`jg@m*r9TJ1>N#3t{O(Sh^6FE`+5EVd+9x'
    'x)7Ewgry5%=|Wh#5SH>NzA-#TMV2mvr3+!{LRh*GmM(;)3*qG#+)VR}L{==#{DRT`7mW75NMyzAzsqOEfRgvP{34g@;=-eVvbVbY'
    'BA0tg<GB4rF85@wi2X$_qm;(gOai4qnIg*G(G#Qc5OL{9iUdl5GI<o@FP!vEpcE*RMdh{QtWgqpDWDW6lSgq5DM=+!3Y3Xa;x3_I'
    'aF@_8irFUndxcB{%H&a;d$PY*$V;I3_p<ZGu<aZ4%cD#lg<Ipoo_?x`GC36A3>S9z6DX7r7vY|ZxCQ7UZUMT8TYxU&UZab+$><{7'
    'a}n;j2=`pXoj@1irHi=J=^~tU5jO-~gnKSRm5Wg2A~?GUmM(&qR@|J_3YJ<CW37m>R>W8<Vyso+=A_c>cP1jP756B$g27fW*a`+)'
    '!AmP5t`#xXil}Nu9JL~jS`j&|h@4i$N-JWe717a(2xx`pTjBXuxV#lEZ-rv5aCs~A3n;#Ivn&;}n@5>EDnvjll)f0HFGlH$iHD1c'
    'hl`1ai;0Jexg+ahqT^zez8Ix1M(K-D`eI_`VsyWlc(@qOE{3Ix;pJkOXblssnMJl{7TKBzXiWsPCIVXH`PTHkHGOYQ-$AL?FwvU6'
    'x5o3W@qBAM-x|-i#`CT5d}}=48qc@J^R4lGYdqf?&$q_&t?_*8OkAXA=h~?v%H&ag=AA&994f|2Yjkf-JhVplOHld}?uEOAd*Lo2'
    '0xlr}E+GOg!Sk1(^d%^L2}*-fm!R||cpemeGU<X#h=5CA@Dez?1ePv=mrGe^xRiB<OPOz8%6#)u=9`x?-@KI7Y*6M>Rvj*7Z5x#P'
    'WPU~BQq~|q(I=BL#ehQm$1}`;60^ZeSxX40cKpexEp;h#!%Gv9lWWVxN@<Mp(Gh;37!RdcRG39x%53mb=6{zmJG+$m*rf@V2X>RI'
    '=a(i%gzyW=we(9_OK-zkLL1f++MsP4v~7d7ZP2z2YYA;wS#QHyLL1iE+px0GhP8w?=+}msejC)xqTG5xKnZQzFw<{?wpkSZU3iT|'
    '8<cLtDnOe=?VbB%!3Av+)pltTWwIz=Ux&Xe>5w*win=t3GC5T6OB+@l+OV?F1~0W?WuXnuYQri(8+_J=Re(0Qt_`khgU{L|>WPxF'
    'wq%XAWR12st1ZrIi?iC|thTI9wk3yvGHuBrZOIdD$rGUH-z9z47H74^OKr&$ZShju#CV%7psapv@k?7A(iTs&#RY9~L0i_B+M;_~'
    'lx~Z*ZBer=YPLnqwye#xWd$;zY;QyV+L1%rkwe;{bUT!8htlm(x*a*B9qW<p$SCc|DDB80?Z_eR(6${pq#a7PBZss@_jcrvcIe)Y'
    '9MUc^w@)Wgriij?wj;l^Bfqr6FYU-L?Ql;!@=H6s)Q<ep4rjH)S?$O#?O4@phwIvrd)nc_cI2LRII<nNryc%mNA78dTifB*cDS`2'
    'xu+f8ZO6J|yF<JiP*5y{@nz(!%g9-m;oZyd?qzuQGV&5Aa~ahPDA$(HQkSt)4~joo%wV9XE$OVwaL8roei^!7hDMjc{ADnI8MVe`'
    '=x`ae#%0tRmy;(hCr?}syO+c6<*<7>nc;GB!R6Ewmy-)FXW#yEGQ;I?b~({_IT3d`d|pmeT@JgK!|vro)#XIT<uHFa5pX#=T#gQx'
    '!~Eq$z%SX`{Uy7(zhpP}m+a>Lk{#P$vTqN{{F41!P}EjrqNISbyScw)7yp+zUP6`%zn<Lb{Uv+)zhvL{m+brgGBHyOy)Cj7`WGkY'
    '-1+M(n7?1a9Q_LB=vT1sdj)&DSFpnm%3Q%tFDPnD&Wo>L-}egk`>#mw5`I0oCwv9F|5q?)zJeX%E0{rF!Mym21TX2*EAh*foCUZN'
    '_gsm4uEaf8;+`wn@4phifTHhA`sGUeawQJA5{F!gC$7X3SK^5)6YB+8RCLIdI3z~#Umf<&uEH-@vEFkP?zsy0T!nkC!aY}UGT<uw'
    '0*byf>6feU%T+k!DjaeZp12B6T!kmDVjblw9C8&7xhla+y0kqbWqU@-_SAgs$?WaP?Cr_y?WykDQ^B`qY;4cjgZ7Mupy(HpHD7zG'
    'y!O;}?WyP6Q`fbpc5BaQ(VqIOJ>x@rYOwZ<5A7Kr+EZDzr<Q8Z_|TqR;PzBc?HMiFv-8@X^9Ai0N!l}#w5NJ%Pvzg9>ZyVey@C<F'
    '0vA-^f(l$vfeR`a-z%v6E2#A=7~d;6iBQ4#Ucsq>3OrH4JfMP80~PqCf>}WYCkiU?QU!B_3cOUo9HD|aLIpmnz-JXyB^AsOD)3+h'
    '6-xz<tYD5%fj=v#W-4%N1#YdNnyFxpP=S*xm?Ko+>k6u%3S3^n$%hI&U%~vLf(WRfda58EDu{;)P9jtg4;92i1(j6=(NV$NqT-O~'
    'NX{*;W;gz7cH^&RH~wmN<F95n{%UsPuVy#?YIfYO=3K(n?6_aej{DW@xL?hV`_=5YU(JsD)$vG@+x<^pT^Lu=agWO5SE_{_zR;sQ'
    'yXm+O<+ZcF9`wArFv^583jt++J*wezDExZ5B-a-IdUz!6YEDHIQ5qC@xd!I1f%$7-{u-FS2IjAU`D<YQ8koO^vkuq5{53Ft4a{Ey'
    '^Vh)qH86h-%wGfZ*TDQWFn<lqUjy^k!2C5Ze+|rE1J~EUbq96|JFp|xfqJO}^->4+ggdYc+@UxIMDw~1?3#37*Q5ixUL81F(Sbd%'
    '4(yJ1U`MP2XDd3eKh}Z$u@0QA=)i7S2X@OkaJHfYduJWkJL|yNiVjqO9oWV1z`j}sPE&MXm#qW4Y#lgF(ScgA0~KHgc7-~y&)k6>'
    ')DG+=cVGwgT0C(rduP|OcXlm%XV<cOd@cLM*W!t5@x--w;#zjgu0{82;qzL0doBIDmL7Fvr?4aa>xkz&;`xqvz9XLR$ewUVBA_Gt'
    'h8^j9NBZ88zIP-ZIuZdL@q9;I-Vv8~#Md41bw`}s5hr)VyB%?BNBr3le|E%?9dTqwH0p>WJEB-ec6vLqquCL+c0}9j(DpjCy$<hQ'
    'hj*{TyVv2}>(~Xp4kurSw%4KUb!dAX+FpmRuY;HCVB$LZejUB-L~lDW+wH_`w-dhZgs(f{>rObi6aDK%|3Ilu^tKbd1x24s`nnUo'
    '?u4&9;p<NLx)Z+cgs(f{>rVK(6Ta?*uRG!EPWZYLzV5_4yc2u#otTw(VyC_n@z4p~JK_0G=zcv)U(e}=>p9(UJubf<mtT*|ugBNd'
    'qxAJC4N6^)($}LjDE?&8<)El7$=UU=bUnOW4-=hXqB9ZR8JBm)<(+YPXR>!^Jl~n@-8sigc4pccmO8^yXPD@W%RA%p&bYiYF7J%X'
    'JLB@sxV$qi?~Kbk<MPh9yfZHEjLSRY^3J%mGpckZdv_*hb;ik^5794~y*rc7Za~``(Dnv=eFMI}0bk!h_Pzm^-$3@h0c~$U+Z)jK'
    '2DH5aU*7;PH^9UV^!)~U+lAhCA$xZrdw0RtUGQ}meBA{nccFivR2O>Nh2Da~Clh@KMQur!cfsXdaCsM8-UXL;!R1|Wc^6#X1($ch'
    '<y~-j7hK*2mv_PCUC8BK$V*+w<z2{9U5Jh@xS$IW&;=L#3f+H2F8>v|{8xDXS9tzcc>Y(o{8#7>O8pAme}(R#@X3Vkpln+q0zgq)'
    'lEGiW*{@*fSMYKpx8&qerico6=HyYPfQmQh+{g_&d6X%%#VnPCnQ$IuawtFV53dluG57RSCSIQ?qOe|fWA0g~bogf_d6d0Rr-*`n'
    'Hx^b8!YWP?g_XS<b9)74;YG(~H|ACd@+f=%Sy|Y5P2ZS%Iw%uvWY3}a7otRQWA0Y7=sTmpy0O4+Y25ehntxe*xzCNcRe%DDZ|q6M'
    'H}(WnJMK{k+#56XN^8e&R?hy_+53A^@$E=A=I-w)jc-S~F?WAY_W9JC3i_2rirrLDEadN-ifc2`e>WA^W}?6Irh+QrFT1IrLs*Tu'
    '2_0^N`I}(=Cb+(-z;0M^xv9Wz7A09KqI4GJI7`QWOOnBx3Jj(}xwZtKMU>8=BD+PDj#0fh8Kl$M-X@v9DP}%?CwZo%^d@w;Db^w4'
    'DZYv7CRFK49Cam*x)MiSiKDKC)wHmt)Rm~}N>p_vs=5+YU5To$L{-<En(0i~Wax^vU5T--DBTrpyAnrTiKDK>QCH%qD{<77$mv>G'
    'cPowio^(i8T+kKWyT(e_$=*p>+7%acjg=0)4gTzk3%a6oSG4VVh?>b5>qd-qBgVQFS3{$(?MB3PBjUOdaovcxZfMjEjk=*qH&p3H'
    '#C0R$y1{M{r3)y}bvL518`0Pe9l8;X-B6_)suWSWfbtr3BT~DeSP`WQD6d~PqPQDT+zoBJ5yjn5x*Jj44c%`h{%$7zZYKV2F05@w'
    'D4j={0xHJl&BW%-g;ns78S*HTL&><k85i74q~44tZYC$+%xHKsez}<_zL_Y#nJB&)hun+{ZbtW;(e`E(yScd19rrJ((aorG^C3DU'
    '<F7kW)t#v7Ufg4dnD0)EbuaEXl!mrs#C3<=?(o?iKD)zUcOtGk5!W5gx)W91iK_1K*`28B4!hl9w>y#39j?0*9o>sN4sqX;I&>#;'
    'x}!>WBBwhVbtiJVqgW5du^z-x58|i?anyr2>Oma!AdY$vM?Hw69>h@(;;09?wFkQQAgX%cf*$DJgUIPY<n$nNdXRT};E5jS-UFq3'
    'kUx8%dk=DC4|MN=wmnd@2m19mM6qOy^<*6DNyPOe;(8KsJ&CxUL|jiIt|vP5M2DU*-xKD05^+6=xSnv`lQFI*%=aW3dlHR3QKcu*'
    '*b|L<qES!AxSlB1lSu7}emxoEdZK1eqPQnf+!LjH62(2yy(dxJ6BqO(ihJUTUR1HYs9Spx;k}6PUPO2=;<gvj*b5i*Lib*U{r9l%'
    '+Y1-;BK~?2f4zvmUeuqxs5pD!mtHue7cS_9?!C~x7fSa++g_;IE2miY&f8vS)C*O59il@rHhWWl_NM;qP2Bb-ZhI5Ay@}M`#Aa_)'
    '>5VGAQKdJk^d>fY6Pvx^x;L@e8|Hfxo4tw6-l)=>*zAo)z0s&QvDq8NdJ~(y(XThL*&8)`6Pvx!wusU(O2%eybni`U_QnOhiOt@4'
    'q7N?UgA4lLf<CyQ4=(6~3;GmJVT5xReegsdJkbYF^uZH-a6unj&<EZ7pmZOU?t{{OP`VFF_d(k}sM!bo`k+`JH0py!eNd$jI`k#;'
    '^(FK5CG+*An(0d(>`TScm#o+quKU7uU%2i|{PiU(_9ZL!B`fwN8v7D|ePO;YT=yla`VvQdiJZQ~N?)R*FC$l9;-N1Q&==45B@f=h'
    '$)j61d2|aWk8a`Q(Jh=jx`mTRw{Yg`7ET`B!s()0I9+rLr;Bdk1ko*=Ai9N9Lbq^A=oU^1-BR>*Y5XmDUzf(;lJ|A=BexWN9sS5H'
    'MPEn#y@gX=w{Y_47ET`ZBWv^{YxE;)^rPnMM-J&n&DW0{(hpzv!`J=rbw7OFkBrifjM5J$_andb!`J=DHvPyp{qTH0vQ0lCpdS&?'
    'kKEIbc<4ta>PK|+BQNzMR{D{p`Vl$($XWfU2m29K{m5tih_QZTw|+!iKXP3^;_p@>?p7l1RwC|JBJNfq?p7l1R?hm}O2pkt#NA57'
    '-AcsWO2pkt#NA57-AcsWO2pkt#NA57-AcsWO2pkt#NA4a-Aau0C&u~{WBrM-{=`^+Vyr(g)}K+kKM~iTi0e<p^(W%`6Jz~}vHnC='
    'f8wY=anzqU>Q5Z?Cyx3PIsJ*1{zONA;-Nng(4PqCPXzQQ0{Y|m{<!?t><0cif7&&EO~$Vi?+;HEQM^<5Yjz5M%}(L3*(v-rdxO7b'
    '|L@nF<@hx>Rs5PgK2R!;O5<byzviZj+w!-Xg`=CLxAC_0+j#QiHl94WEz$Q>>Neh;ep{mNCFwj$6;Sa_>bLPG_1k!p`fa>P{WjjD'
    'ej9I6zb$_^T73NUHr}g#8}C)WjVD%a;~kW@@wW8ac#rLEJRfiyC-iU2otO`SQ<lChH;atEGlz2D8U5dFxjAJz-Uhynx9r`Xa8^m?'
    'c2v0?Rc=R>+fn6qRJk2hZby~dQRVi8KZ__;KzT>Te_4!DMO0Abc2v0?Rc=R>+fn6q*u5QgZ-?F6VfS{}y&ZOMhuu41@D3Qf0|xJa'
    'vpeAI4mi65C*OgS@4(4-;N&~t><&1)1D5W9r96t?ejQN4$#>x7J8<$Hxm+GU7m`H<U*7@qcfkA|Fn<Tk-vRS?<aW8^=f|?Bpu-*L'
    'a3?Om6IJd+l{-=8PE@%QRqjNUJ8|-zIQdSTd?!x66IJd+l{-=8PE@%QRqlk(JK^(A_`DN7?}X1g;qy-Tyc0fu!=2N=DX<hC%Ki<{'
    'ndVWd&{llT^f$bj{x>{l`WxO%{~K<g&ZEF?N|gBx@2LkxZOJ#xCr~Pf3U8QCpy+SAi{9SF4cm9o_q*u(UG)7fp18dWChmfXyI|rj'
    'n79ij?&2=)yXZS8`p#tE@1nQA<$Ykk<$Ykk<qcp36t*8yzvX>kzvT^JzvZ1@zvaDNzvaDNzvWF{zvZoPzvb<wzvWF{d6bH0V87+9'
    'TM>%Q8&Xe6Y5=3!0HS{Y(LaFbAHb+KfLt(uTrhxKFn|m_fDAo=3_XAhJ%C&=fLt(uQEdR3VE~z70Jl*L;QomLWbXmw>jC7D0pySY'
    '#iuBuTreQ_j9<th=@=FB%K$RUfZQpskU>gfRJ>JU0QX1?;2w#)$=7$I-`(hUH~QU;es`na-RO5W`rVCwcazKSCYRq$F29>xemDBv'
    'jed8d-`(hUH~QU;4tJx&-RN*PI^2y8cca7I=x}%Lv|Y@6j6xsMVfvT38yyD1^+32D2-gE)cOdKzgx!He$3UWEAki_9=okpQ17UX{'
    'd=7-qfsB*`iH?Cp$3Sji8Az-QBvuAe+YCgpfhaZ*#Rj6-z})k&VZNS<QBl8v=r@p&c_3;IB&r4yRRd9T5K%P<Z3m(4AhaEXwu8`i'
    '5ZVqRat0AOgNU3#M9v_z9fY=n&~^~o4no^O=r9N!2BE_sbQpvVgV13RIt)UGLFh1us2W664MK-|s3-2Bg1CnY;vOo9d#D-ip=P*;'
    'n&BR5hI^<P?xA`DW$vMZ0EM>1O);QsTjAypP}G*Z>*F5ohPj8kKJMW*n0u&L?x9+{hx+9ns<q$ohLGPS*iEH>$NBl+CD_fj6;I6n'
    'F2QaN74G`@U4q?!lJ5)oU4qYyDD%4npSiX?3T=t|W<c4t!u=tjs4aP8$nUse=6Bo}@;mO7`CWqD_>%>8b127d?vpuoQ)Tz!-FvBp'
    '@5RaY;^cdA^1al;_u}h&@%6p<`d)l}FTTE)TKHa^42r%p=~htGmUQdA`14*Ic`qKk57*ttdui^&gZJUV`|#j>JkfC<j=T>?-iIUa'
    '!;$yl$oqJM&3$+f6n$sXXP~Gp>9hNA)_r*CKHPIZbBp_#Tinmw;(q29_ZP;M0xHZj?q{ZPKkpj8pLxgqyleP=W+C@83%Q?J$o<Sh'
    '?&p2N_cJHCpE=3>yb1Vz<|OyWbCS3%^8EeGP#)kd!4L43;0HM4@<4*6OzMFIOF2|H|MCDky$|q~;0Jh1@B_Rh_yOJv`~dF-et<Ut'
    'Kft@GAK*>E4<uL$ZOM1|K9FD{oq7<5JcvUc#32vjkOy(dgE-_t9P%Izc@T#@h(jL4ArIn^2XV-Qym9(L{PG}vc@T#@Sg09F<G(uj'
    'HtGj?8});{WBNgy^&rlAFz}iEWaO*|@!5m;>>+&i5I%bdpFM=n9>Ql2;j@SE*+cm3A$;}_K6?nCJ%rC5!e<Zh#_5M}-9xzUp#;0('
    '?@Ydp`XSy%{Sfb%eh7a)l;AU+dI+};#;t>K>tNoUJ{a!~#=C>@?qIw-81D|oyMyuWV7xn+H>nTC$%Aq7VBVxY7+(*@*Mo8LV4OS{'
    'ClAKSgK_d;-m5;C_o@%(z3PMU{9rsk7|##J^MmpHU_3tr&kw=#LwE!G5F%g*5io=Z7(xULAp(XF0Yiv@Aw<9s-p4+Kco;%F4B>t3'
    'Lx_$cM8^=~VF>Xsgm@T2JPhIO>_d1v`w-sFK7_~_LgWk~a)uB&zo&BiJ+<QRsTF@uJ@|Vnz~58z{hr$hf6ojBl=(e1A1G=|)_lKb'
    'hVpwVz~3`N`2#iIAE@&FK$Z6gD!D&UyZwP`?GM}|_y=YMpv)hr)<98PvReBCvw}ZRyZwP#!5`7+k5u=6M6o}j*dM9q|A>BnM87|x'
    '-yf;j|A?A@<Zj77q8}*wg`|FeM6o}i(VwWx|Ab<HLa{$liT?@x{)B#iLcc#zZT|^1|HQ43e?mV{^b1M-{)A!=^FFYLc^}xr+=KOS'
    '@dRd+p&#Z}tcQ!|G1J+$-06*o?1woG^Du7!dzd$XJ<Lg&hdG<}Feham=2onSxfSbSPSHHfDVm2lMe}fO_bNOlTvGaQZigxp#;OSA'
    'Pj8gQeJGse$fCp<vxhnH@(6rB0-uk-=Ogg>2z)*QpO3)jBk=hMd_Dr7kHF_6oIH92J|BV4N8s}j_<RIDAA!$D;PVkUdjysqg{4Pf'
    '=}}mE6qX)^rAIlD^(bes9)+bxVd+s=dK8u(#dVLu(xb5SC@eh+OOL|Rqp<WS?s*hm9)p+1;N>xRc?@12gO|tP<uQ193|=0Cm&f4c'
    'F?e|l_dEtKkHO1h@bVbEJO(e1!OLSX@i=Fc9xv>@L>V;wIGOfwGVSAJ+Q+%Y;&Jls<J?>EIA@d|=Zw<h+)4mSJ<j>1$9bF1<J?s7'
    'ICoP#&TSNrbN|HS+&J+#cT7CatrCxOkHq8Lg77%^NIcG+2#<4D#N*tF@C3|1!RfFkI34x`r^BA$bl4M|4ts*rVNY;6><O5E0_LB9'
    'c~I&Jn16zkW1#4hNmZWU<k%B%_5>_F0WW{1V)-)_%b%%H{!ESXXX=nYQ&oa8f2Jw{MQzEd<j+)<f2KzHGgalExz+m5++6(^;^;5L'
    '(O-y_zfhz6g*xOfRF$C2U#LnzQCqSq`3qI$U#L<3LRI+}JpUK&oc=2s{S}S=N>%w+6#FZR{T0RjO6B-hGy+B6lGNz0sPb2I_$#-I'
    '{}omK%6;O0L!-Z;(cj2*e?zgqq1fM0>~B<#e?ucs^est^{)Q@lLx;bSZT^NTf8!?bq0EbiGA|y=%@ISH7Z2s;h@m`PGL)xdhw^mg'
    'P)-34<>}_3oVy>&6C^`<f@CPq)eSA&>kz8Lq1^H?v~XKW7)OV4cgoPh^LU}g9Lm#qLkoPC#!TcH42gFr=ZuFI&UA;F_fXCm59MtA'
    'P|m>z6n-(g9ulE=KnlN*MYXdh-y=s3&CRt-;uVl#JbN{)SZhRo=P;hc8pgTpVVun#hAP8QWf-aqLzQ8i)E>r3?O_E~Ld7`@RfeI%'
    'Fqj_(*F}`hq6G6rl+L5V>F;5vG7MFUD4j=zli|ZqY#53S<Mj71&U6n$&0(>caa-K?q_)FiZR6A5sgfMZD?Kb$Iz9^?l^4U%eR!e9'
    '3{gCsNF7e34kuEF6RE?A)Zs+xa3Xa$=k<r<kl{FFIGz|zqz)%ihZCv8@x*W<bvT|FPBacL+?ZS%Gm-Sm@WQRgp>iCKUxwp};e}^0'
    'f(M7=km0ysIM2%r#}mWReK<-FN890tsF{r75ykmK)T0r^^ax^l1Tj5=m>xk)k3hc>=r;oWMxfsaVtNEIJ%X4Xfqo-UYy=t=QM!Qg'
    'ij5$`N1$I3r3)yp<_MyH1kpbNrAMH25v2<#uloox!w53N2s|+YPmJIxkr6m#1X*JQSz`q589~+<ftN;*HAdj95oC=K_-rIuV<cH)'
    'Bw1r5d154)VI*D}iF-!!?9NEMG?H8}l3Xy7Trd*%j3nMi;-!(eXC!_Zi9<%>f|0mjB)X3*JbM+KJQAfxqV!0#9mx}MBT;iC`i(@f'
    'k%wrM%mq)fmhdEN2~V<?@FXiyPqGsABx?yzvR?2c>nKmMUhpLA1y8bG@FeR6PqJR{B<lrFvfA_{t9MUw-~E%^cmE`J+CRyi_D}Nc'
    '+><;z_ax8GJ<0lD5v4&{mXhl|Px7?fldO4+B14ZNLysauk0L{lB14ZNLysb=MiEt`h^kRU)hIIbC^GaYGV~~-Y7}uaikv)(s2W91'
    '9z~3eA}5a`;zp5^N0F095sjmW#!=+tQN-pba`Gr5wTRLQRQ$bS6ptc`N0F~b5!0i{*Q1E=Q9SWCid;U5=pRKcA4M)0MJ^vjW*9{-'
    'A4Q&cip=m7nc*oi!&792r^pOXkr|#MGd#sg;!|XXr^pOXkr|#MGdx9Rc#6#M6q(^Ea=}yNf~Uv@Pmv3rA{RVGE_jMu@D$Pi6w&__'
    '@%|L?KALzRO}vjL-bWMfqlx#?JP$jX=pRk=k0$y@6aAx!_tC`rXySb|F+G|n9!=biCQ?TesiTS1(ZuFxqH#3wH=6hxP5g}};zko='
    'qlv1~MAc~GXf%;Cnpk<7=y;mwc$(;Vnl<>RS%ZI?=y;mwc$#tZX`<t4qT^|z<7uMfX`<t4qT^}e;c4RGY2x8&;^ArH;c4RGY2x8&'
    'M!ctqfTxLoXW;W0_<ROFpMlS3;PV;yd<H(BA=^9ypU=SOGw}Hgd_Du8&%oz1@c9gUJ_Dc6z~?jY`3!tM1E0^p;4?7zEUWd;vQP3X'
    'YlqLWcK9r7htIN4@+>Qf&$3VQEUWd;a+fnG^(-s-&$5yaiawd#CwZ2Al4sc`d6s>WXW1utmVJ_E*(Z6HwaRB%^M96=%V*gEc$R&V'
    'XW0*U4(6X@pX53ANuFb$<T>_9o@1ZnIrd4OW1r+Xn12rDL8<3p{yCTj#h)zhnt-CVBumf1%X2XCJWM=~2cO4-&*Q=8@!<1#@OeD='
    'JRW?WyT(DO=V9r2SOSGlCU^lwZAnKyk0YPQk<a7E=W*ooIP!TM`8<w%9<HCqk<Y{Y^EmQ(boe_u{2fRB9Y_8hNB$j0{vAjD9Y_8h'
    'NB$ihK&ii@!{5;X6h4{I0hDbk_!AVhB{};$Ed3o`#;_tWh82l1tYeO0ePRsjm}5AXH-@!~F|2BiVI6D?Ro56+y2mi*8pBG)7*;aI'
    'u#z!`b<8pBF^pkdV+?byG29R|h8k=PwbU5y_8G(MWel^BG2Ev!h8uLoaD&wtW*TEykr+$$JC^EqEY<H=?u{8sEj*U$cPu)LMTfEI'
    'FcuxgQVWlz79I<qW2t_}!tPk^jTuYzI~L~0Qqzt_hq34|mV0ByqRLq6-LX`-V^M4@cf*WDzp>mDGZr<+QVWko&2g*&jw9m65pm;)'
    'xN$_>I3jKwH_weD{>Bl1<A}d;%zDP*f^oQD9J-Gq{>Bl1<A}d;#NRj~ZX7Eh<M7KkZtoh0U&i5yakyX{w{VTa6XRHQ7>6guq5C+L'
    '9*4H$h}3b1Xq$}G@yuGs6Sw1u+wsKhc<zE4PZW<QipLYh<56=wYK}+E@u)eTC>~D~k4K~N%xK4>*mxp*Jo=62o~ZGtIiBbrPxOyR'
    '>G4GWcyu3+?&G;bYCJ9&Pi7d8C&n``9*;xDlQqVZHOAwf@nnthcxgOYV?53pPu3WZvnG%=CXh8IkToWdCnk^?CXg8>kQpZ6o(cG6'
    '0xKXBaL)vC!31)_1aiRyqJIL;nt+!k;GPNiWdfd<fD0zzf(ht80i`FP?F7~pC!pp8^qYWU6UYS<4pA(b3nr2aCXx##k_#r13nr2a'
    'CXx##k_#r13nrrGMAV#!niElTBDr89xnLrSO(YjgM8ApTf{Ca(kz6nlZ6}foCXx##qWeU0!9-jz5f@A(7fi$x6UhY=amYk+!9@Hr'
    'kz6nl_e^B{Y$ADLBF>sfo|uTwCXy#6;<}0CiHW#w5<Z)R&nDrsN%(9MKAVKkCgHP5tfEfBb(3)2BwRNM*G<A_lknLjoHYqAO~O5s'
    '@XI9pG6}y-!Y`BX%Oo5!2~SMI1(VQy5=u`(=}Bli2{k97-wWKb@&dO*ypVW`BLB(kS+N);ZjN|?n<HM}u80@7E8+$20eOLYKwjV;'
    'kQcZI<OS}Ec!9ejUf`CM7q~eBlzM@CBwpaIj~BSr>;-QAc!7J&Uf{-w7r1fa1@4h}fqS=J;8uwjxM}MJZrTc{cKpe}OpM}BhL_+?'
    '=01<f=r<YtCZpeE^qZV`CZ>o|d6dw0GTKf?+sSA<nR`Gca}UU5?g5$1Js^|Ob~4&dM%&3~3rbB!+sSA&8I2~R(PT85j7F2uXfhg2'
    'Mx)7SGzA@|pu-e&m;%>R;Cc#NPl4+x#L*PuXbN#Og*ci5*Hhqn3haVXQ($)rH?V-hClgUMg{YcBR88SNohiiF6!e>depAqI3i?e!'
    'zbV|@G6glKpym|R%%bq`!tT-(w4F-)O-1RcC_NRWrxI~fiMXk_U@9({iVLRVf~iE@R3dIF5jT~Hn~Dpj;)1ET0F;`F3#Q@%Q1r>9'
    'epAtJD*8=Dzp3aq75%27-&FLQihfhkZz}rzBcWJH5ydrh9;NbaiBszT;4YJYa4!8H++OkzPO1Nc+e`kzlaT-5Rvu6al=%lYn}AZF'
    '=#$C&O8&tOI{)DIl7Dc6&WrH!BD}l^FE8?h=!>xQA}qZKOE1FGi?H+}EWHRzFY>(Ti!cF7fudhXGVvmPe~BmhUn)Mq6@B<6p6`E&'
    'XZT;@IsKP-GXEu>zJH0Q?_c71`<J*m;wA1Dd5P!kU*f*Qmv|cfC7yT>DA>F--u#?KT`-L-HH|DajVv{dOf-#5G>uF&jZ8F+@n{<3'
    '(KN=RX^cnH$VAh~MAI1ir;(RHscGb;Y25ZUjoaR)F*;3SJeo$%nnuo=#!X_=xJhgp`D_{)Y#MoK8h3|H;|{lJ+~GEjyThh4=1fQ1'
    '>1aD0ZKtE{bVi`*j6l=TeLA{NNB8OIKAjP0IwR0@Mxg18K-1BEI=W9s_vz>kN=--i>F75d{idVebo85!e$&x!I{HmVzv<llHl4fQ'
    'rla2sG@5}%Gtg)TI?O<a8R#$r9cB=JGl;(##NQ0!Zw5NdK!+JH4@%8|`59CKpzz5=G|nIzXK?r83}SNzu{ncUaRy4yK<ODMJp-j@'
    'aOd9)bf1ClGpIaf;DQ-c7c=n03}Si)F+BrM%p|5~;*gm*WF`)oNfgf{if7`UnYd>r?wN^uW)j6SiQ<_=@l2w4ChnPuduHMuP--Ub'
    'nTdNq(I=Bi&qV2&C_NLUXQK2>l%9#wGf{dbO3y^;nJ7Jz=$}dS&qV2$sjOb6vU-`y>Sb!Fm#L**rj~k{TIywLsh6pxUZ$3MnTivX'
    '0%cyN&H|-C;ggAHWkD%W_LGIDGC?U&^vUEinlJMl?aMr|`7+PZzD&*cGS%<PRDds2{l1dWD3yAJ`$JwyXcV_4PRhK(O@6O%8s-)5'
    '?t6tNJzwGOzE`+S<P~m{1f@WkSGd;?lmdlMCZ7HUr9jzF7M?Q&r9jaqlTV$#!jr+T@C@oJJQ@57HwV7LEtIctkKilZLis9j^eS=m'
    'Dsl8GGn7|}s#l4sSBa`uiK<tLs#l4sSBa`unW4N&<bYD3=ogal07`+PPbTBxRU+V3JpU>#e+^&1hOb}4*ROF)&TF{*HC+B0E`JS|'
    'zlO_S!{x8x^4GXC=QW%RN`azZNct0$0!5!p`tvm$`5GR44cEQS-0*eghOZaK;sPqn6klhi_&T?}z0SPxb?$e2omu4T-0$`}bIRA5'
    'Q@+le@^$8vuXBgn>&!4;XNLJY_pQCo4D)qvSbLrM=Iil%vovO+H2pfW&o{Vz?TrM3nL=Bthzd8ey}@4c8{EG32D`^^aNpV++_&}y'
    '_pQCb4Qp?3!`d6%srCkU48FmgYHx6}<s008_69eey^-K0ot}l4X5pn-cxe`1nuV8U;iXx4X%=3Zg_maGrCE4s7G9c#mu7Jv;4GXq'
    '3un#3OS8Bga2B@%&f<2!S={+I3lGl1gR{8vZx)W6g(GL-$XPh@O&s|qj(ihGzKJ8>#F1~}$TxB1n>g}K9Qh`Wd=p2$i6h^{k#BO#'
    '-<$aJP5k*LcmBP}oqum~=ii&$<o6~{ev_O0-o)2$;_KP?dN#hEjjw0p>)G6vIUASH#^tkd`D|Q18<)?<<+HgFb2grzjpt``Bj#)('
    'U^Wpj8_&<i^Rw~%Y&<_3&(G#Y%-P(CIhz|XXA>Q>iH_Ms$84fwHqkMg=$K7(%qBYK5FK-fjyXif9HL_mH)+lxR^|{ZbBL8W#L66E'
    'We%}2hubpe5IJ**oH^W<Ifpo!LmbT^a^?^@bBLTdM9v&;%bde)nRB=;a}F^!hZvhfjLjj&<`855q~84}_3l5ZY5z$T`%miDe^ROb'
    'lRI<%$;=Iu0%iV5r3y-cqE99()qgT``zLklKbg7xi%RuhRI2}?8vPgb=f9{p|3!`YFYeR%7jqy`3Y7U5H6|zpiawdFG5^IJ=wDQv'
    '|6&gGZ?ye4+Wwo_%fC_j-zfcWl>RqL|C>3<ztR2Q+?Diiv<0O=(eEX-{Wog<2mStoe*a-^@gLOu4{H7gHUEQ}|6#`PAGG}scP0G?'
    '{Xi*D^m|GD{)1v~am(LZ#T*&^{9D}l_f|10rsKB6^KozS{OwyjfBP0s#J$BWe{XTi-&;H__ZCkdzQxmWZ}GI;TRbiI7EjB)#nW<c'
    '@wD7qJe&I#Pwl_OGxcxr9PL{?Q}`Coz`YHhZ^P%?@cA};z73ym!{^)Z`8IsM4WDnr=iBi4HcubE4WDnr=iBi4HhjJfpKrtG+wl1|'
    'oV^W8@4(VKu=EZry#p`r@Z{w?JbC#Jyu1T1@4(AD@bV5mdk0?LftPpS<sEo=2VUNRmv`{XJ23GsOuP#d@502pF!3%-ybBZW!o<5U'
    '@h(if3ls0+kauC?U6^<mCf<dKcVXgPn0S}I|2OOolxMSIS*n2I$|H|bxwh;RTv2DE%nr)7l}CSBS*VObxwiQ1YgE7FQMM)m#h(n('
    'm<gvB%l@0+&k5v~fKva>@9qQ{N<g``Fv5oH4T{_1_4y!C2`Jl^J;j}G%cIbiIQ{)!PJjP5zdI10_x^8wcc3h+<^MOoJCF&h{{PMI'
    '4upM+EGnED|8KrJj0VxNEDB>sG)`twTq~x+LwEnp?*IhJGXLfL=YKiz`QQ8*&#3EVsrO<vgUf>p-$VEJ(EUAhe-GV3*|zfd%yU!='
    'zlRGzxliU@@E%IPhti<bdngTx+lp#}vTX%5L7^?7=6k659%{aan(v|Cd+7Hb`n`vK@1fs&==UD_y@!79q2K$teY}!TMwY&hn(w3L'
    '`>6RoYQCS-uQYs1$@^#v%6_t-?fdBWKKi|nexUFz35`J6wt_~W(3a5XeKdL>jowF<_fh42*nJ;%KY+6j;Oql9`v8_e*|vh`LAka('
    'XCILHK=CJwe0~6*pwtJ%11Q&)&wQY`t*8Si+g8v46xtFxe1Hxg;Oh_abJ(bwFH3)b%Rk8PQ<jA2_yAQtI7F4C=Re5JeM9uc|1R-<'
    '`wxkL4^i_&)cg=NKSWJXwyog#578Es`($3*57F;K^aG_nL_bj6R@4ZTZ7XO53T+9EK18Dr(da`o`VfsiM57PU=tDI65RE=WqYu&O'
    'BXZV9DE1MGeS~5kq1Z>{tdGzSl>KBuzmL%9BQ*L5jX>dB5;}mgZ3P`bp)H}qN9gboe0~I<AHmtj@bWRdd<-ui^W^NuJS+Qgt~L!z'
    'mDx`gpNIVzUxQK~!`a8=EKvAl!pWdqTRszk;<h4#ptvpf9BuA93n<qXKh>W5&H~D|WuJSA)C7gLgeo7S%EyfFA5*P;%t-PvPxyY!'
    '6ZRkT#NWqM0v}Ted`vWcO#FR}Lq5hK9}{tNiKDsrWiEc1i(lsAm$~?5E`FJdU*-~3b8!zSH5d2H#UY^Z$%G3)aa+*^pln+~X;5fO'
    'C_NXY=c4pnw4IB#b5V0HYR*N?xu`i8HRqz{T-2P4n)A?a9{SBgzj<ghFE`%|Oa5i)c_=n7H~WlGX=qC-21?CCv3bNhD10)ZCMegI'
    'k9SbqR#X}kw-uEJ<=XP`4$8I_TmTAf2^Y-61@lmB9;4wr^qa?MI1e@Fq2|0p)J%?s^T_P;iQD<;J|ErZqx*bxpO5bI(S1I;&nIr@'
    ';{s4>J}#J#(xC9kgqonZt*9m_+g4Bv6xtGs%}25MC^jF(=A+nr6q}D?^HFR*ip@u{`6#vkjTWHM0ytYhb+Lfz0+d<+yP#ZK{M>Fj'
    'Q?h`l0>z&!)+nHCTR|gGXiIRt0InA>uUbIHT)^14fH~I!vgrac<^nS20@Pf9ehW}+0g5doau%Y>LR49Z=NF>ULNr>4MxfNfoGPh!'
    'A8#RwfpVYBE4C0-K=CJws(?aULY0N6vJh1kqRK*aScnb_(P1GvEJTNe=&%qS7NWx<>iI>evItccp~@mE_(f>62#pq@(W3m#Q1OoY'
    'A`}Cq7NOW8R9S>7p!nYvRRM*zger?rWf7_@LWf1@un0aE!RKN)TMTE5;bk$rEQSeCYB6pF<=XPREGEBz;!hSi17+I^oPk1Hg0sbN'
    'wiwqfCYLY9gNw=Ki(zo_Aq*z-^%5Mp1a_Ce?h-t>1g@9B^%A%SrIz5jB`^=leKODd64(XBpDeNq3T+8?m%#24*j)m<OJH{i>@I=b'
    'C9t~$c9#<UOW}GcTrY*|r9}Tym|qI>OJRN~(Z3WOK&hqZuoSMB!Zj%VcSWv2p)JAnQn+3UXG`I1DV!~Xmu2v>jQQ9y=3~pK`Ib@T'
    'ErYXVxDJ$B1{2GOcToJvA`_svtytHAa&7r49h7Y=)O?`OmSA@o>@H)BTSn!vjNH16ncFgE<;$4IEn_rX#%Q>V$XQ0LEJNvKC|yYe'
    'RHAexN>`$EB}!MKbR|kx5-XMHUWw-`aRDe*i3=)G8WexBs5B_sR!|cZ+7fD3qGly(R-#`e`c<M>C5ly|SS5;8qF5!0RifB(G+K^E'
    '%h6#uv#jN)vYc7ga#UH44xrR>bXZO_g5pmWH3G$LMU6nYwtO^#vTX(ZK%p(6-*WU@4%f>WSC+&4a>kYA=&<|{9g;b61#z?jjaH!1'
    '3N%`QMk~;01sbg&j#i-93gT!5`hij_&~F7Af#OdVH3DVZ3Oay7TSA8w=&%AER-nTQbXb87E6`yDI;=p4m5lEzQDr5ntVETSjPEPq'
    'dL>-1WPD%A_`VVyR>Jkl+^C(7&&94}L<gl-q6#RqCD>gFyDO>SSCXYx!r)36Tm@&V;A|C~t%9>vaJCB0R>9dSI9mm0tKe)EoUMYh'
    'Rd5DMt%5U9XiIRm3eHx+%c?_oNjhsaEUkv6)v&Z0mR7^kYFJtgORM2!HN32bm(}pHx^Vg?oj_S8K+#{8WMVZ;ti~^^;bk?vtbvI&'
    'FtG+E*1*IXm{<c7YhYpxOss*4H88OTCf2~j8khh@e_4`=H88P;zOOl??@3RrrMGM8?ON)kwbV;%83Wdm_1D70T6(*d9)VJ8$=9G<'
    'TYQ!(_btT{7L@&DA+v)*TY|H-aJClrtfeMeOHI3$3TZ7|uZ8P%IBOkTuY>D#aJ>$$*TMBVxL$_`*TMWcT(=G#)}aF^wXSfpUMlzR'
    'imHHepUkVW4(37OlL_Y6!TdUyUkCH+;CdZguY>FLu)7|1*Tdj?Dwg%|xt@w;J$$Z*!Syf*O09=8P_8Y{*?OD|%6_uICn&Tf_*@U4'
    '>tSjAAuJ`Me*^y90D~J~a03i(fWZwgxB&(?;Li>4xdDG}fZYwS3rcOkpBvyBl>20!>kaS;3ZG2yxdA>mz~=_|+yI|d@L2_)Rq$B_'
    'FIDhT1us?bQUx!dR295b(f6vt+1@Z7Rlx)(d`p6fDwwDuQmcr~Dp;z5rH$~i5neXJ%SL$F2rnDqWh1<7WZc{cOQ6(7SlS3n8)0c9'
    'Ol*XSjWDs1zHg-Oo9O!{`o4+2Z=&y;==&!6zKOnXqPL*bCVIPx-fp6|oA3lEd`p6fO)#;EzHd6D@5$)c3=^ASVlzx^hKbEEu^A>d'
    '!^CD>uo+%Jsm<`R8D2KS%Vzq%nZ9qP@0;oSX8Qg~CcfCDZpiZK(tx5a)D0OclSTFF)D7pv%K{3oE~y(-$fRNvw}nS!K8Z7Jgu+E5'
    '=@`|iUAH7WT$w4LaCpBgi|W=6PfC<VpNzLj>V`FrbV)$r*HiJO2r-I28v0rmP$)*@Zz&aJ@+f}CO4Js=Mx}1xHvFCO1NL<@;TnP%'
    'g}*Zs9u<myJz_H&Jj&w7in6F)?XpaSvTf1e5wR5aA)vao!;=!(wy;H<Nk<f>vZ!9|OeQ>u@=2y%BwyUy_}>K-^)?tQy`{)Y#Ke{&'
    'FVQEr<ax<`GU`Dzh0pdDl*yxPZzEK%PC(%Tofw55%yJf^I-xD_xh2>4vT$il^b7TZoH-^UR6G8baHULXK=HSPCjzo4d`ozCAfP~R'
    'PU$Vh-o`zu7akjo{$21yjN*S6{IV6FZN+C>@!3{<wiTak#aUZ%)>gc<6)$bYOIz_0D6<tWZN*Dl@zU1diKsLVclng2v#4I($UUhX'
    'DmZH^UfPO#w&Is<nb3s@#gC+BQRIpE;j#!t9SUvXslF@<ZJ{LFhO@TetZg`J8_ohnpUiqGJb#-i0mW@aXKl+lE8M-G7G<{Kx^1{_'
    '8?M`i&$i*SZTM^(KHG-Rw&AmCSgMAlYFMg<rD|BJh9yw+$s|jlLR&T(tKqB~UaH}x8eXc2#%frqhNWs)s)nU%SgMAl?ZnY`;%GY='
    'dOK0Iov7MQRBb1!K$-1C)%Hw0k;+DR7Ud&6Ldl5RPQ+~|dvDLgS7g-<D^{7(7{%Wb)ZI?}Z6~vDCmOet*|!s$+sW)Pihd&<+M-`b'
    '#_e|Ud<{OU!Dlu2tOlQfGBxD+n(!ofd7h;jd{%?cYVcVNKC21$vzG@3gC}ZmT}^m)ygcWn(i%Kig9mHyU=6O@fwOkttQ~l12VUBN'
    'mv-PKP-X{S+JTpL;H4dSX$M}~fqQn~o*iWN9c1<$IBN%9+JSp^;FlfvWhZ%lCwYD+8EhvRY$wjziL-X%terRu6n!%3rJdw6Q2fcF'
    'vv!j8L7APnZYQqWiR*Uax}CUgCqCPW&vxRoU9hwZmUh9?E?C+HOS@nR6n!$u(k@s6Wp)vbyWngWyzGLPUGTCCUUtFDE~0T4EbW4&'
    'U9hy9XxvRS?j{;{6OFrx#@$3CC<V&wCN_5yo4bk4-NfH+;%_(cx10FeO~eHhUXmK_><)iRKvBGhPi9fwIQ}wORE);mMB}HK@c+m6'
    'RYoOfjLPfQ%id;?MN$6(EitNFJO9qafWqQvNoi?WNhXWJC&P;hKg~yYc!)p!Y4B(K$#8>m7KKlSx3hejcXD{`as0_xqp*@+L}lsh'
    'UzYW5{657`bL;a#p|X-si*GxOelU*$@1d<uJc$kWPG(X8g+7FfX)@8b)QMkE8Q%VxMYXfv8GlQiczHRznln?f2QTfxOM9pp_TU##'
    'W)BVtC`@95>tdAf%O3m^P@VXbrIB0rklFW;+4oQ-?7?Sy@L53F?<|RA+CygFL(Q-U*X^NZ*hALeL(Q-U*X_Y|d#D*cBWHa^&iag;'
    '_1XXD>b~Qvs?zR(Cnq-vMMy#kkc5O5DItUqdT%y5()6_#M#1u%-g_VG6h}v=7j?!NdqF_K-g|rP{Z+?NM|y|fDfgb7FZ{PY`-HRi'
    'TI+dsIeYILWvSv$dCoSG!9cl9j372e`K&{yc$Sq*P@3H$)FJvmqZ8o?O7qz!a@M9OXNCVubXq(YY$AhgB7<#;GFbG!I4^A?pG7Es'
    'Uvz0{g3|1^i43+G*KNjioADVaw;7*p#%G)H*=BsU8J}&&XPfcaW}LMdXKlt=o5^RJ$!D8!-DZ5Y8E0+AOPlf17J9=i^oCn-))t(#'
    '1!rx+OQ7({tb4ZLo-Md%3q2($w*_Zy!C6~y))t(#1!rx+SzB<{7M!&OXKle*TXEJ_oV68afdWu&D?Zzb&$i;Tt@vy!KHG|yw&JC&'
    'cxfwM+KQL9;-0Paja%s(x6(Im#aUZ%);9XaZS;-X=o`1u8*ZaF+(vJ>joxq@z2P=`!)^42+vp9q(f@6u|Jz3Yw~hWUMDen1d|z{M'
    'ggPewOOQv&-z6y18*ZaF+?HQw58oF)xt;Z_?W|{QXFY2>>si}bH{FgSx8um|^sw9WW4GeyXXuJRx$XIpTygY6X+@y4EE(l(XOy=c'
    '&x69h%jUuD<iYLqx7*2Q+v!EO<InB%qT9)J+v!EO=c1%h-Z8#xE|;KCnCJ)3qOy!zx6`Las6+gBQC3V)^mkEK+`)R}4)oiBeml@_'
    '2m0+mza8ke1O0ZO-wyNx<#sSG-+^K~P;3W^fx`bKtJn?{+ks*`P;3W^?Le^|D7FK|cA(e}RM~+lJ5Xf@s_aCEo#?O=9d@F_PMF^b'
    '^E=@hl-o(HfYP#r`JFJo6XrqT-({KK3G+M2-aE<OJJDe$%<qKjoy5aVxZVl7yKwm~*xd!YyI^-0?CyfyU9h_gc0svaIC&R*?t;%<'
    '@Cge4mn@&V;Byyz?t;%<@VN^<cfsc_7~BPeyJ2ZJyzD0Wcf-<dSlUhW?}jr_Za0nuC1v4%Qyl#~W)UbYOZeOkpP=x`XjoSs{aujD'
    'qcHxWpLz^ymSuN0d15zw?j}#{hTYxdiQRC$n>?`_C+{Y+??#o~<dEG5X_U<&dstiB!`j*&#>smaC+}gLyoYh}9>&Rg7$<|mC$pnp'
    'P+S%@BGC_&mL>Y_VWkZeKG`AO){^L#pn`sT7*X$G)VzmPqdj~%*u%(p4_^-U5&?UOfW3HrFP`6v%R#xlxEz#}r7j1hWeH1raXBb_'
    'GVAia_<Ao{V=q}_FD~DUulM5Qy?A#oZrzJN_rcOWSlUNs*av5z+&(x1rDaKO-3LqiU<nlcU1o-|j~U87^6owu+(%~E$LwVvvzLAF'
    'xsR-|4|eyFHTJ>vKC;F><}3TqVIMhUAFAvlhwM8@qihb@k7D~#Y(I+aM=?-tKmFf+G}@0w`_Tv#{Vy4f_M_2$G}@0w`_X7W8tq4;'
    '{b;lwjrOC_el*&TM*GodKN{^vhyCcVA076i!vS<SfDQ*>9+W#ktbo$8M27?DZ~z@Z(cfisIDifZ(BS|&9Dw-)Fn@qdbbw5B096j4'
    '!vUB-0M`eIhXXKw0ItIdWY|qn%x+O>mR(S;fD&IvsGZLkrF@1c!zU>EUow2gDCM)LG|Oj<Qa(eJ;WI`lpCQWdnV<rnF-rN2QOak8'
    '+WCx8%4bn&mca<MGgu6R#W0wlLY^pwPf)J7H0xGSQkM3HptLOEx)`oO(UTc=i%YY8V}c4Jh+?>oP<sw3hU;SZOi&?f6vJ+U3R$BV'
    't`k(q8pSYQT$*)qf(n_v7*!Hf$SB1JX_U<<L1}h$n4rSwFhrTrVS);y!=N-fIt)s)qr;#yJ30(Xv!g>$_+)n7G(zoTMNs@?`&bc_'
    'mL<B!C><+;!Y8w1#RL_U4ob6Q#h^61-Ws9ykz<H5E36S}A4dkI*^y%j@lZlMln?=+TnP~XO3Km*0HtLK6D33dD0(sz0VPC037#*('
    '<t1d45;95&5m18XOK^D!zAnMnB{;bR@8;k$2cJ3k1O=d64t7BSD19=?<vG~R!7eBOMgL1Cv*%zwNA}Labq=m`aGitQ2(_<mC#bNt'
    '9iwz@I|uVQn9sp{4(3Z?z7*z5VICBKa;5Z?rLbEHyQQ!T3P92SnPImSc1vNm6n0Btw-k0uVYd`^OJTPZc1vNm6h2GgvkX4V;Ij-q'
    'K>;XNhLb@7D0wo?8lV7_KAGrHh7O<r6#ZR>`7$y}8O)c#d>PD_!F(Cam%)4)%$LD@8NMz<hca|1M~8BBC}+e{jw+yBIXZx%vJ8Wu'
    's4Vtw*qr3=+EH4T__`c+%NY-rldsDeqm&Z?<>*jOzAk6PQjQMgj9ALa<>ic6%F&^`H2M%)9<?ZlS`>d4Est(CC@CpNqjE+w<tSFp'
    'Xr}xi{j#H(4yf4yH9MdmDAxh~Kv7vnKTuSb(GQfCCHi$hzYgfv0sT6lSO*mAK;(2Fayp=92lVTJVja+^0~&Qel@9380p>fxbw{}F'
    'NaS>cc~Gt+%!87$G-rXLvWzOAs4SxjC@G7wTl|xhptLN}sAFlgt)x6E3!<`klSz4W3tq0IBiXGZGlq_+*^y}Mh?*TytRwN)5&b$6'
    'e;rY?Bk|V}Z9AfEN8+y|N_QmwI-+|=;;-XDF384TCuS3!m`!wIHqnXML?>nwotRB@Vm8r<*#szjGMP;z+Je%uMB7fxG(ho_?K2Hf'
    'QkKpwKw(*SZqbRkMTp`nClW6usNkhe%sV<U@94z5qZ9LvPRukq6OEmT#?HhaDA$?z10`i?{DGpfO#FeOvP}GelCm`ZKxtW`QD@?>'
    'GZELB80$<_btXr4CP#KA;yM#!or$W>#8GGBs56n%nONyebR2>zhoH(Kr~(Q=xkJzh6o8^9Gpc|BQ1oO*BTxWJpG^9(L(u3D`l>_F'
    ';Sh8<1RV~6`9m1x9l|K@5Jq{2pvobratNv%f+~lgN*7e=f+}551r&gCT~GxSfRZQEI06Nr=*f(Jpa2v-nb8jvfRZQEhyw+n^vOiq'
    'F2r9K;;#!zcR}ecDBT66yP$Lzl<tDkT~N9UN_Ro&E-2jvrMs5q_h3aoK3|fckiqzO{JPRtbuG>B!HSRcCn$O{x?rj+Jy%!ys;=}^'
    'UFnay=J||sc~Jo+3#_1^D}7a0`lGJ&Kwar`x|YVYM8A|2_9O}F9PK6y@+j?(x|YV2#rK@VW$^`J@vlH8DD9mh6loNlxQ%MoAwD`='
    '68~Ogj5;R2zLcOyqi7{9SKKx4iMX!{QPPh^KWiC1ne<%IuP;UKOLifK>=p+xirZIGk}r$f7yn3OSNgaL)T}_w3e>DX%?i}4K+Ou&'
    'tU%2Q)C^HP&`Q)SphQhjP=T5is9AxU6{uN(niZ&7ftnSlS%I1rs9AxU6{uN(niZ&7Q5uaqA`~%Gk&n&jjC90OR@(}+tw7rfw5>qf'
    '3bd_6+e);JQP^vTWucsvC|!xtl_(vf`0t`0%dABAN_4M8_eylHB#JAE;!2dRMCnSDu0-idl&(bS7=^VC%ff0`qI)H}SE752!oLe*'
    'H7jvJgrc!cv;v-#wJTkjA4`=)N{40HD6T}?O0=y++e);pMB6H~twP%>w5>whDzvRa+bXoJLfa~|twP%>w5=khtBC0;w5>whDzvRa'
    '+bXoJLfa~|twP%>w5>whDzvRa+bXoJLfa~$xQZyQLfa~|twP%>w5>whZs?bw&gDf>(@VOcW;bSo-Ow*V(ceXPIdntKZp;+Bp=~#`'
    '?Z!;88%lR0in|fT-B7w4N_Ru)ZYbRiH4_wa8n!)G(hY69F&pfLnhEM$o_u=ghPK_9DRx8Y1a&TtzSHH)Qr)`|)7|nj%y_gGKADa1'
    'Zm8KEHM^r`chu~Tn%z;eJ8E`E&F-k#9W}e7W_Q%=j+)(x+wR0|chu~Tn%z;eJ8E`E&F-k#9W}e7W_Q%=j+)(3vpZ^bN6qf2*&Q{z'
    '6UE($;_m3zqcnRuAx7!xgaj2%Cq$_I<X(@`>{*2#rP;FzJxa4@6?&9r&nomN&7M{0QJOug(4#baRv|_4S%n^@*^_%cN|Tcd(Yz{G'
    'R6xl&h8U&i7<!auPcB5L{p4PVGAH*U)P7c>M-%}OYazGM+vDIb4^jB`p3DY&G8^p4I%ZF1XP{h!B5|V`Us9H$s4O#s?#V1GLLK5K'
    '!?}$pS3t>`n4Wo`mBv3~-81jA(wN<zd7qU=H?QV;=6zNg{aQ&}maJ<;Kf~HH@3Y8R`LcMH6{3)d?5cE6)>wM7j@h%oXK_i)Qg#)f'
    'Cv(FHwV&4MnXbP?-AqqbV|u3RpV9BS_hdD+XF7{4i8ad3DSM`Cqa`JUCkrd3J<~OvlG5Z2?JGPz({<CZtfVKas6Er!XINI;leuWm'
    '(#~<Pgc`+M$H&0Ri;EMkJICP>%}k4P2};&fqyIBIPwmN?YBe6L#)H*(uo@47a@BYcl$IqYv8r)oHIA&tb=7#H8c$T?iE2DijVG${'
    'L^YnM#uL?eq8d+B<B4iKQH>|6@kBMAsKyi3c%m9lRO5+iJW-7&s?og~-K){P8r^%*|MjB(>qY<9t28;~nrI8k6;PsWFILDw(UX}|'
    'i@jJAk5K!m#a^sR_iEQRu30{R#_j7>nmwo3i}mYXtY7zPXDM!N_S9l8*0v+mermB7eOzy1r8lwCo9F=LdJ`R>s4No?y@`k3WN1*X'
    'H?h(?KZ1`swV<STegq$8=pc{M?A@Du-J1;Eo1EO6`0Gvl^(Nwa6LGzXxZXru?{vK`(yuqGcfHfqyXc3qd$X3;n@H_Vr1mBndlQYl'
    'iMZZGTyLVPH&NA_Oxv3n>rGVk!4rM(L?1i>%Jsn$ptLNBsy;ZR4-V;r3;Li~9~A3@Vtr7o4~q3cu|6o)2gUlJSRWMYgJOM9tPhIy'
    'L9sq4)(6G<pjaOi>w`vp(5QxaKn?SN8uDNbd9a2&SVJBJ<!Z=$pr|a9`D(~~HTldJ%?bihu7<2w!*@ea_+(^|WR6fk$s8eSUpAZ8'
    'kWFjIrZr^K8nS5(*|dgiT0=IiA)D5aO>4-ewM0%WkyA_LfC5mimN)_hpy<g=9Muv>wPadQ0Ls-8akb>#TJml!nYK2+8XE6l4QlhN'
    'q0yW*kK*qSkwI(8!nMS0Epb~*+}0AewZv^Laa&8=))Ke1#AYqAS(|=CiGIVkmM<!`=@*sgHqctWuhgdBSE5`{%h#4#V!D=?t|bfC'
    '65+K(cpYA<!%KB|2^4^Gb$AIBfYK+E3|)t_>Tp&aeyKyvI@GK~%{tVqL(MwWtV7K@)T~3zI@GK~%{tVqL(MwWtV7K@)T~3zI@GK~'
    'zdH2m%j!X2RuB5JdeE2kg1)R5^ku!EFY5(;Sug0zdO=^-3;MEN(3cg0zN`@RWrd(GD+D3R+-(q{_PY)GvO>_eH2Fn~=(}N5mc7lO'
    'FRKUjxV#>h*E3hE$Mc|EJuU}DWtnfgptLM;c|9(#Cx3#%zsrt4>sdXhCr8$^dQi{Uw4T+2dU9kv<DPoPJ@w2K>xsX5;;)|gt7rUD'
    '&-kUDxnVtX!+IjFo`|bwZdlLUu%2;GJ>#Bw=7#mm4eN=xdLpi#{8`U>K|Rq}&%CjoZ{GFn-Kr;U>zPwF;Lis9*?=QKxdt2wipnyM'
    '1f^w(BO7pJ1C9iRf0ymG8|bwgaBBnpY`~EXc(4HvHsHYqT-Si>8gN|$dA@->-$0&kAkR18)&|_#fFm1lWCN~iz;z8cs{v;<;H(C`'
    ')PQ>$@Jl}&(hrC9BZKwBFQ8mM`~r%~GJXLiW$AttP+FF_ryuSCg->Q3(vN)B55M#ypY_8%{m5ti@KQhazw~4OXFr_PkL=bDpY_98'
    '{cuP>9MX?`){lJF5BK!LJ^jdM{m5tia8^H@)sKAEk9^h-*Y(47{cv4B@>xGT*pGbH4@dSRpY=P)pV@rYpLt_{=8gTCH}+@V*q?c0'
    'f98##Tz}?`pr|ZvU=Z*41SMtZep66dmN>aTGfYtYWc!>F6qaSbANA+^QGe!}{h4p}XTI5=`DTCSoBi`%3gWMN{qyb#;;(xBnSJ(W'
    '_Sv7=XMg6K{h477K)(U#Hvs(xpx*%W8-RYG+yL|gMP(WNKxtXBCNKcS2A~)y{=0U?Kw(){l>w+S096K{$^cXufGPt}WdJJ#1JGyy'
    '8Vx|B0jv-VK(PTRHjw^dApOHYdIV5zAUy&oD$Dc;prkDA5kP5KqRK#e1W@>7c04hV@x(xSi-GhH1L+Y4(gzHr4;V<+A4r}bNS+_a'
    '2x1^3h=GhC1~P&eNdGX9{$U_}z(D$df#mst<oSW*@`2>?f#mXmWbc9G>w#qGK{#X(4jF_)KmjN>2)}>=Q1oQRJ)i)TKADV02jQMU'
    'xCaz~!v7`fr9pUU5bhboiqarflm@Y)Gze!6!aai+jSj*~gYeQIyfg?e4Z=%<@XH|lGKf`&L999qV%1>~s}6%$br{5|!ytS%2%inY'
    'XM^zBAbd6mpEcsMMts(Y&p-hv*ND$R0VsMh<1<hIN}fz}7AOFvPbMC0#Dky!6#iY-gN=Bw5f3)v!A3mThzA?-U?bVB5l1%S!A3mT'
    'hzA?-U?U!E#Dk4^un`Y7;=x8d*oX%k@n9n!Y{Y|&c(4%<HsZlXJlKc_4{hIfSdvG{XeMm?q3!+*YkFwAKSL!BZJ$YnO*%C1v#19z'
    'DFTIm7jLiYoQuv37af{+LGl|%prC+q(OKi9EZzweIqT58(jmFI=*dLs5QW4X8jVAeU5IfT(lJWhhE(^s*746`gmoz@E-gMZzy6tv'
    'u3Sh^{D#OAhvt=z1|>zgL)%9zB}LKy(xE)xzM|4Y(;Z7CF-z(Gr94XNSrW5UKnZ85VsVQSR8rE8;(15hz68a)r(%@XHhx2bN=n*M'
    'JkH9$AwrQ~VpPyQd9pAI3CjlKg2A|8FfJI33kKtY!LjZUyHVB{j3+=r0p;S0X=0RUTNI;=Uk2le!FXaYx(`P8!RS61-3O!lV00gh'
    '?t{^NFuD&$_rd5s7~Kb>`(X4NjDCaBZ!r1|M!&)6H>7<paY+3T)Et7ELr`-FY7RloA$c`R;@^Y>1w+sl6qUvLmBiYD(y~O`A>;y3'
    '@?@&?5Tbtw(LW@1LA)b5ZhO`fL-529JTU}M48a9M@_j%wjVsCx!4pI9#E^Vuk9a969fCuK;E*9WWC#u!f<uOo8HSJ<hL9PCkQs*H'
    'tRXmS2+kUUvxeZTAvkL&&KiodhT^QDIBO`*8j7=q;w(@wlpHb?pMjDm)2uNRXAQ+YLvhGZ95NJ#48<WsamY{{G8Bgl#UVp+$WR<I'
    '6o(AOAwzM<P#iK8hYUsOp(s5RrH7*QP?R2u(!)59FpTpE!&v1Q#=6EZ)-{H)b}@|Aiec<hAI2_qP%w;@jA5)j4P&)p80!<mIAt)5'
    'QwGCWZ5qbOp<$dH8pg??VeD2O*6yX4rPND79;K@z!&m_s#=i7n?d}Qx4QqE#kVon2$gp<zgr&pU-4o<dT+c}NVR?t-;z8!H{5ncJ'
    'qz#5~rfC=}C&Th9CvgCj4CCCyu>9VNXxS!6P<o1D7^^BxxTgvCG~u2m+|z`6n$nn#*0VrC6V7VFSxxMiZ(_$hDEePA&T7J0O*pFw'
    'XEouhCY;rTvzl;L6V7VFSxq>r31>CotR|e*gtMC1Ki`D2ns8PV&T7J0O*pFwXEn8FsaUb>4*e!v*M#eua9tCwYr=I+xULD;HQ~A@'
    'TsNHFX*j*paC)cV^iIR+orcpp4X1Yk1;go&KuKA`S#iFsfTFU@m<W_FD~y6bNm=5T;(S>FrDaJUH=GgDa7IYO>Hmh){|%@A8&3Z>'
    'oE~pDJ>GD7yy5hC!|Cyc)8h?qcUEybO8URy^nb(Y|Ay254QGTjoDtG+Mo7aMAq}VB98SMEoPKjS{pN7`&EfQ$&1Al2GG8;9ubIr('
    'Oy+A&{Su94n#qHppqV__Odf0|4>ptQn#pd>WVdE=PcylvncUM%?rA3XG?ROp$vw^Fo@R1SGr6ak+|x|%X(snHlY5%UJ<VjBX0lB)'
    '`K6is(oB9CL4FxQei=c289{y-L4FxQei=c20R<z-FQB9>%`c#|EEx-rATx|0`bQA`BZ&SHME?k)e+1D#g6JPX^p7C=M-crZi2e~o'
    '{|KUg1kpc&=pR88k06Ri5XB>i;t@pg2%@-!C~hH&TR8vMLQJ<1(=Ehw3z6DFq_!{?Zec9kLfp16Mrk36TZrNo#waa}QCc|1*TRUU'
    'g|m7sj7nNKYuQ4cXdzF;D1X8*NS;iyMhjV^g|To8S)+xl(USj06vVlpg&fk7{|*%0shO0u=YkfZzlG>;VXV<YE@&Yaw2%u%;*gOz'
    'WF!t5i9<%>kdZiKBzb-$ei?~hMv~b_GQu5+Uq<4Wk@#gKei?~hM&g%|_+=!18Hry;;+K&)WF!t5i9<%>kdZiKB>l=r95NDzjKm=$'
    'amYyej*;{oBXQ42+%ppQjKn=7anDHHGZOcV#67LJrxo|K;+|IA(~5gqaZf8_hE}}PikDjPQY&6+#XYU~r4_%lqHQbMwxVq-+P0!?'
    'E84cAZ7bTgqHQbMwxVq-+P0!?E84cAZ7bTgqGl^<wxZ@J6dT2f@KNYDiX9=NP;(S&j$%j1DD)eJexv9+M$vbSLd{X+f>CHY3T;Ob'
    '@1r>9J&Ncb#Xg-;<bqM0^BzTJ7)4Jq3cn;MIgcK(ly%Q2cA1RgwErlaHHuv(qv&Nu;iXae{b%tJ_mWXKYZUuYM&YGV`F&*Zcp@oF'
    'oiz$)jlwT&_@xcMwBeUF{L+SB+VD#oerY56+i*`C?r9_X+vrK!a8DcVX~R8jxTg*GwBepM+|!18+Hg-B?rFn4ZTO`PzqH|(HvH0t'
    'L)vgi8=0sLhqU34HXPE1L)yqhZDgW0+|!18+Hg-B?rFn4qjAq@+%p>YjK)2qanESnGaC1drY9MVmqz2I(RgVzUK)*iM&p;!_+>O|'
    'jz-PVs5u%nN2BIw)EtePqfv7-YK}(D(Wp5ZHAkc7Xw)2ynxj#3G-{4U%`x0GGKQN*#uU^njy_|ILEABCI|gmXuxAgH8^iAhjNy(?'
    'P_BTIUoRiSe!em6y&J=?0*oom{wDdD((G?dMX3GPrD7C68U60uSXw)l){dpMV`=SJS_{e*Q1Y9zV`=+X+BcT=jir5KOS8WuJC@dt'
    'rL|*e?O0knme!6#_i^Yx4kpII#5kB32NUDi)j1AcK)G=+F%B1ia^qlW94w7vKjt_%8^@l@ad0*c&c@T)@w9e4tsPHm$J5&Jv=)>b'
    'j|;}r_VKiDJnb7#`^MA0@w9I|4jE5t$J5#goI9Jqxw8qJJDb3*H4`|6Hi1)U6F7x7fm3J`IE6NWQ)nrQM)1Le0@oqcLG-@NnY0Pq'
    'VKad<X%je;RzS(G?@r)^+63;fnZO-36F8w3qxAQ7C*qKaIAkIYnTSIsvgdgsewoNw=ZUxnl$(fqCgPBZ>`$JEUnb(0iR?(8h<he-'
    'W_coBnuK2_;g?DHWfBgVghM9bkV!aX5)PS!Lnh&nNqAxsE|`Q1CgFlfxL^|J6en>`F-GZcFi*l0lkmhOPAyI*n@%R1PR2cxanEGj'
    'Ga2_x#uK32WbVxdrDaKenM`g4g->R0+M3KwTa)qGWV|$){4$w7XEJ@x6nL2eFH_)U3cO5#mnrZvg*ci5OQ75oSOTSG2}@I82^2n='
    'WoZg5O@XB;#NQM+n?l4*fx)S;G!>Sn!qQY&nhHx(VQDJoWk9*9FgO(kLGhFA41$uflrvCRmgQ_JoK0m0HkBFJRQQ|<pHty;Dtu1k'
    '*2`(!dN~btr?K)ijg_xya6JvKr@`(t);y-M<^c+(!TdDXod%!NU~n2YTTbI<%W1GXjdjy$teZ}Q>uKx-n8sd!Y3v1<#%y;QYZue_'
    'jy{bQ$Z4!nP2*<EY20i%9mS@j*mM+|j$+eMY&wcfN3rQBHl4ZQbk-R_!E_Xxj$+eMY&wcfN3rQBHXX&Lqu6v5n~q}BQEWPjO-Hfm'
    'C^nth=XB<c)6s7_`b|f_>F75d{br!w4D_49&6YDza|UY8K+PGfEX+XL8E88LZD$aTGl<3+s5t{QXQ1W`)SQ8uGf;B|w^z<U+Zkv('
    '18rxpE;R$CXR!7(12t!`Ryl)coPmBb&~FC%%|O4I=r<GnW}@Fr^qYx(GtqA*`prbYndmnY{bmxIGl|Wa=r<GnW}@Fr^qYx(GtqA*'
    '`prbYndmnY{br)yO!S+HelyW;Ceb*PXq<_DGtqA*`prbYS!gti+hb>;*eu2qv(RW3t9P?dY!-^mVyrO>{bmt=vxvW0=r;@fW})9K'
    '^qYl7v$!F47K+VcbTJE!X0i4=3&mzJ@|cBwvsn9`g_^U7##wv;m_=;PMx)tiG#ia(qtR?MnvF)Y(P%ar%|@fyXf&G`n@x<(Mx)ti'
    'G#ia(qtR?MnvF)Y(P%ar%|@fyXfzv*W~0$;G@6Y@v(aca5jUHNJB%6aVa#X`V@7)zD<Fq4zdelk?P1Js4`Y6N81vi1nBN}8{Pr+b'
    'Kn`QJdl)MqhjB;GVa$XNV<vnUbKk>Q0Xd8nki(em9#&ZQj`DnPSYh2eGGy^#+|hFwH~b!sKM%*BhvUz~@#o>Jl^o6t<#5i2gK~$n'
    'j&eA28Bq9Sb|wFCR`L&L-f=jqDu*)*Ih<L@;jF40&Ya|MR#lF`bw}X3BXHdj`0NOLb_6~<0-qg$&yK)nN8qy~aMlrc=?J`Z1YSA<'
    'FCD=;$`P!i9D$dP;J&9LSUEWYpB;g-j>Jnx;-w?;(vf)SNbVs3<&I=t3`)xq*By!LK=G69J_Chi*$j3h8SF?rcqAS?5)U59SD_>M'
    'Ds&`{JQ7D9i3g8@!J}aCC>T5n29JV4Q0^!q^(Z(y3eG_B-?eiF3d^#*90e~&!OKzbaumEAMcf_*OGm-dQN-<0a5jg1m2=t|3`v{A'
    'F3ULu28*M9bPjti=djCi4m&A9;gi|3LUY)E4GQLP`fv{WD(A4{dJa3T=djCi4!bPpaH?nyXA$SH=W-6aEa$Mxat`|{=dhD<4m&C5'
    'u#<8QJ1OU|b9xSYrRT7(at=Ew=c3qL6q}1;b5U$Aip@o_xt#o(i+-SBE~iK5viEf^+RjD4x#%|+jpm}!Tr`@CMsv|<E*i~6qq%4_'
    '7menk(Ofi|i$-(NVJ<q%V}J5IRGEh=^H60Ts?0-`d8jgv-O8X~9vXq7vdoDGP+FE~G>`ZLB~PY`%_HLG5pna_<vb5<=b`O9w4H~V'
    '^VsD)4{hh6?L2ll&qL{XC_N9Q=b`jGl%7X4&LbM<;evU%U_LIGj|=AGg88^$J}#J#3+Cg3`M3ZS%qMQ=;|WmmWE!dSalw3)o{yUI'
    'QFA_O&PUDps5u`s=cDF))SQo+^HFm?YR*T^`KUP`HRq$)d=y*2n$7~&bQUmzSilHk0b_;*tO6`x6#x`0U_7yaG1vme3=0?~EMRSB'
    '0c$f07<DaR-E;x#rVCg%UBJ9?0eeapu%~nZW0VEV^cS#ibOHND7cgR3z*&<8oHbd%S(63q;aR|Wk_D{cE@0p20#=k3u#0p7>q`sK'
    'eIdFpME8a0z7X9PvOfzHEM(PTA*&9c=*f&H7UGG8cw!-*ScoSU;)#WLVj-Sbh$j}}iG_G#A)Z)>Cl=y~g{(R(#1jkg#6mo=5Kk<`'
    '6ASUgLiU3#WL;w+ep!fL7UGwM_+=q}S%_a2;+I8a_C;j&MP&9xWcEd5_C;j&MP&9xWOh)nh+Gaz%F@$Fpr|a<_k;3fh29>Nl%=N~'
    'L1|giKP+M-u!xbsBKnR+^c{=nI~LJfETXqqL~pT(-eM8G#Ugr(MVxS2MBlN9zGD%6$0GWUMT`U%F%norzp{vaWik0>G5KXN`DHQr'
    'Wik0>F}pz*lWjo3VzSL*GRk6d$YOHHVj_Go5x$rRUrdBACc+mJ;fsmz#YFgGB789szL*GKOoT5c!WR?ai;3yQMDb#x_-LZ|XrlON'
    'qWEZ{_-LZ|XrlONqWEZ{7!({$6oZnoG>SoKSu$EXn)o}K7(1F6JDM0fnixBp7(1F6JDM0fnixBp7(1F6JDM0fnixBp7(1F6JDNB;'
    'nmAfQ94#S^mhi1$2~o9#s9Hi)En&2_gwfg(B4-JG@e<-_330T9zIX|J@e<bjm(VjWVO@U-z3&pfwk#o1mk_B-*u}ksxLv|%Z3%I^'
    'gt%S8PVFT`@e+1iFCiM25PwVPQ<o5pONhp$XuA|`m!j=bv|Wm}OVM^IIdUmkaVcZ4r6|1=rI(`gQj}hb(o0c#DM~Lz>7^*W6s4D<'
    '?NYQ|indG9b}2b|DcUYY+ofo`6m6H1cbAfPm!kVpbYF_@OVNEPx-UidW$3;P-It;JGIU>t?#s}989n7PT(ArmEJOEYD7_4&m!Zls'
    'R9S{9%TQ$*sw_j5WvH?YRhFU3GE`ZHD$7u18LBKpm1XF#3>}uk^>V(oE{FN$Fu$DD^X2HUoZPyc+`1g*mlJWz(P23{EGMd#^UZWQ'
    'F}9p94$FzS<$N<;PW&w=(=JEb<(!FGj?&9ntzXXf@a5#)<tV+JQ!vZXeL3s;%TancCta4K`wG-tfto8&a|LRyK+P4Xxq>)aK^(0h'
    'o323H6==HxZC9Y}3bb8;wkyzf1=_Aa+ZAZL0&Q2I<_gqYfto8&a|Kbn0{vE?-wO0wfqpB9;uS>k3bb8;wky!~7_>bGZI40QW6<^('
    'v^@rGk0E0ogVM*K^f73A3~C;On#aKPF>rkhTpt71$H4V5aD5D19|PCN!1Xb3eGFV51J}pE^)YaLY~ed|arCL;SoW$M%U+dZVg6Xy'
    'J(fMz$Fg4-lslGFFvs%6?^wRv9m~$?V>#P$EIZMUWheTvoPPSB(rD@wj^Lxu=*0z8nxe=sCDG^i6qUB4C`U$L$5T{VK>4ru5%d3('
    'ez%V<$Nrzf-k)frMf_y)6+ilktQ6&<tBC)nz-}%&;P^kK<uQ!1OG#0LI>omlhjmF%bn|iirT%{kw=f6My~_nu9R6Jpq70wm|C!-4'
    'LhYQzDCMl^I9zZXE;tSs9ES^z!v)9jh4?r;aU7li<&MJ>$Ki?N__li-4mpmmxyRv`<M7Mz?8!KuJsHQdC*yc_0v*o|jpNy&aXdRT'
    'QWR~C364*-4NVdKFPS|V$Fuk6cy?$U&)%Qo*`aYfJ2Z~x+{^Lo*EpWNKgYB8=XmyO9M4IY6JY5CSULfgPJova;N=8(IRRcyfQb`m'
    '`w6u61X_Cntv!L(p1|&u6WE<{0;haVpzS9d)b{LNl@p2n6N&y4iT)Fb{u7D*6N&y4iT)Fb{uA@jpX{bMF(3WK(T1J`g>O%G?VLz1'
    'IFVd%VqsriX>`>3#KOM3Ty!<}iG_W6x#$S<iR6hB$rC4%Cr%_!oJ5{Di9B%<dEzAU#7X3dlQ?Sv%AG{kIEkzQ3ZKmGJ3NVfhbNIk'
    'P9kfZM4mW_p5!EYl9TB>PNwfTnZDy>`i_%v&&jywWZZKy?l~FvoQ!);#yuzFo|AFU$@C;A)03QxdrrnZC*z)zanH%P=VaV-GVVDU'
    '_neG-PJy#i;OrDQI|a^8fwNQK>=ZaV1<p=^vs2*g6gWGDh&u(&PJy#i;OrDQI|a^8fwNQK>=ZaV1<p=^vr~z<Q;E1!iMUgVxKoL^'
    'Q|XycCH_FUQ;EM*i9b;IWH$azCH_t&{!XP2Kb2@al|KAbV)HcGej05*jkcdg+fSqIr?C$ZlsgSxPJ<Uv{A4>5ps*~<#Az^b8ne37'
    'nAM#IOQ*roX|Qw}ES=7Yj?+2OaXOrx4riys(&?~tIx88cvyuS{PKUwMVd->uIh~Ukr*ksnbT~VmRmRg<Wjq}QPv_h2>3rKgoo~CR'
    'GcP`!^@-E@N_skLd8cz0<8;nqtc3ZMFuxM!SHk>Cm|qF=E17++WSs#Ntc3ZMFuxM!SHk>Cm|qF=D`9>m%&&y`l`y{&=2yb}N|;~C'
    'Y<DH|)RpM45*=2e!%B4c4E@7r=pQ~q|L__5htJSIe1`tvGxQIi$@dQ>asTj{e2)-su})CbSH&Z;0?Nhx!)NFbK0}Z28G3}z6jp!2'
    'P9~2cuES|u{A7|Raz*(k<N13uDG5=2-7W4(+EMua;xibdoIwwJ2ArJ%XJ^3K8E|$6oSgw@XTaGRa8^LMcpP#@p21w)r=9_4XTaGR'
    'aCQcqodIWOz}Xpab_SfC0cU5z%bD<UCcK;pFK5EbnecKZyqpOyXTr;wc<D@dITK#agqJhn<xF@v6JE}QmowqzOn5o-AYQUwT1Bo~'
    'MXp=Ld8bumzExztRb;+ZWWH7OIjiV%R*~ygk?U5G>sFELR*~ygac*f9nQs-DZxxwu73;LC$b+j`i(N&oTgA%yD*BvNWVcmhw^d}f'
    ')iA#r=2ye~YM5UQ^Q&QgHO#N3&sj~Mvl`}C!~ANPUk&rCVSY8tuZH>6Fuxk+SHt{jm|qR^t6_dMz07KQnbk1A8s=BS{8_Mj7U%fR'
    'g6p&3`YcAHXTkhgFn<=FKMT*F1@mXY{8=!67VMtIdAzgW`YcAHXTk1Se1A9#uFqnmdKS!|#rKD^(BUj1;4HoookcvH4cBMG_1SQJ'
    'He8<#*Js1^*>HU}E<YQWpAFY%!}Zy4eKuU54cBMG_1SQJHe8<#*Js1^*>HU}T%QfsXT$Z`c>ZiWe-3MT=dhM{4r_Vmu;O_RD|_d#'
    'vUd(Ed*`sScMdC_=djLq4lADLu<CaXE1u_YLhT$@1kYhb@Eq0v&tb*$99BHfVb$*(PNAK{X~%OolXecL9nXc&bK&z`_&gT|&xOHr'
    'VeniSJQvQ+g{5=h<y?3<7hcYVmvdPgJ(so7bK&J&PVSw{YUsIeb}lUazi{*v22022gi0<#Q92FV7crlr=)+yn{|m=9(Ub8J#*+V+'
    'kH6B=d|CWmt)w&>XeB7W;F+T6x5SgOC{lBgUlP<I`n#}Vc@#Yvoml%UHTx_z`z$s4EH(QqHTx`e`7Ce$EN}m8{_Qb=DN5?{IqLGc'
    '=<VTu8plJ?=cw7|sM+VJ+2`_KCQD0`zsuJ1bNTO-QO$}Il=AsG+VDB}{5&=LJazdzb@@DX`8;p`eExm$kTylh+dt3SKM#YShrusU'
    'moHG4FHn~+P?s-ImoHG4FYxv+@b)j{-yV%aic?gmOIFP<QnN3j-xsOp7pdnLspl8b?~By>i|F@7+VDmA{30#-5;gl0b@>u?`4V;c'
    '5^w(!@B7k0Z%8<c=KVp65(d8ngI|KPFH^HGQ?oBqvjWQHQMR66&et;+C7YrzQ|m8N>n~I5FH`F;Q_n9`&#zF=ub}N$sP$K<^;f9p'
    'SJ3t=)blHOZKJvrr6^JQE41M&wBf7N?5otQfO739t>;&%=T~9(tJM0d`C8{<UcO2jzDgUuN*lgPt-ngGzecUUM$NuP&Avv>zDCWy'
    'M$Nv43%*9pzDCWyM$NuP&Av{}zD~`)PR+i~8@|r}`E{c4>%_y?$syn1ec#}H-{5`U;C<iVec#{>-@wV=;C<iZec!|{-{kGz<n7-?'
    '_is{{Z{pT(QnPQu#J70+w|L*Tc;B~p!?*Z9zeU`Bi?)A@wtt)VeVg}voA-SipM4uIeVe*`o4S0Px_q0re}}h!2d=+EUA{wIz600a'
    ';qBkS$=`wb?@+Vv^7ilY_V1DzzDr%cOI^MTFW)8NzDqs7OFh3!J-<uMzDLcz$J@Wh+rP)#zsK9ZheqGy?cd|=-{bAy=k4EzmjVjf'
    'QChR_Q?mjJ@+iy1_o>VGsmu3K><8542h`;U)a3^#_5*7618VjIYW4#d`~eL9fLi~6TK|Ar|B!nAkhlMkxBrm0|B$!;khlL3{eH;X'
    'f5_W^#M@I86&C-9xBrO#;Ya+RKOz(Th^+r3#=Acvqx^{c`6I^cKZ<t`$5*N6ii&?sJ%3C+e@s1pOg(>0J%3EieoS3{OkIA=80E**'
    '?8gVyEPi=$JXI_HNmR4QXVD}wL20djLal#-BY#30enK05f|q_mi++OVe}WD_p|w9jho8`fpHk1CQqP}Kv!7D4pHi2fk_&!HU4BYk'
    'ehTwHh54W6ca6s%dW(NbJ%2_$e?~ojMm>K<J%2_$e?~ojM$LXk&3;Co^E2xCGaT|WYW=f=YMrccM$2c#c~tPrdHCf#+IJr9I}g8{'
    'M{CccwddiN^Jx2d_~ks9I1k0ngO~GY-+8p}d}@6@wLYJEo=-i`r)K9<m-Bi1`HTe4N2Bx6=zLT;pIV=PP_2`7==f-0f>MpnN23d9'
    '-vzX<fN}+tY3&7M=nH831!U+8VB!LpxBw<DfQbue`vtW9g8Zs`d=Rqu0+_e}CN6-93t-{`n79zPUI;H2!pnuY^+I^L5GF3ftrx<?'
    'h4fVy;@t~j=|Wh#Fn<muYEe<~g|z)b+I|r&Dxh3DO51l4?YjuwFQT;<F`l@HwqJxNE`o`R=)*69my6)#B6zt7CN6@Bi}L4la<Q5h'
    '!OKPPauK{-OxrJ}?HAMbi)r7*wC`ftcQNg|m<YI-_FYW-E~b4K)4q#o-^F<TVp@AKt-YAm{+!nSoYwxF_WhiC{+ycqoc#H7veeJ%'
    'JAO`Ge!<&+!P|eq+ke5^f5F>-!TWweX7~kf|HVOX&&K;NiHBcOvtLrPU*h>+QqN!F-Ct7cUlPT?qz%7>!Cz9(Us0D|QI}uw_FwV7'
    'U-5=tkw1S0XTO58Umf)JY>xaDoLxfAE}>?Z5G$8Z&r67vONfU{Xu~D6;S$<#3AMh22)KkcTtXWzp$)%A_g~YZU(=#rqx-LE(XY|{'
    '*R<i+#PqLm!LMoGuZi1V(}qi_=cVN9OR4px)cR6%xRf?rO1{377F~))my*FQrL~vR+DmEerL^x-a@M7^_EK7V87;bu7F|Y*E~D0$'
    'QR~a7^=0_%GHQJpwZ4p6Uq-Dj!)KS#hRbNfZ&0j&f_9X)?>DrsfPw<bDE1rX@4un#zhRdA8#MY2t^EzH{SA)%4K2EyHe5~{F2{qH'
    ')1u31(dD%0a`d~L_FYc<F2|pj)7r~v?d9lxIl5mC6PLrp<uGwMN?#5WSJ1vIXx|mI?+V&?1+~6{T3<n}ub|df;MOas^%d0m3Tk}?'
    '{=9-V{I;NGWbEL#wCJ}59ZI6DW4}d}-?BFI+h}YPPpHEuOMc5p=eKbETb%V<`ncaRn)xkr^xsj>-%-!sQP1B|&)-qc-%-!sQP1B|'
    '&)-qc-x2-4qt?Hp*1xBozo(wRr=Gv3p1-G_zo(wRr=Gv3p1();-&5<~Q|sST&p%MlKTyv<P|rV5&p!}<f1uWXpw@q&)_=gsf1nM2'
    'pbdYZ)_<VZf27ubq}G3=)_<hdf25v&<n4civp@3oKce)Xc>AAt`=5CGpLqM9c>AAt`=4n0pQy{9sLP*u`=5FHpLzSAdHbJH?9bHY'
    '&#3ZeYW8Pp_Gjwy7wYmC>hc%r@)zpz7jpSusLNk?`(JqbU*P4hy#24d{ja?Jue|-Qy#256@>lBeS9tj=HTx?y`x|xn8-3&7sM+7B'
    '%ioBVzY!~c<9&al?SI3Oe<M2nM#lUbv$`v(=atm+O6qwf^}LdLUP(Q#q@Gt&&nxlEmDKu5YJDXmq${cQRn+<_YJC;8zKU93MXj%*'
    ')>l#Mt5EYQ+He(ZxQbd|MK5|4ZMcdyTumFUrVUp!Ub>nVT}_Lw#;sS=zN=~9)p+-6T6;CEy_)u2P5Z891aUR3y_(iuO>6&7YyVDb'
    '|4#e<PW%2&J^zjlf2W>*$4h^wF8|=||KRQa;O+n5?f>BI|A3``P?vvDmw&*^Kd8$!)a4rLat*p)L(Q(CX4jzmHE4ScwZ4X0Uqd~w'
    'LCtHZ^)=M`pVa!F)cT){_5Vq&|4FU?Nv8cL_53IG{3q=GlbZdDy8Mf}{ENE$3qJov&HhEr{zc9H1-t)(-G5Q*e^Kjy!RNoI^|kEI'
    'yq4XW*RnhFT6Vi$%U;cE*{gXizqxQNzqyd2_+r0n*|~WwyIrqkALq5~cD<H;oY%6C^IA^4U(2q}YuW93ExTQ>Wmo65oN>Pnmac=P'
    '>tN|Rc)1Q<u7j8B;N?1axei{ggNf^C`*pPaI@*36ZNH8kt=F-m^*T=bUk4M{9mGU-f9v&}x45437T0ro*Y#;@OT(OfJ$HFs&rbB~'
    '*@=EVyZ*0d*FPw@o--BKbEe{Y&P`m;xrysJop(K_^RDM~-u3Juzn(q$*K;24dd^K;&uv=QbBf}6PEp(dpEtng4e)sbeBJ<`H^Ao&'
    '@OeXee^2sv*?s;uu+JY9+yJ{b!0rvOdjss=0J}H9?hUYe1MJ?w4*eV0p??Eh-vHM)!1WDqeFI$I2-i2l^^KgcxDn=Wg!vm`{zmR!'
    'x)B|2M28#k^^N%YM!3Eau5aW_#f>n3Bh25(DT*688*w9C-^j_68}apxuzMry-Uz!l!tPD5dlT&51iLrE?oF_J6YSmuyEnn^O|W|t'
    'F24zv--OF=g6o^$`X;!(39fH~>zm;ECb+%{u5ZHEH{t7>;QA)Gz6q{xg6o^<oo=Rgx|!bTX8Q1(>8oz0uezDO>Sp??o9U}=rmwo0'
    'KKy2SuAAw@Z{}pi&Gc$F)2rP~KXx;H_|5d;H`8<7oZiHki|d&^i*YmOS8nEH#?72xxdnD_f!$kR_ZIlP1wL<q&s*U07WljcK5v1+'
    'Tj1;#IJ*VTZh^B~==*P>@4p4kZs9b`E%f%cz~?RSc?%5Q+8)Irg|~8l@~zyTd@DC5-^z{2w{m0ht=x(X3ZKmWGR3XjSPlwq<@aT7'
    '<&NZAxug76?kK;N8<TJ4H!N=D*Jf_z{^VP^G5J<*MZT4LkZ<K4<XgE1`Bv^hzLmSiZ{@D>Te&0oR_;i?4OMPKmD^C|HdMI{Rc=F-'
    '+xRV!+t3IU+{SMJ-Ns$jx1rx{XmlGI-G&agp~G$Ha2q<@h7Px(!)@qr8#>&E4!5DhZE$@XT(98<@ij2N2Ikkm{2G{F1M_QOehoK>'
    'gMu~a0E)^ocm0FXvP6e9#1SZYGF4>_k+X)#S;NiaYtU~E`mI5+HQYSD2L0A>*Z3OLT!WfxP;(7xu0hQ;MAaIiY7I)SLFwC3`gWAQ'
    '9i?wa>Dy8Ic9gyyrEf=RP;fi(cRRX+k|)!MyB(!(N6p(&>~<8p9mQ@(vD;DXb`-lE#coHj+fnRx6uTY8Zbz}(QRQ}2S<9$$Eu+e{'
    'j4IbMj$F$)axJ6uwT#k1!CFR#YZ)D`We&8KInY|>Kx-K*uH|0owcIPcmQngz?v7r|-O+3LU4^y$uEJV=S79ypo37=z6V@{4TFc$h'
    'YZ<q$<tFL1jAGZJ$~sh8hbrq(WgV)l;|^L-u#S=cI!6BM82N+3zsu^k4*k}l-#YYLhkonOZyoxrL%(&*1J<G6I`mtIe(TV09r~@~'
    'UfXrdE!Ls!I<#Gfw(HP#9onu#+jVHWo;<joJh+}bxSl+?o;<joJh+}bxSl)+3f7bPKuKBpn;D>}EYll;@@0ko50sRpzkCBq%aUxm'
    'p1yHCedBsE?RqlpdUES}a_f3>>w0qQdUES}etBa(nRY#yc0HMPJ(+eredBui#`R?3^<?2Yi1#~)_dAI9JBar?i1$0Vf%*=j9~9g{'
    '^xr}B-$69qK{Vb$G~Pip-a$0pK{Vb$G~Pip-a$0pK{Vb$G~Pip-a-7`LB!ob#NA26-ATmVNyObr#NA26-ATmVNyObr#DRi4i8xSF'
    'mPQ;XElb8BcM>ai5)XG04|fs|cM=bG5)XG04|fs|cM=bG5)XG04|fs|cM=bG;`uxA{02O~0ncy1^BY*t+CT(sAObcp4%xssWCK0d'
    '270aytV?ZRU1|e;)dto8HxMfuh?Nc8-M)cw$Oa;31Cg_V+uAp9&-w=9VFMAcfgWfB@vwn-*a-6*VSXdbZ-n`cFuxJzH<E2Ol3zBG'
    'Up6wj*oZ0{QDq~lY($lfsIn0qHlo8ubl6A++lUSu(P1MxY$Qu<Bui~Xqm5{^5sfyY(MB}dh(>pz(OqbC7aHA#Mt7mnU1)R{{li@-'
    'b{C4>g<^NX?p?5Z7wp~zyLZ9vU9fu>?A`^tcfsymuzMHm-UYjN!RKA@c{evL-_0$CcXMm--Q3-GH@61g%}suHbCciQ+~k*{uqwqR'
    'cXO}b-Q47NH#hm+&E3j(b5HQy+!K5^_XOX~E&X?M7x3NO1$;Mm0pHDC!1ut?J+O2SEZqZ3_rTIUuyhYB-IIRr2wPin51ictXZNIE'
    'KcXwT?t#I3VCf!Mx(Al-fu(z3>7INpFO75gJ#cm}tJ(Lmntd;;+4u6T;9l0Y?`3T}MbWZ;$-UgobT7AC-OEb%y{vTK%a?<DS@*t|'
    'F9-Ls?tL%o-uLna{9abU@8!$Ey?i;imsRk4`R08eoZSa!_rckHuyh|R-3Lqe!P0&3av!|h2NU<v_WNl2eYE{P+I}Bj0Pf=pz<qrE'
    'zYiwvJBW$w_kjC}j{Av@`-zVGiHG}%hx>_u`^h2qlSA(3=JETvdHjCv`oEu8xu00MKmEp69On7^xheF1ZVJ7hn?mm=j_xP-+)wVg'
    'pWO2REIj~A55Up`<d6s8>;X7?fE@Aw3_bu$55Up`u=D^dJpfA&q~AruwwF8rXAh*`MMKVl2Vn34a?b;B_8?jKL9+0JWZ?(N!VkjW'
    'gE06Y3_b{F55n1lu=F54dk~*J2!jujlOH4}KL~>l!r+5&_8=@hh|eCxXAd64S=MI{;<E?w*+Ve+5DY#9gAc*rLooOd3_b*d55eF='
    'F!&G*J_Lgg;lYPs@F5s{2nHX5!G~b*AsBoJ1|NdKhhXp_7<>o@AI6^#<Ijg-_hHz57<M0q-G^cKVIurtxPBO}A11;dhWUqK_hJ0`'
    'Fzh}IyAQ+e!$kPQaQ!e5{xHlxOoTrS*N?!`Be3)cEIk5CkHFF+u=EHlJpxOQz|teI^aw0Hf(IXgrAJ`t5m<TzmL7qnM_}m@Sb7AO'
    '9)YDt*&Fj{+P>(Q(H>=|%%j}q`Y5xdN0|{l%8cky)(akGy#N$E%Kn!}+5hq=bJ$0j!#>KI_@k_eKgyc;qs(X@Wxe20R-PYa7WpVU'
    'ULIw~%VRM37z{oJgO9=BV=(v_3_b>fk1=n2jCtc@%=AG)J4))3W%n`IeGGOVgWbnq_c7Rg40a!b-N%@xKE{0WF}QvVt{;Qz$Kd*L'
    'BK2`1^>JeJabojvqVaKhi^u6L9_N<#$GPSGaegu2ac+5koM?QU_<NlG;c@zh$5XD0lE2H`0RK2Qz(39n@Q-r?{NvmJ|2Q|mKLKY?'
    'z}XXIw<lom2^f5W?DhnFJ^^Q-;0YK6C1oj}ptLMu_X#rJ6L9?mnePdhe<JmDQSx^guAfL(zKW8+%P{{$x(*hy8$1EmPp~@Kj&ga_'
    'uEP`P@Facslk`VVqS2FR^dzc0i7HQ`!;|>>Nqqez8a>IcIy}j*7d#2`Pr~(+u=^yweiC0l3D-};?vwcXNqqezTt5k)Pr=z!aP}0O'
    'Jq2e^!P!%A_7t2w1!qse*;6?ADL8uy&Yps^r{L@<IC~1to`SQd;Or?ldkW5;g0rU%;w<aIr}5y^@cA@+J`JBwlP8{r-KSyqY4XI='
    'aQ!rVf`X@U<kPVGH0(Z2E_fQQpC%VP4f9Wv3!aASr^y9R!~E0af~Vp7X>!5SF#infJ_EbY!0t1!`wZ+p1G~?_?lZ9a4D5n}XYej4'
    'Elaq52Ckoh>u2El8MuB1uAhPHXW;r7xPAt%pMmRV;QAT3euljJ%t6d&J^w7@vu7EfJ<Is)S@wcI%V_OcMr+S9T6>n!+Ov#zpJlxJ'
    'EMu@|8G}8`4)13fkv+?Z>{-6qJj*wmXBmS%3un(V-hGx)*Rzbeo@Lba91K1OgU`X>b1?WE3_b^g&%xkxF!&tf-RBtZKF4_XIYzk8'
    '!R~Xg`yA{(2fNR~?sKsF9PB;^yU#JgeU1_CbFljy>^=v(&$FWYJS)1-v!eSvtKiSGzWY4uyU(+}`#kHr&$9~tJgdFWv)cPStKiSG'
    '_WL}m;Lo!c{CU=epJ!e8c~*j-XBGT;R>7ZV?e}^1dq2;9@8{V+|2(_DpJ)I43vm4cT)zO<FTm~#u=@h+z5u%~z~>9_`2q~S0B0}2'
    '*$Z&?0-U|T>iG+-p1%NRFR*|91=h=7fX^4;^930E-~5;%+RIU#q98?)MT(+OX-83-C@!ENUlxZ$=OB(-P`)hLTTxO}K=F^ki=rpv'
    'pJy+L5<?LvU)DKVO$!QTc@&qm?=S`B%L+TZK}lJ<BLozd74}j^v)}(s_fqA;;QZgxcquQeS(y9sD5^{JoA&>k-L;xW`F-LED(owX'
    'P`U@CIQPGqT_43IFJ@KAy_nUZ9mN}9UWEA<;TjaY2=gz(^^36kB7D9GgD=9_i?H-!mY3oev%JKpeK+rm?4N&;{WdSc%ZsI*<78eO'
    '?|(^9$LN=RN=u4kR32yA(8@32<d<;rOEG709~Xx4OZfUFeEkx>ekspxal9+(CAbFVpDZx{66}JaCo}AVlCqRtP*|4b`XwCs5{`Tc'
    '559!!UV`11aNWze?&U0JB`@Q_m+|1sumlQThO?Jp2^2k<;p}BtdKq3`hKZMP-OKpwWt{agZGRbOy^OP7##yi6tXFW)E4b$s+V=`A'
    '0tK(+BQCmGukd6c{y_1Q?M#63Wrf%TC1ojRps*~<;466P6}<Ec+3gja^$OYT6@2yzT)%?PUd3mx;;dJ3)~oOd3SNcXSK$*Byb8Oo'
    '!sn|n_$r*e3QMozvscM(uj0B_$!@RW!B^qs)zZ%Kpf>u&v8bN$RSMDXkA)t56@R{pKVQY4ui?+v$aSyb*4J?BYsBqqaQ#}I-Ke){'
    'M+w)U;5C?k4R%5ClkMz+!m=#aui?noaO7)v@HJfb8tlG?>t4rouan(g$Ahoq!Pj946ub^+pr|avASf+M_<S7(LGhFAe7+8Yufy5v'
    '`15rf`8pna9hP3lgRkSk*YV)%c<^;R_y!()1J}KQ>)wE~H)#7Cv=$V+!5;ZHh+9zdWXcjKEX#8C20nWOXT3podjp@n0fTSgvp4bC'
    'n>g!Dob@J5fPy#S1r(RHv-BpsfPyz+=}mZflhXok!pobS9e5Kjy-9X^6KA~%FK@D!|4sJtzlrPK#C31tx;Js%o4D>RT=y24?=3v|'
    '79M<yn0^Z#-Xd<_LWj3F!|@h6fP%MB<t>;8g->Rge+x&xg(Kg>gKxq0TX^toJoq-b?rj|THjaE7UO>Uyump<AGMs_(Wd#O7aalW`'
    'ptLMu_igwDB~Pa8zKyTnhTXUE_1pORZJhiz?7oeY-^R&r<K(w-^4mE1ZJhizPJRa`zk`$C!O8F7<abc)9W;6eRo+2|cVPY<*nNi+'
    'NAJKcD6C7C-FNWrJGk{7_<RSqzKdJm#jWq+)^~C1yR;n?ybBYcs4T+^C|_1!2^5#La|X(n6&M61WhtMav@BuwUA+4)?7oY4-^H!('
    '!tT4c^<CWhE^d7nx4w&8-^H!(;@1Bw>|YA`D=GfJ!d{#pD9R<MbNux`tl9q+*4?5-{#=TRqvhTZg^h^*F4_+oqxkP4XGN%UVfR${'
    'zWmOk=zT^1S6Io2-j|@x@mg%i;Qtl&)I=XmM7aVgjy_d{WzqJmupbMG;<qPj>AC1vkYm)ju#+o%d*^ujeo^%CBbT7)OjC5o=slQt'
    '4<_D&iT7aQJ(ze8Cf<XI_h|cjwEaEW{vK@y<=&(1@6q=6X#0D#_I-A$z0ViM_t}H>K3~M%XAjo<d>?zC?_(*7mZ78fWxj~L&o{95'
    '`I`GaUvuAQZ`%9px_X~oSMRgy3Y2@F-R<wQm+F0X_r1^VzW3SP_W_)J0B0Y-*#~g;0i1mRXCD++v!iwB+y^lD0Stb?_r?$4^8>yx'
    'egL~4z~Bck_yG)l0E3|12Qc^nd(%FE&wmpS|0W*(jpzT3=l_l8|BdHCxqsvNe-~B(q8Lk1A;v<KjfZ~|5C0|?{JSvkkDe_4cmA7O'
    '{M+dv%0|w=$rB&a+7D^%hqU%XTKgfb{gBpzav###4{7a(wDv<<`ys9UkoJ8@`#z+7|Di?yp+*0pMgO5i|Di?yp+%qol=~0u`w#8='
    '5AFL8ZTJsu_z!LPh%ZJT@x|yPz8IybB>HIc5#Q=Q;)~Hod@=fn?{OdT{pcgUAAQ94xR3an^bz0VK8l%0>KWCg5Pwlrf5exjkNDE`'
    '5vMjj;=9vFe5?D2Z*?E>-RUFFX?%<eKE?$fqb(@+F=~FCKhqmIBt{u+KStY+^CPQh`$S2IvQGXOCx1-bevBtR#uFdsXSCtVLwP^O'
    'As-XPpU~P*XzeGo7L@yh)_y{3KcTgs(ArOE?I*PM6I%NT?fZoGeM0*_p?&|QMgOHm|D{Es0F?VL?fWn7`!DVLFYWs;?fWln_%Chv'
    'FKzfQZTOTZ{*);Glqmj`DE^eV{gk-<lt}%QNd1)9{FG??lxX~vX#A9D{FG??lxX~vufU)375G!mP<={leoAb9$~WOnj7>K&Hr<2^'
    'HsOLzj7>K&Hr>Q1eN$l{d^ETy0_8RpW?<2vqzIIjCH=!D`iD(;5ETAhho})9qnbo-$VSH|qGJ=eU{hh96K#9SZ7R%j;>qDAoVAJQ'
    'k5GsB?{e|`;-6Fs|1O$vZe|{^8Ll_O^=7!<4A-0CdNW*ahU?964a#k%_uUM;n_+h|?1IAoCClz+*xd}fn_+h|3~q+O%`mtb2DiZ3'
    '7C74iXItQG3!H6%vn{X$%5A}sptLOEYzv%ifiqC}cUjK1z}Xf!+kywTz}Xg9+KRKb!qQe)+6qfsVQDKYZH1++ums9&#Y<b^Wh=aF'
    'g%?oxzhrsY3NKsXWh+c<g^6vnb{nnTMr*gxzHLO#Hd+hHZNn3wq%1no7)`*6KxtXR#5R}!g->Rg2vO(Q1<`U$9)<A`M2jrj;AI;z'
    'whi}eBZF;&!EMCfwuAW0#@}|>-446kVRt+1Zii1$ZaaK}lCqRfP+FGoxg9=1;geZDx5MXl7~BqL+hJ)tyzF2ezJq!A4rbmvn0fDD'
    'uDyfV^$yl9cCdD_gY#pc+zw8Yfs(THj4dcFOGX|$n6ZPxC-V%3Z3tr2z6*E<`+j$@yL|_{+jlUx-@#hR4%SL`uvW4Yu6M%qPS!kj'
    '!u(E{-^rTCPITDGn#WF5*$MNY+)kJWC1ok|ptLMuekaU>!Y3o<qZRAOt~=3TCwsGZqRLM8X75C!ovgU*M3r5vOYLG^Y8UHLyI7an'
    'g+{y3XcwyNLX}<UunXpQ5f8hFhh3-w%I#v6Y8R_iyI_77%!9)JCCl|L*xd!6yYT!jJiqH8cC((}h39wS`Q3268?JZ5^=`P{4cEKj'
    'dN*9}hU?vMy&JA~!!;<kn+O1<WeM}UVSYEvgTlYdGQS(<cf<T{nBNWayJ3De%<qQz-7vq02-rge>_L@1sImuD_MplhveX_l+Ji=W'
    '$WnVyY!6v#5BlvvBT#M+@vsL~_MplhQ~`zmOEwejL8ConqCF_KhfK5w{q~TF_Mq5axZVrbd*OO7T<?YJy>Pu3uJ^+AUbx;1*L&f5'
    'FI<Cidx-~7T9z=s7v}fEJShCTEc1I|elN`Lh55ZOzZd5B!u(#C-^aLaALF`xjO0MMeT?KlX<0HW*vHsyA7eLA^mmz+p?$0j?PFZG'
    'j~T;0#&!D`8Si5aX&-Ay`xpW4W7NEl@!&p2&HES~?qk%vA3pcP=YIGE<@PhL+7E;KVQ@bTf};N=!{B}x+z*5MVQ@bT?uWtsFt{HE'
    '_rubDSlSOu`(fz-EFFNQ1F!_j9l&*<v@GH50Gu6wGf?z*8O{#C*#S5^0A~l_>;NnsfTaWY>;Rk{fTg0cEH5dFc_}K(@&d{gP~x5l'
    'wKEZ;l!*{!m;gopONNOUrA!o+Wtk`{%Q6w8l!*{!n21rzL{V9`?Gb8kdogV<rtQVF9h56B%X$Kol%;b@P+FGoQVcJk=*bKd#V`?~'
    '%nUO@g&BJ>yhNxys*2&IxGd|C1Qjw-F`Ol+5M#v$F_?|906qiw4B!)#3*Zx!l%;%v(z1ll06sy{lNmk(_zd7PfWZLH0yqm`DS(#}'
    'm?(jX5|{u5pj-*OfC5nZWD<WR@KORVpa2y8FPUg8fwK}gD<R@aV5tO_N?@r3mU6I^gQXlSfdWu2M<&X_L=Gl$FaZic(f^rYA_o&W'
    'n8?9I4kmK6JxAM1X?rPcFQx6E0F*1mA)o-1JekH3C;+8TCY+VR87Kfnf0tpY6qZVfu~Jwn#V@6BRtjfja8?FqWpD<{mBA7yD$BGF'
    '6qO}=@1h}l5hyK798yNx%V>KUJy#j|rHl++hL_4<sjMu&Yc9$Xxde4A52CbRQU-%%<nl83EF+hf9mH-nmzTqJIb4^+H7HjO*Py5@'
    '!!;->%Ww@!%Mz~3;kq2I%i+2luFGM!9CpiLw;VppVXz#|I>1r~Sn2>vpj-!70wrZ>q=KTd41=JkEW;ouDT`t{nwS=W(z1ll4)7VG'
    '&M`01WH66H*F_|ibRecXFb?Se^Br(`2bk{w^BwSY2XyFwuREYh2YlV(AdRxV?ucR?QLH11fpQ&D43w0mih-iCjAEduETb4GDN7Xt'
    'rDcg?9Z{?!igiSzj;PWR9Xg^zN0{#j*BxQE6MS}p&ra|O3P8C|unP)6(UTcIK>;XwGQ%z?0HseR`K1%=c7okb<d9A<*a-$Z!C)sC'
    '>;!|IVX!j{c7{Pv0LpcSK~Mlno=n{e3P9158LmMAD0(u(H7EcjPo};G1)%iFM2F7k&>5F^#^s$+r8BB@MwQN}(iv3_Da)?<9a5HE'
    '=Sxw%&KIHfmAx3HYk4tB*S!-|Soc1pEW5H-K*{Yohm>Vk_6jJuUFVRp?6;l*O71u-pyYO)L&~!2e20`}SN0;*zLpoGboDMq>AH7<'
    '3hUk>%G|XRqx5#27^QbeC8%(RRD{~^+Bu{wd!J4_itf|t0`pzUvg@r~(4h-DbScZOw{}657^Um2UC^itI&?t?P|yWcx}XXuc{0_g'
    '3mSpaClkfGpjel(?8<Bx^y^ZVU778InlVaOX1kzmm$K~5NnKDgM(NE-UC_2mS@!0nE~we1EPD%3JIduzyV6}yx@%eX>qmsz*WkP2'
    'g0AS^72Ug{bXT<PO8j*t{<@-jS9C9+<hHP`W!W37x}sQD6zhscT~VbgI&>w*x)NhuQKc(7bS1{R5@TIar7O%=z-|TXR={or>{h^T'
    '1?*P9ZUyXCz-|TXRuD%O#8CxYSHN`zTvxz#1zcCabp>2kz;y*&SHN`zTvxz#1zcAg#C6u?mAJeT9V*eGl3Z7bDwU{GNv^9zqe^mJ'
    'C5ly|N+qg*f=VKw5>+Zur4m&t$yt?XR7uXNM6pV8RwepXlCvsNtdg8niGG#jtV$HCBxhBkUlkfvp-~kYRiRN88dafD6&h8cQ570h'
    'p-~kYfr2XHsERlOrB5dMRiR%M`c<J{75Y`7UlsaQp<fmHRiR%M`c<J{75Y`7UlsaQp<fk!PSrtbW}~rNS$3y(x3cU`?QUh+o!Tji'
    'cWOtd{k%oDvh2R?Ze`hh+uh2t=Pg2%*~J~BbQgDm3g;~%)V`-XL51@c-O92%yt|cUcX)>=bI(@+CEtBxl<xQLR+io29ijH~79q-<'
    'w}?>tp6+gC*}J@Al-}i)pu*i~5o*8LD?x?3(YiCw>CQZ-J2MSXE<#b_jb<-NS&E{v%*?GjGlmFth@T8QCsD3|l3oAZ^BxST4ja)u'
    '@4>LrVYR#G`+(BYC<40Y`+yLYBxR95Lmo<#zl;1C-QAZj3+Exxnb#m}dv;x_JM-}Ftd4YNhS{CDOoZA`AcUwxQtRkenFK|(4pB*r'
    ';#!x)T*r+KYaLw(7@?%rC8f#VCAAJwQWn=bx)-E-S#pZExHxHha*8+lY!J0C`Bk`RCRLnEP_i}?{V&;hRd?2Adf<W{xS$6v0Ofk%'
    '0#I6(oc8E}CwkzC9_Zc!ReGRG4^-)aDm_r82deZyl^&?l166vUN)J@&fhs*vr3cLSfcYLU-vj1*!hBDd?+NpuTu+z>MP(VTd%|^3'
    ';t!PTi4HyU{X>-Mf|8#3{vrDH#ym=6vnSEmllbdN#Pvkmo@m<>HG86FPt@#Lmi+ozY5a4Q35seKwl_hk(mm0(Cu;UYzn(-@Pt@#*'
    'e$^;ejbha(2Fg{V7$_}EVx=1Ws?o0+jjG|Z8a}Jxvl>3D;j<b(tKqX6KC9ug8a}Jxvl<4gVXzkr_JYA)FbE1jxnA%I3P91589sZ#'
    'XD{Lb6o7KQV7?d8(TnKlMLa|(`Xz<<TYQk9=$4#ll`KXb<LJmGs6AGCp<gfb>xF*3(61Nz^+K@-C3T5@$S*-rUBa>i#dV34?uDAY'
    'h>l)p+Y4=bqit`r?Txme0F>*Ewx9r%KAA*LZ<Owh(!J5IH|+L?-QKX<8+LocZg1G_4ZFQzw>RwehTY!q*&9ClFf#7L$hZ$9<35ax'
    '`!E*n!&tZvqu)M^e)}-q?ZXJS4<p<@jBxuf!tKKdw+|!S5M|CVMyUM^V;@Gieaf;o*~Tb6wb+NzZy!d#eHic7;K&*rS%V`%xf(nO'
    'ipnx8>!7qO@n8)etRdTg!oSP*sWpsuYse@yjCX73Z)+Iu){s$Z=q+mKEovB9)es#uL`MxhLJec78sedbu~ZGcMGa%A8sedbY*WJs'
    'w}x1$VVqUNSA`nBTGkL%HH^V(aY!u=sl_3nTrCa(MP(U>fYP$WA+<Q97KebszsvSHwe&f)xThAs)Z&m@JW-1$YVkxZE~v!?wPeLw'
    'vSKX`sl^kuxS$r@Ytg+HrEAf)7B%b8uMYj{&<~WWLqAYdmeCKCl%-$GKxtW`W*usR!Y8we)e-M?=vPO)*P&(|@m`0vb$pMjW1m1B'
    'O4kwnbtqkjnsvl`9op6r?{z3$N4(dedmXyh5$|=lppJO2!xMGHd)+|}$;NwM{L&Y{^u;frTwnYGipny60VQRrUqESD;+MYo1r$D+'
    'jsCtwe_y=R7x(nVFMV-HUmVgGPxQqFeTnzJ#Cu;H(iczk#RYxQy)U}=Md`k1+ZQ$K(XSr;>d_ArfO7Sy2?{{blNoJ60VsVk$?WxL'
    'TaUJ&02KZ&S*7byx*l!onOoE|x2R`sQIGERWcGTLu1D#5l&(kHdd9o;jCbo9@7AMxJ-XMUdp)|>qk99oH=uh1x`P5xt^wUa0VsMh'
    'qdO=7B~PXi4hlf&lZhu9@B}CTg@2dzL<62^z!MF4q5)4d;E4u2(LgR}z!MF4q5)4d;E4u2(SRo!@I(WiXuuN<c%lJMG~kJTW!d{N'
    'Qxwe#iVG;nm&HG5-#NO`u%rl-FU!v+iV7%*?~epUPsTH%=<dT@5h!04-TfWXTLg;BI>mR22Km2BQNAqEs8E(iNm+99V^O}WfTFU@'
    'O{k!JS>c9XP*RrOEeQ(CvNy~2E6d(>9HaE+&VFUtyCwUTWpD26pH(H-KdVYumerv@%!7jd=+GbL`@?mA*zFIW{b8^_ob`vL{_xU2'
    '%S3ViEE5SzZ`te*6a5Q2mZF~=3i=oJIhI6qi&1=AW>{7-Am%0d78!k|8Gw@q;N$@~c|e}Q`0Gy50QdyupDeID00u$PlNkm<Nm<Gu'
    'C@RbF2};URK0#qw)@K87)&Te%fU^c>Im@Gh&j#YNfv^M$2Ey4uSOP^)W;h!NO9SC$AWRIT?E~@BK-@Es)(*ry198tl+%pKj48kvi'
    '@XMgG?9IS~Xzie~?C)@Zf<a~3yK)OC`JEV0^knAVdQiTs@GA?TxU8KsP`<1Xo1mmDWfv5dWq%c5P+9hODhA=YL1ec<cyJJ^48ntr'
    'xULb`HD<XEQI=~^&<OL5a19C?VZITr8)3H*J{w`M5zZR3EEP9qS&C7+TN}xIjd-^amKw{l_XIbVW$y`&QF>2sBQ9^m<&C)fP+Wc}'
    'E<Y5PA4*Jv@?`}b4y9iK#ZR`Y0?L;abO1$V8C5{}vVumSxU5|<P`<37A1EnH)dYoQ*$6n42so4oIFtxDln6K!Z4V^^1``2;iGacA'
    'Fc{`R!C-V44D*BGdNAw`hR?w;I2g_b!_r_pKN!ys#`A;m{9rsk7+wbB<iR+3FisvqZ$AWI55d<%@b!?g?49pJ$mK)m<A%WXkh1J8'
    '=tE!^6bvEv41sG<^kjx>P*Rq14GPP$jvRsqhv2#)usa0T4W;iNiU)_{!J%2s@~DuLhr$^s7z%@+xU8K|P+FF-I}|=a(UTc=hr;Jj'
    '7#xaQhvLtnIC3bQ4J8W?B?}KF3lGJ+L-FoVygLl<4#T^{@a{0YI}EOekr_bwCkxCEgHKTOWQIXdT-MGfC@D+X1%+i<e-6W+!|>-Y'
    'xE_W-oA757{%pdZP4EH=nqa93UO@4a?JPCHOA|~q(e@^s)r7N}a8?toZNe{2_@xQI496kEama95G@S7@C>Wlf<3;P$B}K!T@qywe'
    '+sEagd|6>O2ujM*5j-d=%P<Jamlb*$P*Rq14GPP$&KgedI~<=4hxy_7tQluD<E&=b1qID;-3+^+pc$^4VYeARn_;jS&YEGV8D5%k'
    'T{Hb{GahV)iRS$3Pgu`fRL^8xKRTjZQrwI`oAGBe{v1I*8-ZI#;MNgD>Im2!k>@kIpr9m03A><R1YD1RPf+}1JD;GaEW<7+DNES}'
    'g=JaSjlgFkV0Q#QYaySt;JOxE*8)qRpasrAQCWsTP+FGo*#d*0_{nxYTVSvS&RSrp1rN61x)yk8!F4UTt_9b%;JOxEHxi$X#AhR6'
    'X(X*3nUA=5_!6N^i$KB1vh1(Tj3oX*$&)D)ps+0Kmyu+tk+^3hERDoHt@x!CzqHa?P|!--L2+3-6QHOp!%HhnfPz+dX@!Z_vg|MI'
    'w3cOmTc;Jjw34%0aZhW?OVp%RSZYmKik#hAmi<kh*0Stx^0ekx!AnY#|0VhMSyGb!yNn}SabzowY{ikSIC2z@9EBrCq0uN*8AZf_'
    'f>CHRirxa0Jefu+C@RaS3Cfoh^aCYjshXg$EbHr0_<9t+9))6~@O2x$Zo}7Ya0Uw6U=S3Swe#5qgP@=dKHFfh4bIwNsSRG*aB>??'
    'Zo|oKIJpg8+Hi6kZf(P@ZMd}!x3=NdHr(2VTSwDtkH)*B@$P8)qtU1`nm%VVs*KL-5Q~{d1sz70Wq;*sG+cv%(d3@dFb@i!%sO&3'
    '9vltVqw(Mvdgd`Watw|f0~4TN47`A%vJ6Y0d|81rP+Zo|ASho};1d*;W!MF!WeL|~U>B4;nQ}dbTt0?eK86SwgXhQK`7!7)2G5Tn'
    'dygS|k0Bn$5D#OBhcU#%7~)|J@i2yX7)v~iB_75S4`Xq`SactY(qqwfENYG=OM!y1Xgij?1d5)_s0m8SQvE<-SvFS25-VfTXe_ZZ'
    'j#wE-tc)X8#=#OO7zbyds4T-EC|_3K6BL)VvkOYg60XO=E+~02<$4_Kj)Tu}czzt7ABX41!RI(UKMr4y!`I{R^*DSz4quPM*W>W@'
    'czit`UysMv<56rp8jVMl@#ruf=EuYC_&lGvXscL+GI?n{xo3P?_V*jd!!;<Zb=IxpVRt-koq$^>;MNJabpmY%1ruNb6qRLo0p-gI'
    'EP>*(cFsWgvI2vkq%7qV6qRMz1?9^MT!WIblzC8Emgq2nK41cUzyu;-0ue9)jV2HQ6Uh1#$odnAjtNA^1fpXC(J_JOm_T$)AUY-z'
    '9TSO;iA2Xl95NA4OvD8f(S0IHPej{^s5z0`0}AVs)d3WiW#eHYTu&q(CJ_&lh=)nU!z5Y@3MSEZP*j#-0+cT+@B)g<+F1hS%L<%<'
    'lCqRRP+FGoISB?Q;nqpGbrK9t!mX2V<Rlz92}e%Ck&|%bBpf*jM^46rlkwnWzE@2~hsk^=nauh%D41N9{q^0+eE$Q*Pqz1epnO?j'
    'Mg&UAQm#Q^S@!F|WWJ|PW>hknIpt(rJ{gTB<MJu^dJ4Xt!q=-QFbE2!z$Yjw%dk5IK0(10*qs8OQ($lkoK4}Y!W6!)PGRIRh56<b'
    'd_4u0rj%uWm3T^7_E(9g@SST4-?^snoofnCo`RF7;N+>~)~Wb<D!!h|SJ|n!d@7k}DvC|zE8<iXn_8Cr{pqPF1`4L4-&8aL#ZR_t'
    '1PaTtzMhJcr{dkIs4^ArPW%5{-FJW#RrdDrnVueJ08x>}95Ao%MmH&&5D)>gfJhpm<UB(T6JSQtM1mxLu3^nN=dfl)Ma&U%1OY(>'
    'jBi(US9g8*Z_n09*ZDrrxpnTXTUCtE?QwE@oZOzfvhDG8dzcX=+Cz{iJeK20lsOjBB?^wkSQBNBrOCI4HBtDNIr8mc-JW`APX)Bc'
    '^X;MA9?!SO^X>6`dpzGB&$q|(?eTnjJbyASKN**wjIU2dhm)auGL%k+3sK@^`nr=DQHauindM28Iu>{9$&9-v<K2^?dotebfLlA@'
    ')(-fy1Gy6=IzWObI2PkV6dub_>Hrs_L<cB!fJ+BD+zxcO9dKO-#@!BhumhAj(BXEV!|i}SJK)a___G84?0`Qz;Li^DvjhI@$e7#_'
    'w|2y>9T}55;@ysnFC9^{BV$NM)a=MO(GfK}GJENWnna0?XxkC}h*EzU_jN~{+!2jB;^a<@!kzGSCw$$BQMeN>?*t{HL?@ULg~xIP'
    'i899`o<za17+s>wv4}NMcq~VrD0?ieLnp`+rT;RkLnrE}6Lr*yI_gB_bV8L*R8A)<rxTUaiOT6j<#eKQI#D^DsGLqzPA4ko6e{Nw'
    'D(4g`=M*aE6e{NwJaGyxI0fBLLFrS__7v1S1^rGzqf?mMpMpk2sT|_faSA$|LUnYeIyzGwovDt_R7Yp3qcbFk5}n~f6dub_BFY?#'
    'm=OiXVg!jY$0D9Y;jtWDqRg>~HBtIlmON4RSXzh9)JkV+r8Cvh8C5z{9i6F;&QwQds-rX2(V6P#Om%doIyzGwovDsf!#69mXr4OD'
    'Ow_C>j8ck)QH!GH!5Ey#526;$Qc>^#We^3g&uX4m5WI6N8zqCcAe<V!_aHUFE)3pkmWi4N-^<7zYo4E)TZhNO2dbI}A63XNI5m9h'
    'R~QxKC&DQ8>#6apAU{8df?p3hqA&^`uWFtM{=4L<;oB2hG*A7Dg<%xD>#cc+IxiiCzZXWqyA;xYnOE3_+{36vvvjs$)S{?akZp=Y'
    '7jo~iNBCleAorALT_Di~5?vtC1rl8#(FGD=lscC%_b>|1B|k7hq6;LtKq8D%|6L;Z@4_g@r3+lTz@-aZy27O^p6H4vy27O^B)UQ('
    'ijtWq%_Ugx$wg^OU7^$!E?sd*R~*t6E?wc$6%t(`(Usi0k$X2h(G5>@Blm82q8lW-L82QZx<R5FB)UPO8zj2nkZw4n8zj0xq8kqB'
    '2A6Jd=?0h6aKUM~;50~_M((GP`)TBN8u^_@J)DNpr=j#|<aZi5oEE+-Fq3T}j8gwyD%)iEm%#uX{AG&ZX=HmE^>7-wpHA+lll$r9'
    'emc3IPVT3p`|0R@I$TbN%ju9f9TKNQ;&e!y4vEttaXKVUhs5dRen!w2q}-GKCgd4Wb%gH}JtN{0e2yh~M#LrfL~_9y5tm@eI2Q%4'
    'w@IX<=9zbjp0P)`K+rt>jm9(f2wTkN>8}AsQLqA$$UBpBIg@iaGpf|^1I=efl^V1m$ul{ZGdY(tIhQjzmoqt+Gj}_ea1t5*UVh$L'
    'oLLy9j)m_x4WihYoyD1*#hIPOnVrR%oyD1jQBcL<`&7^3%+A{F%+gWt9@a$O*)TgB{mw?evpKV~IkU4lm$RXCHs^8<zjqEK&Vj@^'
    '{N6eI-Z}i<IsD!^yZv4~_jCEZbNRh<`Mq=by>t1!b76fhzjy9#zZYlS9Zz(JM0dz{hkSR=tUG7c9Zz)6oM-xLoZUI=?ojF;jT41I'
    '-<*z`XWoF@gY)dcdG>%{4+!?)JbQ4SJvh%EoM#Wtvqy$*e(>6@Ac~!J59szFhaTk6lN@?de?7^eCpq*aho0onlN@?-);&4vo;ai@'
    'XWf&t?#Wr72kZ0j#Cdq)JkIkx&htFzp2vBf2ha03mtOpOFDUhbQZIhJ7r)+%U+=}Q_kvO{&ZQTWdU0mwb1vs|F6VPD=W{OS^XupH'
    '>*u4<`TY9%{CaOXz}{T@dvopY&9y%p1+N6k>&+FtH@!^|1@pSXWHK+AiNe#&{C7c=>I=eS@t&_Yoj`9of!=fiz3KUS(--vS`re0Z'
    '`;cuPvh72*eaN;ColYNe??X4!2NHeAy${*;A=^G=+lOrXkZm8b?L%+Vhc2%VB>F<4FP(p1I{&_q=nILy<ldKT`=Wbaa_@`oeIe18'
    'UcWEBeqTuRg+yO^{l0MNOYZ&1y&t*vBlmvf-jCe-;evjU=!XmX!KEK0`jLA-a_>j({m8u^x%VUYe&pT{PxQkR{ov9cF8!&F{!~YQ'
    'xb%lh6eTlJoJ;?VCz8P{WwKG)A^qXfA1?i=j{a0ff4KCAOMgi8C)*OTEg{<yvMnLo60$8J+Y&rc!W^iCIZz2)O7KewluF=I0+$lF'
    'l)$9~E+ud&flCPvDS^@eC=H-i22d*lpfmtV1E4g3+y{{D06Z~(+y{{R0BU6bwK9O*2ax*!YGnW<29Wzeavw<U1Ic|Lxep}wf#g0A'
    'hYZ9a198YeC=J9R17S80N&}%Z5K04~G!RMyp)?Rm1EDk!zYK)gAnIrkbu<V{gP=5sYzHx74#E?I$aWA{l0nqNAnIWd*$yJ3L98AO'
    'V)bAUs|SO~b}-ovCfmVeJD6+-<ATBDJ{YA3Lt-$w4<_5eWILE_2b1k!vK>segUNO<N)P7RF&Gj<ATb0ILm)8(5<{qtA&?k?%ZK2C'
    'A&?jXi6M{}0*N7z7y^kQkQf4qA!Iw0Y=@HVP_i9LwnNEwC@vVvSTK~aU?^OM;*g<G8VZ-8a2X1hp>P=rm!WVO3YVd98Hz)OLg@nL'
    'sTVK<yMX!M1<e1lQTXQSbkscaHLDAl16{zZ^#W!@7cc|6fR&74oXarIWf<o&jB^>ruMgw*hVgsD_`Ttf7|yQ`=huhx>%;l=;gA^4'
    'xeSNIaOSDQInUvo=kUlA!PeJAI%=NzBG+(cio==Bk06H;<S>F9Mv%h@&UysrIfC;X!Fi70JV$V5Be_nGq&7!Vo7pIM;cnhYs%j)7'
    '?MOzOkz8d`QH$Wk=fS(oqo{fKVWxs?6jWnyEPgE>Ni~k78b@;V9Z5Bgq^d@d?I^MxMYf~Jb`&GgC~_Y~?xV<k6eG$gNQ@%)QDi%c'
    'Y)6spD6$<zwxh^)G}(?O+tFk@nrugt?Px~Y(d0gw(R4H<Mw9z!vK>vfqsewO*^VaL(PTTC@pCj+*wK&}1Bo$^7z2qhkcgsWCW_}i'
    '2BpVjd>xcnK{iUed<?mdA@?!lK8D=Kkoy>NA47g)$!{$AjU~Ua<TsZ5#-jUJuD4^!eJt0_v5**x?qlIH77}A2F%}YIAu$#bV<9mX'
    '65}8-4ie)aF%A;rATbUS;~+7PdKgFNF^<k-9L&a1E8`$I4rb$EHV$UvU^WhB<6t%pX5(Nsj>;Ja!SOH~53}(w8&7`Yss8bJVmu??'
    'c&cMO`HklqFrNIzlizqU8c)|Xo~~;=UDtTBoj|q|$aVtRPQVir$bAC2PayXRXgdKC6Uco6*-jwa31mBgY$uTI1hSn#wiC&ABH2zP'
    '+lgd55zkK~_lfv=A|xh~`$V#xNVXHnb|TqMB-@E(JCSTB;_HcA5hg-n5+o);ViF`KF)~ad_em%{iMpMH%O{chByyib?vu!U61h(z'
    '_etbFiTp~*uax{s$*+|BO3}TPk*}28OBumRAyJC%rEn>QL@6XnAyEp6Qb?3Sq7)LPkSK#h86?UeQ3i=JNR&aMjCv^J8c@bHpbTbZ'
    ')Jhoy%V1Upvoe^K!K@5sWiTs)SsBdAU{*%ultFNEY6cdZc3$wUqGTAQPBbt03TqIh{xm$6`u#9UA4`qkLDZtCIGD|+rXH!NMes$U'
    'V8=@=N(R}dqvploH<i*+^P=Kl)|1GaoSNB$(1Kqt45I*3@asVo>?kcR2!0?h9Tf);{1oJ6qu|H$Q&IDx^s$11y!<I-G=+?UD1aTF'
    'br7`(zRi>u{6xVNa+pF6Q^;WoIZPpkDdZ4Dp}4{C1yL-cDP%N-jHZy$)aa~(7sm%tntWj1WE3T0QR+PNf>Mp5L@o->Ixnzm6eXf4'
    'O(GGzSAJ@gd+=qEWHt(3hF=gxiP*8!@8t)VyeLZKqTu)PgUdw}B{ETlOOR1s6s2aqsrl{HJpv;ar~DakN=MC$Q~zLLUOGzsD{1eh'
    'qTnt4#i`QFOGm-?dxG!n<`quE1=DcBG<-b`Ur)o=)9}PJJP}2SSQI%ViW0df>z61>WTLoxrs1Ax8NUR7nV&Ze_e{e*(?Y-GhrgGf'
    'KMnUxhs1P9Os5{EQxDV0eLA^MC->>(KAqgBllydXpHA-6$$dJNGaVAsAu$~i(;+b(5;Lfr8Pv)Qs$&KfFoO!1f#+x7@)?;cLXdef'
    'Z${>dkg|9x!zc<rVjV`oj_+Vcc_JO9t_Z=kqaYK78;HUvob&|$O8D!!D4EJA-36th@ZU^VPJSrhj7;U^hm|uUQ#tuz<;)1K0qOG$'
    '|CO*D(x3AVqs*D5MuRX)pIPc~I!bSC3ZoXm^8(?wHVT3$*y*1PqC^-4|6O6QLq8pbVrHVCQUfmGxkOQFFq(-*Gtp=!8qGwbnP@Z<'
    'jb@_JOjMbP4l~hVW=4n9|4j8gGf`zGs?3D^OvulK{7mT1gzik}&V=qv=+1=hOz6&p?o8;;%8h)fYMGTA`BL>UD>w2b3lg)Uu^{Yw'
    'X643$g7mS>Sdco^S-CDK{L5??l%hK;H)9BorJ03KU!?xKw0G0}(ySDvqV!l$7@S$q+Js|4VL=#W5-bdUy;-n{C+K@p15+5a2(CxL'
    ')Bm$#y-j{PN}pNyduf*^gAYRmQTR^==NWLxMu|++JQzdrQ!rvtB8rMrf0>`c7K;+;C}f?w0);t5Q6du+1^-IwSTYtRqA2)R^78WI'
    'Q3}j#6q}7=vr%j|ibYW}8|Czyjeb#-%tYA^H>KZfw4IH%vqLq*zYPDoxVE!19cQ{vo{iG8QF=B?&qnFlC_NjcXQT9Nl%Acbj%4`p'
    'u2__aqDc4I=sp|WXQTUUbf1mxv(bGvy3a=U+2}qS-Djiw9CV+9?sL$64!X}l_c`c32i@nO`<&D)BtQJ`0^Or1t@|95o`ceJP<jqZ'
    '&q3)qC_M+I=b-c)l%9jqb5L^*`prSHIcPKoRpy|>9LSeLz8v!9kS~XPIpoVBUk>?l$d^-b<y2fb<jY}Q4&8F-mP5B3y5-O<r*g_O'
    'SDAv;x#SndqC^y>I`LHHB;rvb6J;x|9F5AUs&X_cr*g{CsGQ0vN3jYtsz9R(G^#+O3N)%fqY5;tK%)w(qk`(FK%)vYsz9R(G^#+O'
    '3N)%fqY8AWfP4k4E1+8e&k6`u(q~oDXI0W?Rnliw(q~0cA{IqmS0!CnWyaUR7pDvJD(RCe>BuVS$SUc`Dl@FZX=*_{O6FJ6kyX+s'
    'S7ua6{bl%j@vga&-mQ|}t&-lYlCHUuPOg$pu9DuZGBZyNau5HNC`zQGTwhm7Usp*dS4k&Vg??4&SA~96=vRe)Rp?iRepTpKg??2i'
    'R)u0!8O4H`S~44@^{b+zu0qW!^s7RZDpaXLl`3?oLWe4Js6vM-bf`jyDs-qqhbnZK%i2s7C88*%(Ofi|i$-%<e~F?*Hp=NY7yag<'
    '-(2*Yi+*!6^XY<c#U+Z8;fl*#beM|{b7PegoJ+29(oqU;^I)bO{F}w$z!c1HgWQYL3zw-2Nf5==oQs-sQFAV;%w>gVF68HN4VcF@'
    'U>?_id0YdcC_$9WM!74(Jgx}ya%&#3D4B`k*YJ5<!{>2*n8)>D9@mF?Tp#9feVE5}dS1rYiQqb&j75nk3f5nOp)VFCGEunxlDZZb'
    '#G*tx%3b^Cam|^>wSOL0pm|*T=W#un$Mt<4*Q09mt46<S^s7d{YV@l{ziRZWM!#zGt46<SuJ6@c->cED8vUx#uNwWT(XSefs!^pH'
    '9jYN;4eM&?R>QM~(WZvcriRg`h7qNP5v7I^rG^ouh7qNPD?$xdgqqA1A^5UuK{iTXA8NQh)Nn<pVI-<yB&uNysbLJMVGOC^icrHf'
    'poVKe4WmsB*MJ&E{Tjxe3t3aWkTul{SzW%6)#VFWUCu@Y!LsIskzzr6k&Xh^!EK?u3t1_>kd@L4Sq;6A`v^hQqFL%#ux~9B6$c-Z'
    'P306t;p1_ssCiNPSn3b+=ab)j@|#b7^T}^M`OPQ4`Q$gB{N}T|JfHRC`K%z%hs1nH%!kB$)`jQ8Wj-Y4vr0T45(}c-14{%^I@_Qv'
    'NGzb@vQhZ0_66LRSwJ-|;J(ZPYI6biWfnyF1;3sbMZp!eAdGT%O%`z1WC3?g7I4>O0oT+8+%;LSN6Ib1v0!Uq7=_1DRPqWJLSi9('
    '&qBB?gv&y>EQHHKxGaRrLbxo1%R;y;<ZjYJxGaRrLbxo1%R;y;gv%nbT||D1$Zrw(Eh4`~<hO|Y7Lnf~`oTqv(2K}+5!o&x+eKu%'
    'h-?>;?IN;WO!Y6O`WI9Ei>dy_RR3bCKZ+8uC>jf*D3Ob@BSRD=GEuzx7gPO<ss6>8kuUh~^0QHT99&HGFAnQHKm7Il{KZs%EhK6o'
    'Q45J$NYp~27813PsD(r=Bx)g13yE4r%v$cp)iQq8azCz?(X^KPakbE`g>Ef(;A&xA%Sc-b`C3@la(Awlakmy7YSE#NimRjI>Zq|g'
    's;Z94sbkflj*g{{yK{APEOpFb>$ne8M~_m+szVTkj~Jy&Gkq+I!eg;Dh&p<kI(nNrdYd}dAnLetS4ZDd$4t16drNinM0NB%b<BP1'
    'xVKbCPgF-wRF}D01o`C^)}vTGiq)f7J&M(%SUnomqe?xh)YC`SqftE?)uT#1<m(|{5BYlN)<d@*y7kblhi*M|>!Di@-FoQOL$`ss'
    'Qv-9S2Ifu;xv?iDL<2La2IfZ%%vu|`*VDj#yaw(7G-P;&?@bG$*d2fd=0^?8j~bXCHL(8K!1`wccK{lg2{&+8uYtQe4cr}QU>&-F'
    'mC^?8?lf@cpn*AT19Pqh)~Fj;VQt{<P6PKC8ukdmhs=UA3!m9YjeMz5G7}XCbF+f{FbaRKAaH9K1-}qP$#fL_WnM~_Mm*7oCmQiY'
    'Bc6z&WE905(#Y((5x+DtgKlI6q!BMQ;-yCB(~WqkG4xWnYpx)QB4;%+^KQgvjrgn)pEcsMMts(Y&l>SrBR*?nm7|e)cq6WB#C46h'
    't`XNY;<`p$*NE#Haa|*>Ys7VpxULb`HHNNB(+$on?!iVp*oX%k@n9n!Y{Y|2c(4f%HsQf0JlKQ>oA6*09&EycO?a@0Rh%YPahh;l'
    '6RvB*bxpXg3D-5@x+YxLgzK7cT@$Wr!gWo!t_f!~;iV?r(}Z7|a7YuLXu<_exS$CaG~t3KT+oCIns7lAE?9yKmf(UVxL^q`Sb__d'
    ';DRN%U<oc*f(w=~5-njQT7nCfp!*V(UV^qu&~^#hE<xKRXuE_lWC<&*OIYVy!V2pWR{fSR_AJ36OBi34;E*MZAxm(`62_1v_+?3;'
    'd$@X+Qob-9rOqXIMQb|Bx@QS~S%O2B;E<(wVkw?jiYJ!hiKTdADV|u0Czj%grFdc~Bg0ZghNXC7DV|u0Czj%grFdc~o>+<}mg0$}'
    '=)M%Cm!j=b)Le>wOHphoiY-O4r6{%(#g?MjQWRT82fvICK8g~tDC*~z(a$fVpI^r6@-kMCmoYnAM(4kb&VL!5|1#E$mvK*c8J+(!'
    'W@pPXN+*K3X+b=Sjzx2XWz5``aW8op^SEWqCYCXqSjKE(8S}Vh%q^BNw^+t(Vj1h#%UHi&#!O=wGmT};EtWC2Se9A!3vy3KxtYdt'
    'T(BG$EXM`Qalvw2upAdG#|6uA!E$t8j_%93bFds2ENA|=98WCA1<TQWIZ7`_zvbw+9Q~G~*m4wGj$+GEY&nW8N3rE7wj9Nlqu6p3'
    'TaIEEu}&LBi71M#(?(Gu8|9R~2&FGV>5EYMB9y);vuacjuFOVJGF-8~h`Y`gp~FS!kcv_xd#GP{X5lMk0{t>kv*50Cplx0l6=jsp'
    'Pe&Q0Q&C*ai%|0-)Vzq*(2JmZ5o_WX!FmO(SHOA&YsM?s8L$E!R-nTQbXb87E6`yDI;=p473i>nyZ<ZDVFfy@K!+9F;a|ZW{uSKe'
    'Ux8vPP;3Q?tw6CAD7FH{R-o7l6kCB}D^P3&8m&Z!mFTb%)+=GX64onWy%N?dS*>5m?v0g<d@C9GR-(#ER9VRgwvrKSC5o*?v6bxC'
    'Sjm2km8iKAHCLkMN_1F>4lB`NCF9vjR9VTGwGxe1qR}e4!&P*LtLP3_(H*YJt)<7JWE91E#Z~MYSViZ!iq3Hr`vg|eN3LRSv5L9H'
    'D*DJ(^pUIRBUjN!uA+}zMIX6}`NJx9eXL?f!76rrtYUw`Dt3LWVz<F6<|M1=O;<4|Sw*M1iaE(D`qov<J66%Rt_oZbDi-WLNJqi_'
    'j^IlNt0IR4y=nNDxt?|vJ?$!b+EsM1tMSrmytEoGt;S2M@zQF%v>Gq1#!IX5(rUc48ZWKJORJfatY%KK8ZWKJORMqHYP_@>FRjK)'
    'tMSWf9I_futi}ba(S0>auSVO|XuBG1SEKD}v|Ww1tI>8f+OA=|Uc-33hVgn0<MkTG>ottYYZ#N)(2cI48(qV$mNoRIYv@ha(2cHP'
    'EMLP|zJ{@U4P*HlM&UJ#!fP0X*U*iwq5oV%|G9?odJX;O8amE3jNWS)z1J{$U(8+7i@8gBF;5s?%oBze=c+0tSvm^uTBgqBV(xEV'
    '%pJ{(xrcc%cP%gGuI0r%MR+lHEidM-<;Cm|xtKeXsVHpkgRj)&CH^m-Z90mw4Wn$fL6plj|Nr9I=KWth+f)?Gp@69H|Kb@H5QWFG'
    '`4tca$D$D>{JkJ*UL1@B;qL{vT2s0Q38tgw#mQjPTsmqVP)cN@AopN2kD^5IVS`kZUb#$r@Dlp0OQ_UK*cEXJwRs7<A}*m)FJV{2'
    'B@w}3>qEgMbX`%Dh#d>}t)+f4iW1o<xBKl9o@c&<{ce}=Jo6>&e!GO{nJ-~a#wF~@xP(0!m#`<}682<VLicnDdouom>;8l5{)6lO'
    'gX{i->;8k!hzkFM&xpcfIiC>)$6`MF56=2e=1m6$!R0m+g)iBRqO7z2gR}mFvo0m~OUeCGa=(<^FD3U&$(^Y1QgSB>kL7YF3Xa8c'
    'zm(iBCHG4+x#tI${%n*caVaD&&AjCyKfE7sY33~tdEr|gF3r5xA^nD+OQCcbqwr;n!j~}$U&bhW8KdxJx!xulMPqUlC9+X&guaX&'
    'D3>u_U&aoU%NV^cV+YD*sB#%PTn72e*pG4<Bl~5H?3c0U<T6I~%fgX8JeDfl%NXY`$90$Ey329h<+$#0Tz5I+{N;F%sPJ+;NE9B+'
    'd5|bL7W3fcjPsY{$jce$FVBqgDL<whc{!v0<v8;4*lKou;pMpQ3MgFxr7NIx1(dFU(iKp;0!l=MS3rp<JeH$G6da3Dx&lg9K<SDM'
    'rGl_huYlPVFuMXuS3v0sDE${o|Ao?jq4ZxU{TE9Ag$q&Pf8jzD9?Nkd3Xa9N{5L})nDivFQJTwt;qqTd{1+1cg~Wd$aU~?Kgv6DQ'
    'xDpaqLgLEYoGTke?unvgCW<p7D!dYAMB%X<Gos*FjM<eLFD1i~=t`V*CCsjb*_AN65@uJz>?)XD1+%MQb`{L7g4tCty9zEug;&9a'
    'C_I+qLKGZ}X0)kVxe7{GLFp=db`_Mag3?t`x(Z5HLFwuor4;(BbCgmib9IhVB8(zRsgt>yx&75S5~&&3)w$eLv(c+_*(SoMS>{}l'
    'iFA~{$CpeWE6%=u>1x)Au4XsP)$FXgn*9Y=a~JVy?jl~zu7RuBfpRtXgs*0o$<^HVy_(%3*Ff+Z2wnrhYan<H1g~K|<QjNh1J7&V'
    'c?~?Tf#)^wyoOb{YoL1#bgyBp<QnK+1Kn$&dku82VXf;LSYHF{YhZm1tgnIfwXnVx*4M)NT3BBT>uX_sEv&DF^|i3R7S`9o`dV0D'
    '%PQ5itWsSI-D{zHEp)Gi?zPap4ieWv;yOrN2Z`$-aUCSCgT!@^xDFE6LE<_{T!+uD!)Mo#`*mb{9ob&T3hQ;Osa}V(uER^$;hyWE'
    'bUl==htl;>x*kf`L+N@bT@R(}p>#czu7}d~IOKX9ay^u;htl;>x`Aul4P4`H;2L)W*SH(F#@)bGji~Sju4+W#vD{USC^#0oj@>{{'
    'bVFv2mk1V#vr&4+cLOuN8@P_$z#Q)e=6E+S$Gd@R+>KDW5lS~g=|(8s2&EgLL{xYql!(G(IZ8yqu^6QrxxU{Bvm0S{Bb080(v48M'
    '5lS~g=|(8s1f`pxbQ6?rg3?V;x`}@2CYTWw-UKtE@K}x+QE)8QFWm&en;>`-%x;3&O)$F&W;em?CYap>vzxhVax-^LZsxAZ&5SQM'
    'Grru+^S3uMV&2S^`DXf_o4Iz}%sq{pxu<b6_cU&1M7fy}<z}ujH*?j#nUVHpuG%+q_v&Uw;hVXJ-@=%D3uE#vjLEk^_ZH~h0?%9E'
    'c?$$@f#59=yaj@{K=2j_-U72*V0H`4Zh_e?FuMh2x4`TcnB4-iTOn~PByPoLx5DLCxZKKh>{eWND_8AXA$ThUZ{_NAD+F(a;H?n6'
    '6%XDD&s*VnD?D%IYJV$qZ-wry(7hG9w?g+;=-vk1+n{?JbZ>+1ZP2|9y0=01Hm>%!akak<p0~mCHhA6!&)eX68$54==WX!3o%*|-'
    '`n#R_yB#jK!{v5J+zyG`A#pp-x*ccTj<aru#O;u{9TK-g;&yVso!oEVE%&&WZpTZv<E7j2((QQZcD!^uUb+LicR=?J=-vU{JD__9'
    'bnk%f9nif4XWfCb?tteV@Vo<_cfj)wc-{feJK%XIIowGOcTzcblF^-HbSD|zN#)#$d+x+Ncaq<oWOOGP-AS$7Nq%>d-<`}m?quF^'
    'C+@iuzubvK?!+N?LFq0i-36t)pmZ0M?t;=?P`V2j+=UD7g3?`3x(iBoLFq0i-36t)arxc2{BB%+H@V+U?st>z-DG<=+1`x{?#2ao'
    'li%IscQ^UnO-6U`mQh^yyV3n_biW(j??(5#(fuAM-2<h2pmYzE?t#)hP`U?7_dw|$TyPIAxCcu2K<OSR-2<h2pmZ;HtM6r3;Jw_t'
    'zL&ez_i}&wUhYWW%N^-^*#~$pccky-9`wE3b-tJT%=fZK@Lu)^-pgLUd)e!EFMIv&Wv}18?De~sT_*Rk%j8~mncU0$>HARnK9s(X'
    'vEV**zYpE-V=vWxxZplUhWn_T`>34z@Wg$1;yyfaA0xwk?5MksJ#_c6YwkX(>OQLKKC0?I>gawb-4CVvp>#i#?uXL-P`V#V_e1G^'
    'D(8MG=YA;N52gE|bU&0Hp!y%6`X8YBA0XQY$o2v9dw~2NAioF5?*Vjw0No!TqX)?70Wx|3r5`})2T=L}lzsrEA3*5`Q2IeAJqV=-'
    'q4Xe>9)!|^P<jwb4?^idC_RYo52E{nP<jwb4?^i7_7FV89)gG1Ly(Pvw^$UUqs&_@f+)75;34)9JjAYnhuA0Z5IX}NVvXe?R#hHi'
    '9pxeJ{y)Us|A*Mu^$>UeAL4$05C!6fZ=5K2m^Gw_Swni5HKd2*B=R4QlL(^NiqgZ}r+k<dC8ENISy3VikL6aBh=OCWHKd2R7x^%&'
    'a1V1|`(f_>Kg^2K!|cp?m{p^P_Xrb8F-!er{v){O5!~|#?s)|FJc4^3fy5)^{s`GVLbi{P?IUFS2-!YDwvUkQBV_wXJloWn#U1j<'
    'Zn>wQl?|Sh%}YFzc^)>{E16gDzbuKA<r7hqh((!ee>O^FqcpSN;{QK7mMBWZj-~#Ua6pTqL=<Jlm*DL;QIv>9;jbt2vQZ)%<+`B%'
    'v4ih_^hEz-2jBnbkp9OGzW=dL?tko)BTAihdR!{VPgQk6I!cYgDb@4BD7T~Tf9$CHA3N&)N5}F%cGNuz-AAGOD0Cl%?xWCs6iSam'
    '=}{;>3Z+M(^eB`brK^0DosEyuM?T8V#z*NYA7y9bqx6`Mva|6~I?hMg+4v}mJ&IyPDH3s29z~T$QRPuoc@$M1W88g=arZIC-NzVr'
    'A7i9_jIoud@G-_#qVQO5Y$Xbg#YUUQ7+)Ua&d+1)?t6^!<uS&W#~4i?V?=qJ(e!af)5jT2A7?auoNON_zsJewaWZ<Gj2<VW$I0k%'
    'GJ2eh9%saSe7B6^W8~wEkx!ue6X^Z~x<7&LPoVn~=uTAl1iBN2$8x$81;=8Po`BL5P<n#<GEczl379>>U79DjOY;PGX`a9#PwWvU'
    '8$2tJ%+G%Ux=-SlC-KXZ_~l9b@+6d=gv*nVcoGs%LgGnCJPC;>A@L+6p2ROtlHZfN<(Ga_Mey8ue&R{I^dw$-3KCC2;weZx1&OD!'
    's{pwu>Pn(05k;{M_bK+wK1IL#6nkc$qWgV{J+n{I3qQr4*{A4?pJLDKQ|R{;`aOkyPqAnADZ1vT=$fBm&+Jol%}=ps_9=Skr@{^?'
    '^A5Lyr|6fSrox}5!k?zXpQgf}rlWqEdViXZ`e~}4sPJj3pC~+*tA3*3Sj_WJ(_=nO1w2iU`82!Oo~Gk`nhJQDJ#9}@?@xyn5WcM;'
    'RS!>756|H8XK?v5xcnJh{tPaE2A4mB%b$VZGcbDwO3y&)87MsirDve@43wUM(lbzcCQhl~8Agp~aNRSw?imO^vm3$eyD(BC$}@~8'
    '&*a{P5&m9$e0dfpKZ}!}#mUd&<Y#g6vpD%#oct_KCMtXuCliIoa!w`+j>R;37LA@oqi5NV`7DY(i(=2B(X%-DS)Bar9^vER!83j-'
    '9iBy%XHjJ>zFv#3*W&B7_<AkAUW>2S;_J2WTnoXqFk1_=wJ=)?v$Zf=3$wK_TMM(b_<AkAUW>2S;_J2WTno>&yYb9EU72$ET0FlN'
    '&#%SvYw`SZc>Xy&{~Vrw4$nV_%b&y7M1{}cYohR2&euf2v6x2Bv2W%%G<pt=o<o)AP~|zC{2WexE+ij5yP8boKZg#_p~G|N@I1bL'
    '9$!C?ub;=)&*SUoVfH+fo`=ixaCsgs&%@<;xI7P+=i%}^ZhaoNJ`b1Y;qp9Op5Kj2_F3S<MB;he`aEuZ9=AS^Tc5|RFW}Y}aO(@W'
    '^#$A-Maftcjn`3>jG~yYUtq7;3ykG2@I1l`Q~*)o3seA6cq~@|M8UC`(l4;n{sqRY7f|{IlzsuFU!VeBpaNb<=@<S&L2y6m1(bdP'
    'rC&hlbyUDQDqtNIu#O5?M+K}yqjik)>lo+Pq1ZY!T8Ap@&|w|q*TH%ntk=PM9jw>EdL69S!FnB4wT`M<$2DLb*MN2Cunry8p~Je}'
    'bcom3I%;ekHMWi#TStw(NR7QnjlD>Xy-1C{h<-0pM=zq$i_{8H;fvG?QFts@D@4Ju*q+N5QS(LAe323JMbvx|HD5%{7pa^Vshk%>'
    '#frms8zk~yM86jqKVL-67g6&?)Lc(ht*5HiQ&sD!s`XUWdQ@4D4(lPm9@gujyB@mhp}QWs>!G_Iy6d649=hwPmG#uhdg!i)?t191'
    'hwggluHTJr{OYux%2`k4tfz9;Q#tFYoR_#$_!4&tU*b;TOF6|-r}h$e17BkI{!8rMe~I1uFR^?7C3f$>#M2%xad-74_O!jke$$uO'
    'gY{BoM?v`RzSMcf_g%cizKfUGb@dYa)?Q*i%1i89dx`xhFR@eYWq7^}&zIr(GCW_-c|IM*=)TO|)t6!YGOS;Q^~<n+8P+eu`ep8G'
    'zYO`8A^$S>Z(oM|%bA@W!9q=tLtKZK(cxuuco`jD=DzmJsPZzZyo@R@qsq&u@(QZFf-0||$}6by3aY$<DzBi*E2#1cs=R_Kub|2+'
    'sPYP`yuy9-SGbS<3Oc-k4zHlYE9meFI=q4oub{&#xe+WiY`hA=S0VT+1Yd>Vs}Ot@g0DjGRS3Qc!B-*pDg<AJ;Hx<KRh;}P%wC1k'
    't8jT0F0Zl+<5hNHyoy_2#h<U@$k!nF8U$a1;A;?k4T7&h@HGg&2Eo@L_!<OXgWzird=1yVhU;E~;A;?k4T7&h@HM>jI^EjqbZf8E'
    't-VgS_B#F9>vUv9g|E|*5rxNc9T`z@EY>Bw&dl_6o_l$ndkn90kKuK?gx9&h@;didUg!SG>-1-@hxZ?XeR8Sa%YU7_5wFu1yg}FX'
    '23^-1bX{-Ib-e+zH=y(eT;71o8*q68E^ol)4Y<4kmpAB_-XPmI$o7rhvQ58}EA^MDPUj8o#JoY@^9G&Ho4D>xT=yofdlT2aiR<3P'
    'bwq`4;yR-6Sk84s!Lb<KH|a*-g!P-SeiOQHLibHv_a?4;6W6_o>)xa{eG^sQM3pyD<t;q;79M;H559#5--6&<FnbG1Z$arTD7^)x'
    'x1jVEl-`2UTX^s-a(|25-y-+7cFR59m%oKS-@>17;m^15=iB)6ZT$H*{(KvMzRhguZQS}cbEmiQE>Ypzc$X+Vmh&!Aa4a^<dK-=2'
    'Mx(b;<!w}X8&%%MyKm#&xAE@Vc=v7QTyLZ1+o<_AYQBw{@8INjaPm7i`5m164m!L8`FCLb4s_pv=R5Fx2cGZ1^Bs7;1J8Hh`3^3B'
    '2TJci=^ZG&1EqI%qZIf2J9z#bJpT@!e+SRMOHcGJJ<+@LMDNlQz00oEciFZ2E*;Xlbb#+NmwA_2<h%6H@6t8D%Rbe2*{Aw0eb2k}'
    'J@3*{zsp?aU3$fLnajM(Zr*q4Bj06avjKt|Ah-d78z8uWu5trBH^6fPJU7sBZlK%V0P78~-azNL0oEJnBR4>P1LQYAegot;Kz;+{'
    'H_)YTK!*+JumK%5pu+}q*nkf2p~HLV@E$t6hYs(d!+YrP9y+{-4)3AEd-Uw@(X+n?`S&3I9^~JH{Ckjp5AyFp{yoUQ2l@Bt{NIPt'
    '`%roxO7BDIeJH&TrT3xqK9t^v()+meecbv!l-`HS`;d4a67NIeeMr2|yzzbJjql^g_wnHSxbA&i_W=YyfZzuZ`~ZR<K=1<yegMG_'
    'Aou|UKfq@n;Ij`P_yGhzfZzuZ`~ZR<K=1?H^C5eeKV-M^hwPyJkR7xi@<i2#?4bRS9myZE2l+$x(|*Vf+7H<?`yo$8eaMqhAM*6m'
    'hdllCAx}SjnB@}eGyX8M&p1EaXZ#^gMt#VWQ6KVT)Q9Y7{Rl1}!Q~^kd<2(|$o(U7|A^c_Vu$cY><RveUBDl)@Ao5i`hEn#k0AIF'
    '1V4h{M-co7N*_V#BPe|YrH`qqkEyDUsj82us*iK`En-nJiefePF*WuvHTE&j(tJ$Ceax8kF=N)pRNTi@+{aYh$5h<MJb&~t&mVov'
    '^G6>uf_=;g_Aw*a$BbE@!1EJ$ege-=;Q0wWKY`~b@caaxpTP4Iczy!UPZ+^IVFddGo}a+;6L@|C&rcYoK4t#!Df5R<`A+Yre5W@X'
    'g<B~<jYgvI6T6@C)!t9}PVc9DnfFs>8lN)L_%yS+oH~{g@Kg3&e#)~+pYo03Px)@{r+lmZQ@)Lxioyv*@Y?gd#AlHB3=*F~;xkBm'
    '28qug@fjpOgT!Z$_>BFnpRuF$Gxo542D8s#_8H7RgV|^7Q~eBrpTX=icCCH}v(I4mIbU)4oU7C4e5vJgo}T%fE7#{dJ@YwZ`R6<r'
    '@;M{>=R6nkIph52JQwmgUp@bvufc!LlNq1$^vvfxJ@YxwX?)Ie8lUr=#^;RJpYxo?=X@3CbG{V+1w6mt`u7ENzku!+(ES3sUqJT@'
    '=zam+FQEGcbiaV^7ts9zx?k|z%NNl70=i#7_Y3HL0o^a4`vr8rfbN%6@t0KbmsIhWRPmQo@t4`}3gx1xrlTm4jdB(KC0{82l6wD='
    'FO+{t^?%71%D<$-zof#y%-st~;r)_&|B`zDlCOz>$r$-1_5LN_5C4*S|1zxi{NnWUTwhZC8)3Z>)*E5H5!M@Fy%E+MVZ9O78)3Z>'
    ')*E5H5!M@Fy%E+M8Fx4GT){?0;f*|3u#qu&BhM9VM8A#bw-Nm|qTfcIGT4Zk8yUSfqU}c1+{hCM8yU+tqVz_T-iXp0QF;^I%qF^-'
    'O*u7FN^IiGFq`OfHt~g*O>~EwSby2XTGuANIlGCk%x+?ZU{mJnS-~E*;9TNe&?dT|P0ZsqF^}8Cn!qN$B(#aIW^ZC`W)t6>-NY<;'
    '6JMm<#JbHUzDK)>-gFb+iP^;LdJ|u=+{6mcCca#|iEq_z;!BpB_*U&Ez8bTM?^<r+TeV+huT=q;ujq`w!Y^Opm#^^4S2*M=Jn<Et'
    '_zF*ah3;Rm7W5S^_$u?Aw4mIBV{uP>g(tqk6JOzpukgfI=>8Q-e}%SRq2^cU_Z5n5hS_GAZH8GCC9_ek;x_a3rOnXY%-mu#)wr22'
    'ENx~Uw;5G7qsnH!x3rl`-OSgQHdD8onZ0aA&CQuF;sy69g8brYZbrY&=(idDHlyEW^xI5LZ)R?|neQ}hM(NE|_-1t9Ooea81)Hhx'
    '&3Ixn6}}mVY^K6D@8*|yg>UBDPn)Ut&D8s5>U}fyzL|R8OucWxpIh+f7W}yde{R8_Tkz)={J8~xZo!{h@aGoh#aoycZ^4mUaO4&o'
    'xdlgV!I4{V<Q5#c1xIedky~)&796<+M{dE9TX5YLe6|H=ZNW=haL*R}vIU21!6934$QB&31&3_GAzN_B796sbD?$_{vr+E)u$8rv'
    'tvG8d&f1Ezw&JX<xMwTw*~$pEl@V+!BiL4S--_;ASykD}Rc0%m*or5%X1>%Jw1ert%w2)D;+L)XWh;K!ieI+km#vIhTN$OcGA?ap'
    'B-+Z@vz5_iE91-8sQEQ&evO)6qvqGB`88^OjhbJh=GUnCHEMoMy?;%;e~o@$qu<x)_ci)`jecLF-`D8(HTr#xeqW>C*XZ{(`hAUl'
    'U$Y9g4QAV5whd<6V7861bsJ;rHh6A>=QhUHZH%qksGMz7&Njx@ZH%Vd&|w>Nx4~>1%(lU78_c$Go!-X!?l!))xQ*4`ZG3rg8?~~H'
    'k#-xkvW<~;8?~~Hk#-xEvyE|g8{cT$#y1+bF$!;E+}*}VyN!`{I}X{7L$>3P?KosR4%v=Fw&RfPIAl8x*^WcDQ;plH#_c#{I}X{7'
    'L$>3P?KosR4%v=Fw&RfPxL`ZFZ%66vXuBOXx1-;7^xKYp+tF`3`fW$Q?dbOnqv<z{rr$7{e#2<`4Z44W?%$yMH|YKi+J1w!-%#P-'
    'P~qR8(Kn2r-=NqxjFI1<-#6&@4f=h9e&0~j-%!QhP`BSusozkW-%yR;!unfSe+%nxVf`(vzlHU;u>Ka--@^J^Sbs~cd`qo-3+r!T'
    '{VlA&h4r_v{ub8X!unfSf6F!JJJy=N;|uKHvDW+@Yt7&B&GqkCYyOVa<?mQe{*D#o@A%64cYN*sJMO1`$M?~{<NN5}@qP5~_&)k~'
    'd>{Qg?pA-t-RkeS5BnYWVZY-(?02j@f5%Gx4tVZ>=MGl#cW@_r2dsC%dIzj`z<LL)cffiFtareA2luXbz<LMwu6J<ndI$Hecc97+'
    'RM~+lJ5Xf@s_a0O9jLMcRd%4t4piBJDm$s-omBBos(5E^<vA85vr+E4xsxwk@8l}Flj`5e-Q1mw1v|N>?&J&CJGsK{WQ5+y2)&al'
    '>`tz*I~h@SGKTDA)Y!?Wv6DV)CwJU;^7ZST+<)K6x3G6|H-0By#@@*|zmu!>PDcHmT*G&A4cN&QeJ9s|om|m(@<r{Pd{KKRU)0{o'
    ')qW>e`<-0vcXEB-h0k{3vt9UX7e3pC&vxOnUHEJlKHG)QcHy&K_-q$G+l9||;j>*_opy0`+J(<{;j>-%Y!^P;h0k{3vt4*;7w*}G'
    'Uv}Y;U3g*_F4%?cyU=|Xy6-~wUFg0G-FKn;E_DB%?&ACGI3JIa*(ld*e9vx?@98|g$4lSirSI|5_ju`hy!1T|`5uRSk3+s^eEFX7'
    '<$JXKp04D3l>VNs<a>1g9^JoZMERaE<a<Vq?-?h)XJq)EvEX~E{|8k00aboLl^;;$2UPh1RenH~A5i57RQUl_en6EUP~`_y`2kga'
    'pc;Rm8h=2QA5i57RQUl_en6EUP~`{u!5_Js`y+RAf6UR%FDUpi+RK<Kq(l(K?&ki;{o5b8WBVibXn*9c?2p_t{gHd7KXRA!NA8RM'
    '$Uc@Ixy$_{_eFnXC(w_%rwmdJ#*f?y{gHd0K@|LLesEK^;3p{k1f`##^b?eRg3?b=`Uy%uLFp$b{lwkspSVB$6L+M4g6B{0{0W{v'
    '!Sg5XGyeqLpWyiu1b^Z_^H1>n37$W}^JjSe49}n8`7=C!=4qCnd6&u0ykqcZ-YWPr1b>F$&k+0>f<Hs>XPEsAv!7x1Gn9UY($BmB'
    '@Mqpo@-viv;c2U1c-rchIHmkw;*`QD_w3a#yp`t{p1t~oH}CwyvsXlgzwqo8QE)8w1kf+M)#VqSdi#a<eEq`v>we*RpkH`P>MuM)'
    '^$Sn=<Q2ue6h>JuWuwqb=_vA25aqm-jv_DR6~%K8qinXRD3)zHin0x&T(;>b$~KI$*`}i?+bBwBn^zQfPb?}7qPSo3isF9BE0Rn6'
    'nWiAhJ=2t56yK$ujlx-L6eVKEq8;o}l!&6(95#v)u_&6gMo}Ug<>s(al!!&qj5dlAxhOlojiN**itk2?qV!%rqC^no_NEb~j>UJX'
    'rK4!4S`g)Ss->f7r&<_gcdF$V#b>4=vFuK@{G#~kLFl>cKEMR3Bv2)RDhX6cph}`BzUq)bqXZfy&?tdM2{cNeQ38z;Xp}&s1R5pK'
    'C{YyOF_=IVqEtq4RT8L@K$QflBv2)RDhX66h>szOg7_Gci^7q%AU<jYQEW6Vh>sctM1=+MF{FSfI2IdG3K&DeDEq8>I*Q&5T)-Go'
    'z!*{xA2m|H5FZ(mjF?GA%p@abk})z#MoDr=l0%XllH`yiha@>9$sx%&m}DGG?v_z}tV=T16{2k++7_a1A=(zAZ6Vqc6&9i`QE)8A'
    'r4TNKa49T`KOI{Lr9vnb7R8@EPDQb2kAo=p>~SG3C@hLUD_aP`J@CXHcw!Gcu?L>m0}^|X`yS-J2f6P-?t75?9^}3Ux$l7|_P`T+'
    'kl!A=<rjb6cMtrs2YxAnL=hy4AQ450SQK>^QIv?H*gPPL60s<n6+}@Y8|CH*QIv>9QC}BDiCmPOKSWU?6U7xPLa|g7+ou{txfw$$'
    'igmw1l-r9MMd=w>I*MitsedH8H<9{(iqJ3hhq0Zh=_r~%1pi2GXKFf%W)tBL6otpae>2_%6{BA<`W2&JG5QswUorX>qhB%l6{BA<'
    '`W2&JG5QswUorX>qhB%l6&J<lGEtO>MbXSAiW0dfJI{%tL?()Rq8LvU<B4KCQCt+?yIhPz(or-&D#kCxIHVYd6yuQMqWHe%bQH~`'
    'ig8ad?kUDS#ki*!_Y~uvX1J#r?rDa5n&F;ixThKJX~u{dMTuAx%{!tf5k;{XZ4@P9Q8d4eqC_^zIiwj5X@*0Z;gDuHq!|urhC`a+'
    'kY>1`87^ps3!0&HGn8(I(#=ph6~*46pN^s#bhD!P8$X*dKWc{3%}}~IeL-{jg68xE&EwjJQLam99@j63Vm(9ixJIcc-a!x*Hm8Fi'
    '3Xa9DqRp9aHs_k!ocU(+qWD`On=|`t&Na1pQTz>@&FLAM7scQ8*qm!>3u>hWwbFuGX+f>DpjKK?D=ny%7Su`$YNZ9W(gL0>AlL$e'
    'Eg;wef-NA}0)j0d*aCtr@O6tg&oIilyagRg3%uI`@3z3ZE%0s&RB5rBD)F~$wxH8#Q51j6W()eBJ*kI1sfRtOhdrr>J*kI1sfRtO'
    'hdrr>J*fwx!ab=6qTpCe%{@_bPt@GADE^kzJ<)bgwA~Xm_oN>7q#pJxioXeUPjuK59a>TyEvb%{R7Xpyqb1eRlImzlb+n{9T2dV?'
    'sg9P=Z3)ko@N5asmhfx|&zA6P3D1`BY)N&rq&iws9WAMjmQ+Ves-q><(UR(DiAF8asO4@N#otfclFDgG<+P-7T2eWCQ8{~2IeSq#'
    'dr>QUQ5}0x4@8A~Q4d7Hv6y~)6~*7bv={pAg?@XX*j^~M7ZtD<6|h%P{B2Bo!Fn%P?*;3<sfWF(hrOwXy{U)2@%-L+es3u44VS&)'
    'vNv4zhRfb?*&8l<!)0%ryf;qX8z=9LllO+%-Z0x6W_$0(EdB<oy>aW_xOH#bx;Jj!8@KL*Tlc}O`{33nO2(pS)Q_TMHp=-rijuJ?'
    'x*|kTGKyjq5JkyY6kRQ%D4B`kwL(<554A!R9E*8kpQ891w)bJ=+XqkVgD3XE6Z=pr`%o+U6vf}Ey$`zYgYNsFdn;<C6}8feT4_bC'
    'v_i2~TuEASC256zt*Eh9)L1LjY{gZk6<3*7Xxj=kTcKYo6l;Y>t<b0y8nr^BR%p};jas2mE9$ltb=!)%ZAIO-;tJG?D^M%0K&`j}'
    'wL<q+=-vw5TkWQMyuw>i;jO6fR#bQ^Dtuomd|xVjUn+cG{IV}qyf3=%OQr6Mw);|zM1}iOjYPq**n0%`MfZKteP2fJebIeibl(@<'
    '_oX)Xr8f61ioauUUliMy@p@nM+ZX-zMZeb6ZENbbHFevXx^0aPt*OS=RAXyYX^jr8A>SI-tzq37)~#XP8rH30-5S=dVcnV<YfX){'
    'rp8)RW3ADlH9E9Lht}xO8Xa2irbGO?*_x_qO;xp~s#;T3t*NSC6~*5d^sA!y`+|N|6yJyRtD^W`qhA%pcLM#YDE|KIUlqmQfBmbX'
    '_#3aoDEr3iUlqmQx*kT^y<6!hda^Bw(oanPswn<sR1oE!g-S)SC!Bs&6yHN0M%g{&zbcA9#gvL-&z*%)c87jCik>?QqTCMsbQC>l'
    ')&`z!;MoSAZHnSMx!ORtO;LRBRvTEiDT?p2Y6JN;kZ%L|Hjr-v`8GxIJ#=l*p$$5;DT?piYJ(1KisC!D+Mr6CqWDg(HfYoajoP45'
    '8#HQD6yG)12F2Q-SQ`{;gJNw^Y(Es+55@LFvHehNKNQ;!#r8w7{ZMQ_6x$EQ_CvA#P;5UG+pj3Tziz*x`2M>6&}ct2+7FHPL!<rB'
    'Xg@UC4~_Oiqy5lmzoPg~y#1lOKXmtp?*7o-AG-TPcYo;a58eHtyFYaIhwlE+-Jc5Bp9<I?p8G>^f0*qLrTw9_e^GolXgZ2^gYJ*7'
    '_s7Zm<J|+`c>p{Qfad}5JOG{t!1Dlj9sth+;CTQ%4}j+Z@H_y29)Ld&fad}5JOG{t!1Dlj9)Qmdq&qy2?(jgm!vpCD52OP;ke-jI'
    '@IZP#qTpDp^Ei-s_<=?7w?!Yw9pVGILwq2e$AR1rKal(32Xa6BKsvw!i{fvRK9IY|2hvX*L|=CheceIybqCSA9R!zyAaM{R4uZr%'
    'kT?hu2SMT>NE}3;br5~lL1cRn*&ei8w(&P*AH<#WgXotIqC+|uXB~{Q4#rsr<E(>m*1<T7sPJH%MHC#1@jRF=_F(894Bdm_c`!T='
    '##smBtb=jZ!8q$+`qqOXe=y_^hWsJ;>=1l*2tGRmpB)0FL*Q}<Tn>TDA#gbaE{DM75V#zI&kn(7hmiXr<bDXbAF^BS@t*w<Ja`Bm'
    'JOmFOf(H-9gNNe5L-F9D%()K5k%uzNIuw5%%AD&^+)7k<C~hSRj>YC<hoaG;Xmlv59EvK3qROGT^-$b;C~iFzw;sw2>`?SO6#WiG'
    'zeCaQFuZ#h-aQQO9tQctaPnc0KMdA~LH96t9tO|D;CUE44}<4n@H`BjhvD+WaQR^{I}B!r!R#=Y9kv^@xaSYU^M~R2!|?oJc>ZuY'
    'ox|yL4yV&OoZjZ}qWF_8hZn`4bUB<(=Wx2b!<pwC&V2K5dg#OHnh&Q>KD;RYjLP9f@n=*Hr<*yPZsu@$=);-W98N!YI5V5Wi{eiX'
    '9Zs)!IP;vg@N5guw(x9A=hzmyZRs4_!n!T2+rqjnU1eLk?Y8L979HBsE4D?4wsekdQKc<?WLq?9i$-nHs4W_`MWeQ8)RvyTEsC{8'
    'v9>7I7RB14SX&f30>zF%u_I9I2oyU4#g0I+BT(!J6gvXNjzF;^=;x21pFaYPjzFU$(C7#>Is%Q3K%*nj=m<1A0*#J9qa)Dh2<8Y!'
    '!t+RY9tqDQ;dvxHkA&xu@H`TpN5b<+cpgaw97zQn3C|-TcqGh@gwl~vIuc4pLg`56qDL|pJrZ9ZiIb1SyGP>Pqo8{fbdQ4WQP4dK'
    'x<^6xDCiyq-J_s;6m*Zmtw-V3qo8{fbdQ4WQP4dKx<^6xDCi!A>yGC6hogD^;pn3Hn-z}c`G=!<#^Gq5YB-wb7>?%2g`;^^;pn3H'
    '`x2rk{ceh*i{kG~IJzkQrh}u4;%_=Qx+wmpgQJV$Z#p=-DE_8{ql@BiIyky0{-%SYi{fuOIGQIHj^+uHV_<d+%#MNCF)%xZr$mk^'
    'iocuU7<e87&tu?u3_Op4=P~d+rYQdYiDTe-Oi}#(6UP+A-#>9oQT+WA$3XrV$R7jwV<3MF<d1>;F_1q7^2b2_SnBpz>h@Ub_SmBM'
    'lgP(X#m7>`#}>t(L_U_9K9-t3mYP16nm)ED{(SMVRQR!spT{zO9!rHEONAdxg&#|WA4`QFTNHoJI~_&Oc^_L8f6n_@M$=;%O^;<X'
    'J(ltFILIFd`Qspe9ORFK{Be*!4)VuA{y4}V2l?Y5e;nkGgZy!ft;aF89tZj3Ab%X>kAwVikUx&`^Vcb~0k-s6hf!*p5Ku}-!OSBC'
    'Iz{l;!5ADw1p&cq6uuoIj8cV^&hOVbzoc^bb*|&g9t%7F@K|yBQMYi08Aidq!ql&)qwsEB>eusAzn9+89;}AuC&MW9mx<sn!>C!d'
    'D+#0Q8%okq^cLn{X9%Ww{yNi3rDq|(j`cQqg<+I^8|d*+Ivz^LL+N-Z9S@}_O6H<0vnWbtqHO)eqBPIr;dwj+kB8v#5Ii1&$3yUV'
    '2p$i?<6(9@l)@<c=8xlH_Wx4Vk#cDBAcKM+N)rrj7Z?7&h+z1j(*KJHhL3t>qu_b2f-njw6$WqnNJq_!@`9%+Q~zcv3^EFSAukmb'
    '=VyK)KO5x-FZ)PGncvIL`weFnMyX>3;mX2qIJ4hyX20Rge#4plhBNyOXBI{Q>);oHD0XJQ+3n2IQSj=4MBZ;<_FK;Ex18B;IkVq#'
    'X20cJeha1FaxTB+Tz<#z{f^)J9l!TGe(!hu-tWl$cl_S(cKf|}?!PDZ-*Ya%=Ujfzx%{4A|2^3fC4SGj{GM|mO8kLe{{z4N2Y&qz'
    '{Q4ir{SW-!ANajL?Dl(c5`V<4e}u~)IkP`<W`E?&{)k3@#I1kKoOQ4dDfqp34u8z#5KJn=V=<n8B!@pnqfM~ay&#N&)~YagXHPmx'
    '&1Qn<JMvE;qZ6pV6UgWUGCF~bP9UQb$mj%eIDs5aK$R27;RJFxfgDaChd-gipE&D3an^t0tpCJW{|WMc;;jF~S^o+0f8wnF#99A|'
    'v;H$@_GixQ&z#wxIkP`=E`R1+{tUrCb1r}8T>i|t`~_xz;mrQRnf-+``wNta5`W=5|H63^1%DYMNR&R7&4DO&ES}L{IqSc2)_>)!'
    '|H_&Dl`|ts{1u*m<y?qTe;GfQztNTajjrTxbS2p+Tp|Bkq;xP<%ljMM#oy@9f~ZBRzb*`>YMCg#zEqHnf=)F!7Vks;Mj!Gw`jEfT'
    'hy0B`<ZtvLf1}q3qRg+SayXIPPbBvf$^ArfKat!|q(3{6j_gFZoJiMoB9u;q%ZZRU5fUdt;zUTC2#FIRaUvbriS)E5(x073PkSN+'
    'PozIP5uPW(^CWnl1kaP;8AZull%*R*$xIaIc~Zt%!R)0V8>M}A5<E|W=SlE937#jx^CWnl1kaP;a#BblJeM$sIG1*CX$O~faA^mZ'
    'c5rD2mv(SzhX>m+M`(v5+c8II#~h&@blc(9cCc;--FDDz2i<niZ3o?U&}|3ZcDS`2{%i;NcFZ5z;m>xc(hgPrP6zRKt}B0Mgw95R'
    '49UMULjRpB-rwmU{?6$Acdi{o$-mRr{hiU9DESZ0`XBT?|KP0u!CC)<v;GHX{SVIiADs0+xUT$z^ZW<r`H$VsGv0sx6T1K8Jpajg'
    '{*&|kC+GQ3&g`G?Buf61^ZY00NtFB-=khPk<zJl3zc`nFaW4OY(!coifAQ=8+U?ill>QB+e{*L4=FI-hnf;q{`8QmM5=6;=bDsa^'
    'Jc$xS$@ZLCd(NyqXV#uGYY(ON{CazSohZ?Mw_lGlJDGYo8G<Kso+opjCv%=BqwUGm!^w1xM9GuM?_~NjqTnxMst~1*WpgJ=9m|ZS'
    ';iBBh^lm598K2DDq61tyFiv!UO9!}gfJ+Csbbw0-a_>OyM9B{5-hph1QhyoGwgcIAAlnXP+Y#M6l3z#i>qveb$*&_y6D2#6ZAY>t'
    '3jQ*tG*S9kHg}@bv3Tws$-N`FcOt(|<kyM(I+0%|a_B@3M9EGl)`_zwO8sU0tUGbmojB`L(C8F$IE5TeA%{~?g(yLkJcayDAwQx7'
    'QSjfz6eCIyrT;QZf+#_h`pY<%Q{d8>+&hzdXL9dMMxDusC_$9$jDDRtYoY{E>c5Mhb!X1{RJzzx>0+}{_|lG3>0(c%Z#|VB^Hk<Q'
    'r_#ZnN{@LeGsRQsI8UYHJe3~vRC>%)=`l~Gk35y`@YHCxNcb}RF67>Y+`Eu_7jo}H?p^58yU>?+flC*9?=Dd40+%k3=mLo@kmv%5'
    'E|BO#x7~%gVHbMuF3b(PK(GtFcNchefoE5Ec7<nGct%k&8|CPBWq#BZ)?Jw&b%kzM<}zJzU03LKg>F~qc7<+N=yru}S15I5PSO=h'
    'U88%E;VZ<u!mJz2y1}d)%(}s>8_c@FtQ*X_!K@o@?Z%w48{X~4oU$8p%5ISFhOfJ!LpR8GgM2s0cY}O4$ajN$H+<a<CwD`YZp<RP'
    ';pA>8)(yqFp;$K*JB=RfG_HR^6ckeM_O85SHVS^AAdFfRrLPEybd>74g4QkkS8`YM)9A=f<7#mlSGCjVwom6=PUl=s=Uh(bTu$fL'
    'Pv`ee=l4$M_s)RC8T|Sg{Q4RE`WgKC8IU-Gb2$SNXV5d8!Fis+d7cpj;byo%z%UB7eFSnQ(ow3%4Bjr6e+J#m8T6lLlF^xDbS4>{'
    'Nk(Uq!<n4*nVj{Rob{QU^_iUYnVjcYj2dS}=MwH`$VS0`n15DuX2GbDcNTSf7FVFN7%|V{%6wL4mvdpTpCJ=v>LDA2yA4uNyu#0l'
    'GRh0qiO!<J&!VQ!qHfR1>~ape!Gip=$@XlrJ)3OLCfl<a2hS$=v&sEzazC3f>ugAzP3~ut?b&2|Hrbv{wr7*=*<^bT*`7nT=aB6='
    'WP1+Tp2Jvv4!NJhczq5e&LQ`6$o3qvJ%?=1A=`7v_8dm&bLchBfy6nGI2RJ<LgHLVL{TyqWw}IAG84r~oQv+~W?UYQ`q?P$`Ewz0'
    'E+o!{#JP|-7ZT@^?YWtq{lP#KoOL|+?&RK`+`E%|cXIDe?%m0~I}YhiU(g*c-MNN$hf;SO(j8{qq0}8p-J#SSO5LH<9ZKDy)E!Da'
    'pwt6OJ)qPBN<E;|14=!h)B{RAsHz@xNImF~dcd;>71sm0J>b~`o;~2%1D-wL*#n+E;Ms%v>jB*!(Cq=;p787m&z=zMNwz&1QF`K@'
    'o{XkFsj;49+mq``PqOVvemyhKCWW~N$HHfm($8!6B-@_kcOLnjM}Fs#-+6fAJhDBHY|kUx^U(G@azBr3&m+I{$nQMzJCFR%Bfs;='
    'uNV3CBEMeb*Ngmm;qqQ&+Y2Z6BKKZo+l%~qkzX(J>qUOO$gdaP?ZvgD7rFN$_w&j9d~!dZvEY12oX=QrKDnQdw&zo+=i}t_$^CqC'
    'KcC#sC-?Ko{e1E}pGrNSY<rV!Z?f%8w!O)=H`(^a1-%*hdPAZ&BUo>^^u`6fq0}2Lz2VXuF1_K>8!o-!(i<+l;nD{#ec;juE`8wA'
    '2QGc!(g!YmsFglk5&CdN=mWt%)KMRJ_JLp@2=;+s9|-n=U>^wffnXo1st-K-z_SlL`|?y~-`u|D)GR$41rI+a`tpwJzP#1CFYmGL'
    '%bTnF@~-N>Jfqo{w?+5m&A@$&;$O_^%NxY|@_y(jN`J$tFYkHo%bT71k!?S+?MJr#$hIHZ_9NSVWZREy`|+mbe!N?`A8%9c2bX?u'
    '=?9m7yfL{Sl={J?AMZ%+2bX?u=?|CwaOn@1C`#m_ET#Uu_q;#M`t#oN{t)cXd(ZpBvp?@W?+@Mny!X661pD(=^8WDb56}L*dAvV9'
    '>krTVyidG8Jp1!L@&3>)fo=(OOQ2f<-4f`QK(_?CCD1K_ZV7Ztpj!gn66lsdw*)7b@XqiOd|kpj!%J{^3GWOqL9r4PD?zam-XLCr'
    'ekIgH32K(0UkPszFQGb0(6$6^OVG9iZ3o1j1j$bh$f=ncdIxZQ7(iz=fGg|(`p7T}-XtA7_mYW<Q^$f2It`#J89+xpAbR^+@Q_wE'
    'N<UFGAoJvUGQ0u}h&?kBoOS$NYy+bArUj2z<qwG7h88?oo*0n%9#MXNUP18RW!{DsL<IvOF%S|1Au$jV10gXG5(6_Ng2lA_Y?S6Q'
    '5H17BeIWS_B)@^=H<0`WlHWk`8$^DC$Zrt&4I;lm<Tr@?29e(&@*6~cgUDzQ83j@1UrD7gD0<E`{Jhhk=sBs>KN<da>E}#?DD~gP'
    'b00+RgUEd_xeq4y!Q>u9E%L)BoKk0<j>5NkrZO4~iNRz$IC|4a*n<s@-W?r0w3v>vo*#_TgK_y_C=G_vV00f$?t{sFFu4yQ_aWpy'
    'gxrUa`w(&;LheJ*eF!9mklzq88bU@x$Y=-|4I!f;WHgkFhLX`xG8#%oL&<0;84V?)p=30a9EOs^P`o=7?+(SgL-FoVvK>mcL&^36'
    'vb}(8FCg0ssM`z3?*i)f0&4RD{CNRm@&%}QL1q+AKc9L5WAX)1x&TTS#QOO}DvIlVLFSDi!7hkI5XHD$ka;Ue_+h&+%2B#tH%jR@'
    'h6Hb?O%x1+*)W(5gV`{c4TIS*m<@x{FlIf&U^Wb9!(cWHO2eQu3`)b8=M00{FqjR?yh$Z^?{Pt57zBqwa2N!KL2wuZheL2U1cyU#'
    'I0T17a5w~qQ)9z39!x(KJsd|4hv0As4u{}y2o8tfaF`8;*>ETghthB;4TsWjD2;&92q=w!(g-MxfYJzN*CSvy0%jv%HUbZhfY}I`'
    'jeyw*n2mth2wXP;f+HX}0@saz=LmR?faeH!j)3P#c#eeUNO+E9wPGZ6N5XR?1V=(}Bm_r7a3lmrvOY1ARlkwY9SPl$&>acgk<c9p'
    '-I3583Eh#<9SPl$&>acgQ9SiMDn_>;F{&v3<?m6s8CYtx8^sghqjEE;L~tzry!|NN*fWYZCymPN_DSz`2%^k3vhWw;Z;DApA(&v}'
    'LvSwf=fg+wwvAD|<7HH4Z$)|+#;DBRiuCTHQM{EW79}!K_RS`-C=o@`8+&3=A|2(P;g3a$Oq6{iN-Ro5QS@$~Sd<8&aQjO}_fe4x'
    'f`zuiQMore7bG%K=;VU@FbaRYAgy%vJ<kQf?`2$25IAIXG@B1s8AtPWfziA{U^IRijbBFNm(e(6G@clZCr0Cm(da&!cLI&Z1*3T<'
    '&}cj{8c&SI6Qj|6G)j*~+tH{w8vRD2*l08gqVUYZnjXUlHii*w3?tYW#;h@15yo&07{drQh7oKG*Ud4EL}M6<#xN3%p>It`#p!SF'
    '22rew9TQOs#=$Vk^|WK?X~#sAf;W_;qWG9KhB0dlW7ZhPtTBvPW8pa#o@3!T7M^3_IhHHJSm=(0?pWxKh38m!j)mt~c597=?pWxK'
    'W$)HlSdWGESXhsR^;lSs<!Uh&@?#-C7V={uKNj-iAU_WB;~+ndYw<XA7zg=rupS5NaqOWR$KKF!Tz$uJ^&N*s<Irdv8jWMO-8d8*'
    'hhpPUY#fS>L$PrvHV(zcq1ZSS8;4@!P;4BEjYF|<C^ino#%J~(B*PJUJa?1EbN^^O+Kxxt@n}1qIvUTNpYhCy#?woUr<WQ}FEt*;'
    '#-rGH6dTW-pYe20<LREp(>;yPylFCc8)rZw&U!qo$HRI&tjEK8Jgg_cdIGE`z<L6A=O#dY0^}z^egb#kCZNLvs%ipNHG!&{fMOHS'
    'XaX8dK%)t0Gy#n!pwR?0nt(<V&}af0O+cdwXfy$hCZN#-G@5`$6VPZP8cjr_iD)ztjV7YeL^PVn{nUxvPo0Q<6B!jJqUJ>On}~iB'
    '(QhL9O+>$m=r<AlCNg49M9qn)IT1A{qUJ=@oQRqeQF9_{PDIU#s5uceC!*#=)SQT#ljue#(Tzq?G8big(<n-2quk6Uijq+j>tZMI'
    'uB%DRdZH+qiQ;b{n?(0JiSBn&<{FpY{XK~p(WG!j6gs3JilX_^B;KYqiLQB4*e8b$3G<70&6DVpC($QQqEDX0+-VZ;DvL#lD2h7j'
    'Nz9}s(O*wuCN+s}dlECLN%Y>6m`P2d6Q9IPY7%|<BxX{R!Y(~><Rp6bNs(I%f)|TTVwN?DS=J<GS(BJ$O=6ZciCI=DZY{;FrMR^e'
    'x0d48QrudKTT5|kDQ+#rt);lNl()8(^47Le{8@@WOYvtZ{w&3xrTDWHf0p9UQv6wpKTGjvDIP4vb*1>M6lay<rBd8eieF0cODTRS'
    '#V@7!r4+xE;+InVQi@+n@k<%A@+eB?qU;>KjCcN(F=H>|Eq`TrunZ5D;lVOIScV77@L3r?D`Vs<W8^Di<SWA=WjLgaw*!{33Q&f7'
    '%5YB^?-49xg`f;)mEo*1oK?nHSH|d8#&}l72v)|JRmLb)#<*05v&wK*S-5%-U2n@+OPGu&CgX|8cw#c1n2aYT<B7?5VltkXj3*}J'
    'iOG0kGM<=>Cnht#OlEwUj0+~?g2}jGGA@{m3nt@&$+%!LE|`o9CgXz1xL`7Gnw*SclTmCkicLnbDRi7ucs_0lPsB~3<D5drIfagM'
    '3SH$C`p7BF3Z~FiPNA!uLRUG3esBu?;1v47DLj)lg*o#S=FC%=Gf&}pwJFS?r!a$_!VG!}Gw3PIpr<f{o<hetg^qIy9p@A}&M9=9'
    'Q|LIS&~Z*h&8et46*Z@#=2X<2ikee-zHutEiK)ycrlR{)W)o9!!Bljgitba<eJX1#Q<)=7#S>HU#8f;nm1h{IvZ^u_zf8q1Q}N4G'
    '{4y24OvNu#@yk^FG8Ml}#V=Fw%T)X_6~9cyFH`Z$RQxg(zf8q1)6jhyx=%yRY3xgw#=eAU)bup=l}wAiRvEnTIvb^TnM`9fW*T$D'
    'X=pnQZKp+FoeX5ipT-<-TJ&Yf@KM2OP?`ppX>geiiRqA-4vFcIm`?7~qwksoo8huin#6QSOegp0<UT#~j7mYUPa!cqvp+c%r4CQe'
    'JkeMXJi?gz%Q&U!P?{cn0VS|R{&bj4huQS#n<t^`r$cZ$1gArAIs|7xa0UctKyU^GXJot-ZUf9lX=lxV?hM9>8StC|!5MIw0hbw&'
    'm;s3y<UWJkXOR00a-T`=Gs%4>xzEhxUJzEmOi0Xx#7uIZN$xZ8*-S{xgv3m|G!rk)#7i?XPsavxr67tEoC(31IBO<6XTozP&YB6`'
    'nb4gH-I>sx1>ITDodw-l@SFwDSvYGJbZ0?#7P-$N_aMsro2h?v7T1Sa(c9Al9TKy+2FzmApT(#@3of(ZG7B!V;4&L7v*9uuF0*mn'
    'Y$(l!(rmcQhRbZcG&}R=fzUl+6eu5byNUeScxg5~XTx)L$TK{%@V|@GoekaD(VObS?a{MgJsZ}uVLcnxvvK5X$j^rSY{<`s{2cnM'
    'IjqypVV!mk8qGnYIcPKo@^h&0IaK%@R#@k7C7DC@&q1*{RR0{Re-0YWL8Cd;`yA?h4y&(osQx*yo&)PS^fq%KKL_%2AYTsoa>$oM'
    'zMKxX939Hhp&T8`sg-i7qns|b9L371m2&heN569PD@U<%6e~xuauh44#>&yJ9R14CuN?i#(XSl+%F(YJ{mRj=9R14CuN?g<(60jh'
    'D$uV2{VLF}0{tqOlT<J#sX*Hbw5>qf3bd_2%?i}4K+Ou&tU%2Q)T}_w3e>DX%?jo@6=++5wiRewfwmQBTY<I}Xj_4{6=++5wiRew'
    'fwq;b)Ks!kQ^`tAB`Y<RtkhJpf?UZ8awV%cm8{}avVvU63UVc@ewD2HRkDIy$(nH`t3Q>j=~S{(Q^`tACHE#O`Nm2tN<>lg#g$l;'
    '$VAz7zDm}UD_Q5OWIef(b-qg0lPg*Et7LV#k~O5t+?Nmwg7eHcBq)J&lwDn}WIef(734}*kgIS=6%MJwAyqh}3WrqTkSZKfg+r=v'
    'NEHsL!XZ_x0amdFScOBXa7Yynslp*uIHU@PRN;aubgx3`DzvRa%_{V(Lcc2Xt3tmj^s7R@D)g&DzqzdM&SiafF6+B<S>K(@`tDrT'
    'cjw}Xxp-nOo|ua#=HiLD=sp+S=TiN1ss6d>H<uONxu`jpRol5}I~Q%|QtxxA@VV6VT&j33bvu_zor|_}S<#(`D)Uff9;(bkm3gQ#'
    '4^`%&$~;t=hbr?>Wge=`LzQ``GLMRzN5#!Um3gQ#4^`%&$~;t=hbr?}FP{g`dGM^JN2z8NwVGAbYI>AvdX#E<lxq5rYWk3B`jBe+'
    'kZO9&YPynYx{GS&W7W*Zs_8DO=_jh`C#so`RWl!}W~H>6*;zHSvub8%)vT0OGgqr-u2#)lt(qRCnjWQ^9;KQdrJ5e4njWPFZEMiB'
    '25oE5wgzo$(6)vZ@*29)8oJRMTu_4xYH&dfE~r8G8g#Eg_ZoDsLH8Qg(rf53Yw$!3o~U8<yatEV;E);|QiDTka7Yafslg#NIHU%L'
    ')ZmaB98!ZrYH&ym4ynN*H8|u#l)ez9FU&nH9!7CBFJx8aLROnDq>3+OUHC#~6Bn{Vej#)F3(@F8di@KF!p|_Ka!7<Zq`ycRW*huv'
    'jLU`OKA&volkI%6olmy&$#y>Z&1beWpKRxo?R@f^kFV!5Tbj>oX@2ykrr<9N=EG$^GotxWnjcaMzI9p<{&#U^^I<k0XU&J;d<ZUp'
    '-~tFPfZzfME`Z<ys(%6QSpeMy5L`g+3&?f>`7I#71!S~<j24p7LNZ!NMhnSkA>-LX@>@uL3(069epyI<3-QE4Jh2c@EM%-(h(i`a'
    'X(0|-2(yJaWFZ6>LU17tSqRUC@LUAXMetk%&qeTD1i?iRT!cdw!E+JWE@FgU6nzUcpj)sg`W9#~(guGS8<Q6??k<AFB1kME_eJEs'
    'nA{hW`(komOzw;E(qc#~hQwlWUyNTCb8TGAwQ(_iS&Uy6M{mvz{<~BZ=ed~c-(u)4j=sAZIJsaktQW(2F;~OIkY5b>#W->?IxI$q'
    '#W->?sw_s8TDqWGR^e({g{wusTJ)<$zgqOGMU`4Ayp{^DW&Ny{D?%-5)>8eoRDUh{)uLD}^<GQ8*Rn=d3+q}~*TT9M*0r#%rSqtT'
    'd>!QLAYTXhI{ME#bf`mzI&`Q*hdS!0j>@T{$E-uKIuxrzu{sp1L!&x0szakXDy|O2>QJl>#p+P34#nzFtPaKMP^=Ec>QJl>#p+P3'
    '9>wZWtRBVcQLG-t>QSs7#p;<c)H7qKN6mWFtVhjy)T~Fpdi1MDzk2kmN56XXt4F_j^s8q!QIDGSs9BGi^{82on)RqzkDB$US&y3a'
    's9BGi4XkT4u&&V%QzaKAb5VAcqapWZs92QDM!D6=hTOZLVo@@RVyhz!e7CxRwUP!_E*o<1f{I1SOcY=1YGAFafpyFV)-fAcacN+U'
    'rGZtI2G+J4_|kYRN<>lg-SJqI$VAz%kjJ7#I?An|HLz0Jz-n3p>!uB?tu?TU+Q8ac1FNVFtOYeh9t?^s*${a!D5P{0zM(6yYXd8+'
    '4Xm&>u)^BFnrb5+Y{Y|&c(4%<HsZlXJlKc_8}VQx9&E&ejd-vT4>sb#Mm*Sv2OIHVBP)B2tn4-7!A3mThzA?-U?U!E#Al5-s}V0X'
    ';+{tQ(uhME@kAq@Xv7nZc%l(cG~$UyJkf|J8u3IEYq(LAAWG(<?22v_C5V#QD7U^FMG2y06vZ6bgd>}9WD|~T!jVllvI$2v;j<=u'
    ')`ZWR7{Qtt!J2SL6YIiF_@#+;;U?VE#F*8@DAmNc)Wk^C#MslsXw$^_(u8}OSY2L%(o6n7SN9!gMRC3l{NBCih6`7XiAn6SBrzt&'
    '7W1_tA_7Uof<Qz>#KhjQ_udgKRH>KVdv8`ObWnP+mn6TaX=?2Lc6QJ1*$?thp3L5J_I;k`oq1<=b`DDSLg`*8-3z6Ap>!{l?uF95'
    'P`VdN_d@AjDBTOCd!ckMl<tMny->OrO7}wPUi1^a=qGxibT5?dh0?uHx))0KV$Hu7s`NsY-c)(LSr_ijx^Qo*yxvrKy{YngQ|0xh'
    'lIu++*PBYNH<es(>hj)HYrUD@_GW(Dn`*5$)mm@nx4o&>dNaT6&HT1E>$|;~?e=E2+nd>LZ)Ur_neFyw?YB2`-`>=Ny{QL#QxEp0'
    '9_&p$*qeH=H}zm2bnk=iebBuRy7xi%KIq;D-TUx#pbxcvA8P$RIHV5_>4QW1;E+Ceq7R<vgD3jni9UFu51#15vw}WU_kHk7AD#~M'
    '!99I&PaoXV2lw>BJ$-ObAKcRi_w>O%eQ-}7+|vj5^uaxSa8DoH(+BtT!99IBXSQ#pXO9`}Tj{;yzf4hbdTjiueK~`+FQ?A-<(%2R'
    'oGjayvt;{ndTd|LcJ0e)u6;SbwJ#?a_vQTEzMS9Mmvf%`mfxv}KQoTLFDJJ4<&4&V!nJ|Gs+xYV)DM>W!BRh1>IX~xV5uK0^@F8;'
    'u+$Hh`f;jmKhDwZ$H}?<;Ikim_JhxUoQK;FcKg9+KN#%CdAR-Hvmbo+gU|l(*&jap!)Jf^>|d!8qM9-)vlLJ^YRBK0qJ)>2wEl3`'
    'AI|#2S${a|4@>=FsXr|BhnN2F5~HNs2%S__6i`U`gr#t0ftRO>yhKkGd8vM?$V(ZOc}Y;tOBrSEd8)`u)l)@YVpNE>22}f0rJ70p'
    'E}$lLwYBBHOP`3<h5(<+p7_;<ke<p;R}H@`Sw<oDP*-Ls3cr9Eqnxw&3!f^VZ4i31s_FqaWB?8sfI|l0kO4Sk01g>Id;^GY0PzhV'
    'z5&EHfcORw-vHtpfF}kNqm5C~1p{!wfbEz_-;4_HHdjRh%5Ohahk~<aAbuH$Uk2irfjDF!o*0M=K(zy5X&}4|EU&`V)COY@ET5AR'
    'B`ghumx1sy5Zwn7?I3g?gzkgTeGp0y;;sjA*Mqq0LEQBq?s^b+J&3y=gqnj;bI^7%6crnUVuMj^Fp3REvB4-d7{vyo7^rqIu@5Hp'
    '!Nfke9D5j?s&kYwF&HKWmw!_tt(OLue^Vl<9HYVI-;_vyk7zL34lbW%QXLAb>cOxy1f_?d^bnLDg3?2Xb_mf9A=)8CJA`P55bY46'
    '9fHzBP<jXv4cRWD^!>)L2eCRDf(wS=f}zAdl-P$>=F=I<nHXA`LFXvz`7#t`s8D$f<u?L`QilxXHv)!Il?>%K0)|qf4COZhhElN%'
    '<u?L`Qoju4Hv)#D=1|V_A4<hCl(BdyXZ8=J0vt-kGPJT2DE@zjqU}&l@E=P3GL#eihf>W9P5SGkE&0r1@7;j54QShdwhd_8fVK^2'
    '+kmzWXxo6c4QShdwhd_8fVK^2+kmzWXxo6c4QShdwhdHW4gCH?12tF!zyHucMb^OYKQ!Q%2K>^1UmE!RhX&l!Kqc3Jml|+S1MX?S'
    'Jq`ReL<2Qn1I}u|Sq(U=0cSPftOlGl3}+3)S;KJFFq}0EXAQ$y!*JFxdfH)?Rk$2wwN!?p3>9kcVU-oL9A%YwhN2u*95M`t48tMA'
    'aL6zmG7N_d!y&_P!7yAf3>OST>0u~645f#m^suD5PugNNhf(VfORBuG3u=Z@^9@7kVJJPEDq%QP!f>jD;miYuQ!@-_9x$8=VmR}F'
    ';nWkL+To0_!>N;pGu{rTP9C1UM-*;4M`_hOobh&eaj$0Wa4Lx5**iaB*|d5%<LwCYVFdXwf_xZ3K8zqAMvxC9$cGW+!wB+W1o<$6'
    'd>8?PBVcd@432=o5imFc21mf)2pAlJcSo@Ibp%cxK{Yc1e~!SPBk<=4{5b+uMr@}_{w_vb1&yEz8c}%{Be}C;O*9hEkHqsM@%%_U'
    'KN8Q6#PcKZ{75`M63>HbN21tB6dQ?RBeQ)8NmV%#{YIkSNE921=SSlCk=g!&q{bWx*CXM26d5pz3>ZZQj3NU@kpZK~fKg<?C^BFa'
    '88C_r7)1t*g3nR#ISM{U!RILW90i}F;Bypwjv@m_kpZK~fKg<?C^BFa88C_r7)1t*LZeY=G-^AI@+YWqK8zweMv)z($c|BD$7r%+'
    'G}$ql>=;cxj3xs{<9Sf+Xfzs~?Y;?*4sw)gG#ZUYqsnMh8I8+F<MPqjo|>?*Up*Q=N5ki6_#A`h$Kd%fczz6?AA{$|;OjB?dJMdb'
    'ftNAxG6r78z{?nT83Qk4aO)V{ItI6n!L4K9Yz&-@fwM8&ah5;RuZ^NHIC2b*9D^gr;K(sJax9J<izCNYo&skm_vhHkbKe|geR+mT'
    'IjT5$Y~?9%j<S9}L!}HAJU_Pb#5PCS7?7b-85OewR67<Ij4k(IrKGAHOMf;N7mURPV{yS)vSTdSF*bSb8zKsw&sdZmi_&9JdK}p?'
    'j_epmc8o)#apcN4a%CKfjbpSJ$7nGQ{l<}F<H)gbs5y?2WE>;OIJ6yyn&Z%K9Ey!Yv2iFi4#mcy*f<m$hhpQ%+i~RWIP!KJc{`3#'
    'W*no;I7XRqj56bJ!8lwn4i}8u&IQE`A4i6dBg4m$;p52g@nraTGJHJl8Bd0f$1mf_;_>J{o=hE&w&Tf0Q0@52zKfW`@hCkWrN`4>'
    'k4Ne8C_Nsf$CI1m$<6VVJsGi_<I!k5J@j}K8;@e+QEUQvJAu5NK;BM(`3dCh1oCzQI!quNCy<R3P-Ox-On~_bFh2q2C&2s!n4bXi'
    '6JUM<%ugW4CXizj$gv6J*aTFWfGQJEWdf>9K$QvGsZty_Cy-SW$f^ls)daF?0$DY&qIBH(Ok^+BMD|NfWKYyYb|p=$s1ipwv9b<U'
    'N>N?@E6)?ze>Ra5Vkh#;FcUc&bRwsLPUMWwiM*FQkyAY<a+>Qz-VdM1X|5A_KYSwRw@&1Y&q;7L3C<?5<7^TPPGXPQB>0@fuCht6'
    'JBeLhli+$1Tu*}QN$mWa1oM+%eiFOGCc*q9_KHnHhe_-en}jNpP-POTOk%I!Bs7|YMw8HJ5*kfHqe<*Pn}lMMQEW1bO-8ZFC^i|z'
    'CZpJ76q}4<lTmCkicLnb$tX6N9ek77!8aL=CZo}0G@6V?lhJ508cjx{$!Ij0y?&EncQWiwf!!&vI|X*9!0r^-odUa4V0Q}aPJ!Ji'
    'usa2Ir;q_t$bc#EIRyr%z}Xa7n!+B|DePgLg0H9G<SBS}3Vcq5!KpAf6$Yom;8Yl#3WHN&a4HN=g~6#XI28t`;>f8uaw-f?g~6#X'
    'I28t`;;gAKF^wv38dcsj>bhxEa?_~YrctedYNt^pOk>VGt^ABOY`m?`QToJo8c%GeQ6)^{iS#s{NKfO5^fYR>Y2~+d!p7U`>S;X9'
    'oyOQdor-Ka71?yEuIW@((}{gLu}>%V>BK&r*ryZwbYh=Q6*QeHXgcvtC%)<1#h301jIWIAm+3sao=!D0o%&@4ewl$^X5g0@_+<uu'
    'nSozGwKL#s26f~N7@PrvGvI6noXx;5Gw{m{{4xW-%%F0d0lPC`cLwav#62@{&rIAi6Zg!7iJ34l6DDTD#7vl&2@^A6VkYjHiF;-e'
    '?M$MbNwhP!i?&!N&%{|Xan?+nH4|se!dbI$)+}Z{v+&t0<~g%)-7ID{v+&?7<~g%)B&c>4vz}R~G7D8^p~Eb6n1v3raO5l;ISWV5'
    '!jZF>=gdN}StvFO#b%+{Z2UPJf6j*M*|>E!T+hb4v*CI+?9PVI+3-0VK4-({Z1|iFpR?g}Hol&XuV=&AY&e?@XS3mK_I8{VT|OI^'
    '&&K7martaqK8MO<4wc6oYK=Km7jt;;We(NF9O|q&%rxdO$D2bHJBPY;4wdR0-b0x~Ju!#6bq=$MIn-ctm`%*#9iutaXLFca%%R?$'
    '3uklTY%bN>To{~7wKf+%=TfcBh26QZJD1vRE*0)vn4b&tbE($m!u(unx4Gyrmr8Cfs?0@|xu`N1RpwF|&qbrTXfzj%=AzMDG@6S>'
    'bEzZeqS!nXn}=faP;4HG%|o$yC^iqp=Aqa;6q|=)^QfrjQBluBqj_jF4~^!b(L6Moheq?zXdW8PL!)`r<@4Zk9(>M+&-w5<A3o>9'
    '=Y05_51;elb3S~|htK)&IiC!ePX^3~&-pMoAI|2((tKE&&x~(AGrsxwdOl8`k9X(e-TAP)06rJM=K}a#0G|usa{+uVfX@Z+xd1*F'
    'z~=(|xd4AIfX@Z+xd1*Fz~=(^T!7COz{EnBSO^mfdAD;Ryex#5g}mFj5SA9g(n8+tTnJ|i;cOwCE#y7Sg)q1fM=r#X3t?~}3@(Jh'
    'g)q2~cWf8(j_pF;v0aE;7vk21xOE}^T!;>f&|wieEJBAx=&%SK7NNr;bXbHAi_l>aIxIqmMd+{y9TuU(BAmPkCoe*WMd+{y9TuU('
    'BD}i@&Yq6%x-NZhuqr{xn~>qjWL0gB!ehhI)8$i7!kg;VHBXmMJ*i3_RHmp&qpDESCZ7^I^LPqUO4~y9Ru$gziQCdk!{|^`6{B#t'
    'Nb-HvqEd#c!^`+p&v2j5aG%d`pU;%v-%Rc-L7@Vz3U46PJj0zm!<{|Dojt>yflAMCXU}pk&vGx%!r8NM_AK}EEZ_bt-wrB0%eOzr'
    'w?D_XKL-=f!NhZX`*VEzb9_6f^c>&*Jm3C2-~K$`{yg9QJm2>`-v^37rRVwf7x2Uj+{+8x%M0l60y?~acVB>)7jVc6<-1N^39SN^'
    'ULc|uhzJy4nZBu;mO3w#&)Nye7}dN`K5Hj*OHq`fc>E2iTKz)#z1`~C@N#a7;<m64w|X&5EQX22FtHd_7Ng2yVqZ+`i-{dnT1@PV'
    'i5(PQS&V&g`7Pxn+5{!f5yS4xn#DxBm}p-lz88t_MU;LKrC%hz7l{Z|dXb1;BqC6JWig@`QS(LAe36J=B8HcU;UzSB35{MNhL?x|'
    'RC<XRULpoid}T3)mr&&;RC$RQUM7Z@iQ#2pc$pYp=B_~zsPr;1yi5$B2o(QaF`}1==w%{$CA;fnoX$~l62L2&my#;smCQ@YIbW~v'
    'p8hM96@oIVoYwG4`FHNZh@POr*><n+%h(x8M)Vk!V@Ou8Udi6mPtF>6rM&W$&VgPj%!sOLU*XrUU*Q+ymJsa{qFq9?ONe$!=DOtE'
    'gC)eigxHr5`x1WRZwX8+A@(IiyM$<$5bYA8T|%@=h;}K_E+yKfM7xw|mlEyL@@Wle?Y5NIm-73DOJQOuu`easr9``wXqOW0Qchi1'
    'TAp2}D^W{fVkt~4g^6V_u?!}bWtp11{IM*{)MN#68B8oA_GLu74BeLz`!aN2M(oRoeHpPYBfe$)D&sPKYjGLTE+^XMM7x}5mlN%B'
    'qFr7-vm-t0YB?@g4in39!E$(64in3XeL1l&C-&u>y|KLfo7VAXrl{bF<#=K_oGs^9E|<gLau{3=gDYTg1q`m>w3HR((F#sRTtQZ?'
    ';GD!2Ft`Hutl(_I74(=Z$fFhTxdJ{{z~>5hS;2{eE6AJ`ob|B+URJ`(N_bfbFDv0?CA_SJmzD6c5)ZEAyqT47wvzK-R>I&)T(=TF'
    'SHj>*7+eX1D`9XY46cO1l`yyx23Nx1Di~Y^gR5Y06%4L|!BsH03I<of;3^ngMHa8(9G+F2!?OymSCQeXV15-`uY&7UaJ>qySHblv'
    'xL!quuY&niFuw}sSHb)$m|qR^t6_dM%&(@8T+Mk%tLZUUb2`#$m|qR^tKoAs46eqztKoAsoUMkl)o`{NmR57l&}w?V)tnc!ntpIK'
    '46cU3H88ja2G_vg8W>yygKJ=L4GgY<!8I_rhVf_(CrYis*K6?g8hpJ59oFFMHK?)%9oC@38gy8L4r>^>*5KqdXtah?qt-B1twFyv'
    '=(h&_)}Y@S^jm{|uQm$nkB#eVlLKc`RNuI^y0)r}V%BQI)75|)H;FZ?N+#4fN@kHMs&ACcW#TKtN@e5vQuxfO6xBB_h0jb;{F#C2'
    '+JNFaX<VP|^Dm?N#(~>1iYZKHt)eJH)yXNoF=`TeyTDkfjOrVQ+bpB_`$CnKd|#8g<okkqQWU-~%%l>Od}in|UxSy|;N>-Vc`aE-'
    '3`_(iQWTg79(fJUUW2pO;OsRxdkxNBgR|G*1r&c~k%`w};x(9f4JKZLiPy?ZR0X?;qSs()ZCGPz5?BfgMJWm_g%y{zFt`>5*TUdh'
    'SXv89Yhh_^nEN&fEQPyHQD7<D^;#HQ3xjK6aBY|uH%VEF$|z+iMHNS`#gS`a9u%#`k?V+d9nr2M+I2*`j%e2r!#ZMESH92W=x9;2'
    'u6)<YLDE&Aye*Ar9T9=Tl?C^#!#(Tp%erLWd)%Xy(r*u_zEO2;_`>xtu^uMYlR4|job|A@9+uX_(t2204@>J|2^6h|B~aRy^8yNO'
    '1zy&}%ldLwC7rS;T3_ZYUEu-cZ7HAY$v;qhW!Pg9xK2MapulwqX+1iuM~4k$;|5gOfGQhcegn*JfcXt%+y->mfDRkb0TgW@<2K;W'
    '4d?(0e^==1HlWG|RM|jZw*js<z}W^k+X!bH;cO$EZN$kNaq>p^+z6i=;d3K=ZiLT`@VOB_LD5Dy1BJE%XB**cBb;r-$)IQ>d~Sr#'
    'jd&Ln|6S3$8}aT&bl8Xvn;2I%p~EJ0*aX*`;Cd5WZ({7&1lOD3dK2TrCYT3Bo9IzMd0Xo1O=tv)uPidL2_`l(-fo7M&A4?lENzCR'
    '&9Jl?mNvuEX2#piaJCt@Zid0lFu0lVb~Ai#hEGtmnVw-Y3~q)&Q2cjA1~<dt7MR#V-fkgpx4_aCSlR+hF=`SXActrAwV^Hkj2MNr'
    'uDGqp#1^6jMO$zWC~eE51%<XGr$aSgQw1uw#hisl3{{}CE!=go4H1;LrG3E``T|h2g;5QZw&i^RC~hnE1zYF~wxHjZ?eq)t{6_WR'
    'T$~U?K=qBH@WMm&Ry@BIrMIH=R+Qd~(pyn_D@t!g>8&Wel?>R5?px6v6m3O!P}-L34hn4r-9hEHOm|S;miGEvQF<#%gQBe{4NBW`'
    'r9p99QR%HHy%nXmqV!gj-ip%O=<Bwj`!;mnhVI+YeH*%OL-%dyz75^Cq5C%a!ELx;8!p&}3qa8}lm>;ig3_S8EgjLfq3t%b-G;WH'
    '<Wnm8f#SBJe%sJ*8~SZSzisHZ4gFq6qu0^sbu@Y%jb2Bi*U{*8G<qG4UN37Dwr1B<fuh&Tiq#}z94KuI3?`ewL3vxM?dxa@ie4wf'
    'L1|mAJ1DdjbO)8&vJ3~MZF$cQO4=$e0F~Ra3<srcxkEs4ThSq}<B->J$m=-dbsX~gb`A+ExQ*&-N~LmJ97Lm<u*ev<g_c-{QYle7'
    'w8SW^-c`RrU+@M#djp@nfzRH+XK&!MH}KgT`0NdQ_69x!MQ`9UP~MjI8gJmNH*gjxdIM*H(ze`LpwL!u7O32oISZ7uRonwAw`J}D'
    'rER%;Kyh2qJ#XNiH*n7zxaSSr^9JsD1NXdvd)~l3Z{VIc8CTxKOK;+(H}TS&c<D{N^d??<6ED4qm)^unZ{j6T^d@7@o4Dsq-18>x'
    '0Yz`(5Kw3<I0TfmRa^i{+j6Braa&R8H&OaclztPX-$dy*QTk1keiNnNMCmtC`Yq;8Z=v*CDE$^{zJ;1^q2^o6kKRI+w@~G+@{A}s'
    'xkVJcRh}OuC%06A^0svD^cLEJqPOT7Kxtd9J1A}|>hKmiyp^12k?N4Ng`OeNp}P8QW~Oh$?%QP5+i?9hT)z$1Z^QN5aQ!wj)3;&%'
    'ZL;HSba)#b-bM#d^ft5Bw_*Nmm<J_)S78?vw-woa8+PA@-M3-)9awq?mfnG-cVOwAGD}JNRe_>+%A6%PRs~AhDt!;A+?I`FptLQo'
    'mq2-2%KSSp4~pI)13*bzg?Ui9E%Q7mZOc^w#cf4Z-a(aj=wIHUe|ZPR-q}vE@P=RbyOisI!rz4(eTRPO9r~qr$((n|m3MK$ySU(8'
    'T<|U~co!FdqIYotC~r%%>Rs~aUDSLRH9^t4s0m8iDr$ntZJC;&v@KT?6t@-Cd>1v}MX`5L>|GRl7scK~hxgFoJ#=^v9o|ES_s{_p'
    'y@w8<q^**TpmJN5ji9_ORqQ<!dk@7x(R(NcO4=%lfy!-}VxY7wR}2)l6%~6A#oi<T-Xs6sL(TV4^F7pjZ#y-M`S%|A_des;`()$$'
    'jAQTPiTClu`*`AgJn=rBcpp!IqW2l&-X|O1XN-FvrQb*C_fZ-YzM-HdC~eCX1I2Ac#okA;_fh42RCym&-ba-WVD|&q{Q!19fZY#Z'
    '_XF7d0Cqvq2V@l}Z%f(z0Cqos-49?F6h5WEE+}ow*#*UIMRq@c-4Doz56FiPVEzM`{{ZGc*pB&PK72qv{59;;i6g2?Ua|jcvg52t'
    'eQiQ-K;g{ts_H;Yf*LmpC|2dKfwH76P?(^kEm%26$x)0ciWN)VqW^13b))1Y%>;#QJIR4IF-lASC}BQ9@vT-Rs~iQCd}fNOla;T('
    'CT}1#sV^lj2>dlU6QN0cP4W`QUz0NtlFv*&C3!hE{9TOxmb?*{L>piEH<<VvvHy+O|3>V8Blf=$``;R+6US2W?SE^OPKm-?Fh%8P'
    'V}Jgw7@sKmTP51~%D-oKo#fHqv%3x(Z)^Xa-E}xYp!E0bu9H0adv@31tbx+sv-?bjk{l(o-M?pwC9~bXXE7wX^7kx;D8%shEQau7'
    'Hz{h8%?&|OhSGf{|1Z0<@MFBu|I6>JHmWYAsJ?Mk{C#DV+-Ge~bxn@K7O?d1>Kiq#s*bO${eOv<ViZnth*7#KRw@NKGgKSCAVwjH'
    'lX+_VG5;?~+mKaJ88uGwD5@=^M%DGDfU5sro=5R_#BEI)rQZ;~@gGF=4<h;p5&eUR{y{|lAfkT|(Lc(4NNsKUDe25RjW0uKeE%T6'
    'e-Ph4i0>c7_m4QD^fS|lnj~A?!uM6xen@;D62phY@L}ejC~VIDkcd9avcEdq=!eAjVb&Lf-{FYciu!$sejgIwhs5_G@qI{qAEMuf'
    '==TxveMEd85#L9|_Yv`ZM0_6+-$%sv5&C_EejgFvN5uCL@qI*mAEDnz=oe79GDh*Ye@tKZF}?oB^n4%F^L<Ru_c1-+$Mk$3)9Zgs'
    'um3T<{>SA$Bt4L&fRaxsjtCz!B796A`7vX_$BY3VGX{K|EOj*sJyG&^$--Bo>g0#AKTa1z8&wCP6O_C+oQ%HzWVHAv4E__&{t0LQ'
    'gtLFb*+1dzpNtm&WVHBakrz?)Pezh|GLnGeD~qxJi;?7Cj3obJB>5L3$-fv${>4c0FGiAoF_Qd?k>p>DB>&1H3Ob0Qe=*AZi%|v?'
    'Us;Z?RLW7Ptb(@xM!$cf-@noC-{|*m^!qpZ{Tu!Mjeh?w$Cv!7v?%&F+Ws4DLCKXBH9>J(QO$oR%e0NcuAR8?KWO_OwEYj-{s(RU'
    'gSP)c+y9{Lf6(?nX#1Zm+L{nMDEbe&{|DVc$(0qQL2+AA>Hnbge=;UY>Gvhe*KwU3_IUp{i?0;6fB(1A&&LV>-%39p_xk^>^z-qh'
    '|E=`wwJ9q1<+b56)5<^GbWPQN%j@OIp6(o#!tjuyq)!gE`)|4Tjz2N(z5g3x2)oEb2&Mn#@zo^v(xg%PDPf%XZ@HhZtquMBf5R8V'
    'e-}(pRr+rpdrW-zyJXXPLT>GU^D&?%x$AsHh|wqT@(H|r0xzGy%O~*i3A}s)FBvK&W85csH51=-Kn0dQfu&F2<r8@M1YSOYmrvm3'
    '6L|RqUOs`BPvGTKc=;4wK82T0;pJ0!`4nD0g_lpuOe7x?P{BQ)=2b%A>{EF86!&}zOP|8hr||MAynG5TpTf(h<q9I)S&AwweF{sT'
    '!O~~2^cgID21}p8(r2*r87zGUOP}GM&*0@VnD`7PK7)zRVB#~F_zWgKgNe^z;xm}|AEV6w7-jy)DDyu?ng21${Et!Qe~dE!EBCZD'
    '$q$f$^0ssY`X3_@C|p?>b3kcZKIVYpw&IxcKgOK@B{DP$PgLT2`J55xb4H-g8G$}$1p1s2=yOJ(&l!O}X9W5@V<K7a0Y#rPI(^RQ'
    '1PWIc#v@SLmXAlExUD!Iea?9FIpfjij7OhmoR!l1OpIJ!@A-mR<QL2$zhH*)1v8W{n3H_LEaVI3RbMc#`huCp7tA!iV5ac}GpR2s'
    'IhK5TabERBC97g8zR05uD^p*TGp7_#^_N8ZCDDFKv|keKmqhy|(SDit6QS4mk{R@u%)q{62KFUPd<hd@!o-)v{v|W8FNyujd_Go_'
    '+*xsU_9eW02`^v4%UAI76})@}FJHmSSMc&x-kXO0^D9{T3YNZtrLTzgE2901Xul%buZZ?5qWy|!zh><Cnz7?+#*VKUJHBS@_?pq;'
    'Yevzp87;nM6#bgf;%i2WuNfb{W<>b95>b@4l_QGj{hHC@YetK2(C-`c`-XLfZ&33a))~G*+izHB_=bG{hJ619mw$uHzrp3-kni8%'
    'f^W$8Z*ajkDE$pee@pD&68pEr{w=Y8OYGkg`?tjYEx!I1Cx1)6e+v`e!o;^Q@h!1`O9p&P?B9|B-;x2}!ppbY@sj%`iJ`b|^Bvjo'
    '9og|6+3_9O@g3Rm9og|6wbXZH$9LqzcjUu&<imI5!*}GvcjUu&<imI5LsebT6FEvek)q5K3CcZ@qRbNkRXmZR%oA00#hx!isY7B^'
    'a7a~MQRx^Jl#WqB>3}LqS5R#kRg_Lpu5^Y{r7I}hXLVirWHLS7Dnqq7N}d8I&(1PbTS3X5;81~Ps5V388Z6YbDGDP=xa)w@iY!XM'
    'J#6HP+oI|+N^7uK=^TY4|DqJtmru-!KQVcRnZ7F&P`I-wd9IeAuoo^_%ZpL+B&{lWu9l+oUMeU(@vOQo?R#pIzNfk_eR`F8Fse(R'
    '<|f5qj%o`iV=#ijs4jgLnUt70sx6?5-3WFg*o|N}g53x{BN&WeFoMCTE`5fXzIzqHXH=J_c$8GJ5$r~=8^Lads*{~g5$r~=8^LZ('
    'U2!gxp!f@GlSAWb>WVX)n!4i5rlzhqv&m8VV{diE8A^iU&n$({45+XwmY}$;CVA==P*|IdQVQ$R2b@*u51tiKl%eXB`nuvQq?E;w'
    'IHXipoRgI5igS`uU2#s5qvRQMDOW5xc&n~Bw<u*1CHj@>ifdh^ETZHYSSgDrIW?n{#gIHN21OZ4-#xB{`G6{G_qFIyiw?EuP@Bb&'
    '{L)o|lJ)uU47#?iINz+TE3V|%))iOsYwL<D`L%V$)%pbGtMvtxd}i_aZ7urM))iOsV^mnl52&(|pP>9{?)Px(_h9LJ@bW!)`5wG{'
    '4}X3SM}DuaxX%8)y5dvW@8L*L^gSHei2H2BeKz7g8*!hFxX(st)QG!o#9cSyt{W9~5JioMs1Xr?qB^pwjy$R(kLt*yI`XKFJgOs)'
    '>d2hBy5bXny1L@C<T^436xESAjk)W_+;wB_x-oa%n7eMwT{o^Pu1GYlE3Qa1CZfhf)R>4G*A-V5Kv83&ZA`SFs0pJ}6Go>dj807$'
    '`<pOUHDT;;!pPNxk*f(KSCjI{mF^mEQXaX|w*{J%N3QB*ZKg?i<VqH|QWW23`uwj6<5&~Mu_jarP3p3zq+uUTit5X!Wj0|{Yr?2j'
    'PhC(?T~N>1U(eWI54-iSTMxVSuv-ti^{`tHyY;YJ54-iSTMxVSR0;Le1@-V*51;k$Sr4D}@L3O^_3*g^ob3Q-JHXivaJB=S?Eq&x'
    'z}XIPwga5)0B1YE*$!~F1Dx%EBX_`&JHX%$Ft`H@?f`>3z~BxrxC0FC0E0VH#qLNIyCZJh5x4G06}ux<?2f3iBdY9(Dm$Xej;OLD'
    'I_wDZJHq^qFux<r??_F%BW~T1ns!H+-x20_g!vuedPlh45w3TH>z&|iCpg;)&US*co#1RIINJ%%c7n5=;A|&2+X>Egg0r3Q=T5M+'
    '6D;inOFO~RPO!8SEbRnKJHgWTsZqX9<^O#umhV%se4mQt`&2C7r$+fcmH+ptSiVo?|NU~E9Ddw55=Gx<R`7i)7EpX;nTb$tM>|sq'
    '?98lSXX=8TsS9?dF4&p6U}x%rof-RgW>&B>mB7x-3U<!o3$H?nqMeyB>`Wy9im%LcPya5{Jx0|(K-(Xn?GMoQ2Wa~PwEY3v{s3)%'
    'fVMwC+aHvpjgtBk6#W3*e}L|w<jRWDpt!B5bd1uKy`)b5A+i6EXn#nwKP1{8673I(_J?)Fr);3;hs6FvVh1HxR-y%^ZF#hyxUCrN'
    '54Vf9_;hX;JiiN`-v!U_g6DU^^Sj{rUGV%aczzc=zYCt<C5t_&cR|rE<ijrH11Pz&k^!K&t(XD3kO8}7ES1vlOCB?aebjN=k6`IX'
    '@bV*g`4PPQ2wr{!FF%5pAJr9~K7yhj!P1Xl36xw};RTeo<-CC6wjwV-f|nn`%a69>rT7dpMcFgVACpx-rbqcPIrd|6?8oHTkIAtg'
    'lVd+Fdnvr59EqYI)7$)*90P?b3poZ#+wvR(#cjnL`!P8dQ2NX}+{;g3;wQxZ6Jq}fvHyhFe^OU`!Vk*ZQeJ)nFQ9N`p<e=}Z8=Mz'
    'q^-gdC~eDG0>y1bmVN?DKiQ6@V!!m0y5g>ZU8$^grLx+UIl`{gS-Ubv*p;elSE{aEsk(NpE51Pjigv9lzOw~N+A43CfXZ#zJ6oW%'
    'Eq{X&l((gCp6p8Pwkx&Uu6d?brETR*ttz*rPaML6Zi>Q=g0OhLYhCf}k`!gT4PsPygCs@S8zj5d6`%iAP^pa4_erV}#fop2?8ba$'
    'H!AAgP<l6%-VLR9L+Ra6dN-8b4W)NO>D^Eo6zzu6pu8=8FKf5D;=4k-q1bLHwi}A=hGM&+*lsAc8;b3QD!ZY|Zm6;wI_wVDyTkSF'
    'aJ@TR?+(|y!}acPy*pg*4%fTGH7MF0u0cs#C96Q?wk)ead0VQ=?x?ams_c#`yQ9kPsIoh%?2anClSjLgN4ulg?kKi9itSDw?Y^CU'
    '#XQ=BHGw_Isy&#)?t$)mp!*)^z6VP0fwp^~?H*{m2ik(745c;S9%RlQb;Wn?_CT>cP;3tr+XKb+K(RegY!4LM1I6}0l|4{p4^-I$'
    '9rlFXJz;lG*xeI$_k`U&VRuj1-4k~Agk4ayC)okY+fsJ-gxx)1cTd>e6L$B6-92G<PuSfPcK0M7_9P$ng!w&TeovU+lYH27I~|Jo'
    'uoqSOUd(0oqGsQVntd;7_Pwat_o8Osi<*6}tg=c}0Y!T;&)JKb9TcuC)a;<NEw9-@aa*xw-;0`kFKYI^sM+_*6-)0kQ!FsQHw^9#'
    'XM4lh-f*@zob3%~d)F0rV1lB(;d5{J1cfUL^CM8&ma_{=+A8dV(zcvkP~28zcW>C;8+P}G-MwLV@9o$v&X)FOwzPL$amQzhvRwIT'
    '&V1PZ{nLE(jk}2yB|3x+(K$+Xpd={S4HI8k`_sDOj=>aVI|hHs4x68{i{_{7oB3&7apzcu(*06Dtt-Bv_S3rJ?x~;F6?ac1DBnHx'
    'Q}R7Vg`H#j5c@vFz7MhQL+twy`#!|J53%n<?E4V=KE%FHU2zZOKI{w1P|8FFrT1CnWgmFi2VVApmwnh>v=2Lo_9gaxiGANJ|H5wU'
    '(!MaUZ}v<-bn~ID5c|IDrP>!J_GK^CzVNayd#U!tA^YNxePLo>nAjI4_JxUkamc<nWIveL4<`15iTz+=KbY7LCia7g{a|80nAi^{'
    '_JfK2aL9f*WIveL4<`15iTz+=KRmG?p4gAQV*9hsus=IO_Gi^$e^wp#XVqbUc7*KDj*$J?ZLmK(LiT4z$o}jI*}ty%Zf5}{pHkc{'
    'vOl{;_Ge$h{;V_X&;F48*&nh$`$P7xE556cqU=r21m$mf22^>|^JlE${0w$~2A@BJ&!55P&*1E5tlRvIb>W{Cc@afFWB10-*u4Qt'
    'uB@!hfa10y6F+C{|2bp-&l&rF&e;ER#{Qo(_WzuH5I<)h#LpS~f6f}`&+CfsTY#dUvq$3R?2!N^S60S%P~290GvnuV#Wyp4fzrP~'
    '>0hAqFHrgyDE$kR{sl_^f>k(B^b1_@3tRw7uB_+|O4=&AgW|TL?!RE&?EqYG04_KH7aV{K4!{Km;DQ5i!2!7709<eYRURlh0EZla'
    'LqN%u6;FVYwu&b}aa++72jGbVsND{rcKaoM`6Yh&C4TuOe)%PS`6Yh&C9A!lye;+8FYyv6Tv>1rC~eE#14`N|?g7PZMfdy?_xzGo'
    '+XL~^fq3aaymTO5IuI`%h?fq;O9$em1DR=nq66{Sf%ps*t}HkUl(yy00wrw~XMy6jqO%UfSqI{*198@Y%nA-<R`4s<Ab!Of#IIO`'
    'h*5fKX|gPqqlCc}Wef&XIb-QptRDP|)q`KLdhn~d;(635%Fd(yRbBBs>VPW0B9WqO*T=8wil>Nzq70?`-F{89zb4vW6YZ~w_SZ!F'
    'Yoh%%@%@_keoaKbCZb>070*QlMZc~qo{kI3+tS#7P3)lf%Hj#CDauYzJqQ;Z1TP1{%R%sR5WE}&F9*TPLAc-`SUL!n4#EWo!P!A@'
    'b`YF_qJwbAL9lcXEP>*`E3$MDEd2&1eghM~fr;P1#BX5YH+98xdw)|`Jh%5ZF!7tZ;yJpY=r?u6la@hgTYiQ&C~r#{{0$6(qTk>;'
    'P}-I=2#VW^4E|<228*ZhrYJj&_h4LiFkBxD*9XJ(!Ek*rTptYA2gCKjc<^ADKN#jg(ZMhe%G*-69t_t9!!;;67_LESTh28oZYy$q'
    'FkBxD*9XJ(A>{iZFn<Wl9|H4-!2BUFe+bMU0`rH!{2}xOhoHkD=x_)+fTBa_Ck}!6Lty?8m<J`FQehVqw-wnv1a=RB-9upaP#8QE'
    '1`mb7Lt*ex7(5gP4~4-)S*-^}hw>~7l(ywhh(UQ<%KV`)4~h;Y13+n8-uHl#wu%m*a$A-GptLR52o$#!H98cH4n?Cwx6`QjRN+vb'
    'DjdqQf<t*aa2UCA7)l?8(ubk+VJLkVN*{*OhoSUgC=H4ZLupXnmS)vqXnPpif}+FF7L>GA^aGXKGW|elTdp4{ZY%0{82TNCeutso'
    'Vd!@l`W=RThoRr$^n8b-=HaM$IBFh_nunw2;i!2yY95Z7hodGaI-FkdaP&JI{SHSzQ23OBMxeAU*8vo_6?Hfq9S%o_!_nbzbT}Lx'
    '4o8Q>(c!mYwvx_v<FEg1vW!_*KA|K>Q6MHo^>y)m#@zoleS}h%uFU>6*&!dJ+M483@->gxyT7fhZpD25wlXt~8T@VKZKR|vd7u;8'
    'VyO!#`S$cZuypP4w_zTY&Y7d|eT^GsYb-U@0cERcr4*IlcPdpMQJLGvR~|v^M-clF#C`;^A3^L#Bq}tnOIJgWfQch2bNkpKN5IPw'
    '@Nxva904y!z{C+S@jD{=UGPWay7H<+ijupIVS?%#hr5naREhR?MEg6U{T=cBj);CoM86}V-w_cg`W^B8j`)7JU3@u;Bl^FJV%1f('
    '0fnT_Q8}V;YdMO-pqinuZ7o9~zEGrOC{R{LiMHY8!we;-2PG(I8zt|6|6e)Uz(j2osPup3_`)vda$AOyw#weS|6_MMD7~^S{9T+6'
    'RiL;nbdrtBPxu3BlAMPWPpGT^ulTex{=3j=HBNRS1YYvYsR}VPPP)Y$H7eg(@+tAHBz%_tF6lNxC6`>;q)~EZ`1T_Uc~n(<WJQ$}'
    '6;wGARgOf5BVqo?JddiAPs!Ph{~cN3vy94j9glcNRv3)`9a-TlzV=8sOHn*F)`qQ=N5Wu=LR&D*kuaE|`o`hT0xI%ZKv9Y+>=sbk'
    'mT?`0ZzwW<WQF-C`G$fHN1{UkrJtFp5`~D08Xc8{UjCHoqsXJ9$fKjOJ|x^r_`9s1h@(BK(oe(+9z|9iRp~Y2JUWW3I;zrRM(H<H'
    'vg)Wxk6B$oQ5gl|%P~}CD5?t9I*N=tiX1zNJUWWZISR#&LZhQ#_h?u;8kUa6*GJ>)qv7RfTz)jX9F6CXhL@vZ;%J^DfJ#U6P6a4w'
    'tMpQ!q^;5u9ZgRJimxnY&e7z`(eyS)lPgEV_0e#BG@d^immiIHk4_$^rf&-bK9h&5b)j0TN>NZO9QILrbn<HjF{%v@X^){_I);Af'
    '81y>^{f<GgW6<ar`lVwkI>e4Srow#O-yB1qbqu}KG4xW$!0s{hOUJ<VG4xBv!1XcoOUJ<cG4xBvpu;irOUKYJ9fL;4&@UZ>V#m<;'
    '9D{zx()S!oRvk-L9ZTPHEPc<h^gYLtW5?3>97~QJOW$)WId&|4&#`3OvGhI1()S!o{vAuk9ZQZKOCBAID#xP3vAFzLTz)JrKNgoC'
    'SAG%`mS1Y3<H}EB!rp_L>f_4KUcxeaP1SKQe;mvoM?M@!J{(6r97jGJNB;sU9Y+-eO4=%Y&vE4*I?j#cK8tk^DE_-*t{g{p97j)d'
    '9NBRk%pV8y$Kmn>rT3CBSakVuj1R}*@&qM+7j$TfDoxA#uj5*~CPfvEnwED#g$LjXD)d=R>9d-mQByQ(ibhS*s40C`Q~IT*)KX39'
    'rJ7b$iT|)EwNz7dXiA^e6jhqiXEjBYru11&(WohXR#OyfN}tt~KC3BeHm#@`)f7>}e6c@kiqcI{x+!&5Q~J85xS(mp1yM~A#V$A='
    'PaKa6jwe%(CsU6nQ;#q2ehcSPm8y>~KS2!-Y)j$q3Jy6Qha8VXj>jR#lf|IY@nwgEH-}19$CJ~b<jP7;A5Tsnk6(_*A;*)q$K#OW'
    '@x<}C;P~>~KEAVriK6buqxA7;dpz16kABCaSThuBMiw_izh-1{GqSiDS=<c$nw57ihW(}~s_54Y{hFa)GxTdlhBqU_n^p9SFKtG?'
    'HzVJhk?+k=tQi^J4E>ss;mwjmUeef0DazGsM!q*o4uHvac{MAq0@NfcHO<PqywY6}&C06)HA%S5@I*8EiDo#Y8T~}FieHj%D7vQ^'
    'eMmFB)Qmo)8O~}(AJPn;HN$7k=tG*(hcv^3&FDj#;m8wk<Oz821p1H@=tEAR4><u3o<JXR0v<d851xPrPr!pGlwDU7HbGXMK#u|{'
    'oj{Lr0=>ow^cpAN!4q)Z3G^B#;Ik8O$O(Ajg!1}ee4k0|MHifa?kAx1321u)ik+~XM(OF)@h2vqneG;eQ5<b^^lMI!(i}CL)1x$}'
    'M`=!v(i}CL)1x#;&E}}t95tJxW^;O!<`r$LLkz|Kr8)geb9$8K^eD|yvpGFVbF^(vkJ6kTr8!DBr$=c{kJ6kzq&c2wPOs4%hcu_x'
    'XkPJ4@|i{VG^a;tj+dI#qcq1^&FN8^<Fn@UD9v$Qb9#;Dc(6IWMspn597m?8K0E=4`8<(+;zat16LHUpxaUONb0Y3Jk<|)N=|tX3'
    'K9RKxP;zCZ4*?}@m0sgSoOL2zI+1?jMBH;?*r{F4oaD;Nn;`L(MZcVgLrzSLmBf(zT~XT;QS3xCI*~cviOlg%WR7<tbG#O0e+#m|'
    '1sb(LqZVk?0*zXb;VoFnXi?E9&f*rVYqTKyTafQ9(4hqx-U3xxkl`&*r3E?N0*z9X_HF?cHEKalw?MHL<aCRQeo^u%1vOicw=K}N'
    '1-aP*rCX4jEztcWa_l5>>?HI%3H?q&zmw4KBzB6PM8<(iCy{X{kyW7N%1Tz9gqkOz-$`WEN$7VHik(DOorGd1q0vd@=Xg=rSXq4%'
    's+@!lC&Bzl+i{)!;zRl=h5eXSEy<&n<WWm>Xo(Ij(V-<ev?PyOR#d4D-&f44mSj~+@~9<w)Dq@fl1DAkp(T0L5*=ESM=epMC3(~m'
    'Ra%lqEzzhYdDOC^SUirkM8B5gSWDDwNshHd+m_^5OO$R&j<rPhmgt_M5MS7N+lu^aMgFxy_g3iM3f)_wdn@v<6*<<5TDTP%2P(B9'
    '<65D6E0k_U#<fD}R%qLbjBACqtx&TSinT(cR#ZBz(5Mxvv_gkg)Ecd*ep{hYD{`|nx!IcBY>h^((Wo^VwML`X<YsGfvo+b+nhLiy'
    'x!IcBY>h^($<5X%)|%XGO%>Z3{aTZ$t*K&LQ^mGM>DFX%Ym{zH7Pm(C)?{&OvbZ&#XiXNk#v!e#j9cTE)?|2V+|!y2Z;h8)li{s#'
    'R%@Kqnku$6&T38e|2}*EPzv|<`|KG*DNMnBpLwaKHoY=Mr6Az%GiN0~zx(^lSz$9y)$cQBRn?XPDnBa--%$Je@{A~aNL6S{=0M@='
    's&iBuHf#hGXKG!2QVxc{YZ4o@J}C!NRF|G&UmK%vW67EQ$@gU_eET1W?+?WH2jcq!@%@4L{y=<xAih5k-yeuCL-C!(-RU2Q?+?WH'
    '2jcq!@%@2_{>aXpKNhmTy7b3F_D3~;EM$L8iptra{#};+0TuVE{IT-(Oq>yaWar8s%lTKG__~0S?@O~WecSPm<s1v2QdL_(5vWu_'
    '>5ioYH3`11iRmt&2vkZ@Jdq2TQx#&*Q3NU_sIUv_kL-f_V<pGZPs#HSlzd7$Ly5m2i8e!}9M#u_$!<*nl`<4FA1Dj)WvEm}L5I)}'
    '7Eu_UPDbgI*_CuMyOK_3SJKJs!8(~;S0|(N$tZm?N}tRgrIXS9WOP57y=f=2W9ei(aWeatPDb~W(dc9}IvK7{hTW6l^JExo!w#@E'
    '@Y#mUX+!3;A#>W0Ic@SiU)AYn7V@YKJHXn&bsM;D1J`ZfvkjcJA&=USIc><5He^Q|vZD?8&<4-9!R2jmc^jB-gUj2XLmOP)236W5'
    '`zjj;mnWQMsFa~R1KOb9Dd=|!`kg{PoI*aFLOz^AKAggyy;I1JQ_$}e^g9LpPC>s@$dyx2^Az&o6tq2sd^iQJPl4T2;PVt1JO$29'
    'g|k!hU5}wiIW^z)Se;&3-t`y?>{H2yQ^|)@$%j+PfK%b@R5&{o&Op(rFnB7QoeE0@l*CZXhf~RiQ^|)@$%j+Phf~RiQ^|)@$%j*u'
    'qOz`hu3rU}a+Ksl!e@p`8H(8r)magh%BYfKr=t6*<k+dW;8gPHR9tWxx}U~w*VEYTdK$Z3Pa}^`Bacoak4__VPDA(8(ET)Y2Sul$'
    '`)OnjD891jiPOlV({RXXIOH_4>NIxAo`!y>q1b6?bQ-Fhh7PB}{OQb~PiF>wI<vFWnVp@^?Cf-AXQ#7f1uC7+eEM`&i9yMgmDx2Y'
    'ZY$2R0t!7$GCK>XFq1l+Idedbk}JbOHK#MLI=zr_X<L?K;WLY~tkan-oz6Vx^g?z7mWu1brx&uLDo5!m@#%#TD11Y4&G>ZIjN3Aw'
    'Zp(bSEsC{8v9>7I7RA~!pKi<QR$J!NZCNvJ%Y3>ms<dV9+ZK&dRGvWxR8XufbKkZomZI=?As^bJUt8wIZ40$``N~||wuNdte0x#p'
    'wkX|}`E*<6%x!T&TjsuP@kCoZ(H0l9MfbLadZMcK407`fa`Oz7J_DuCK<P73`V3aL&LC4kr8CIXGss3zd}UGhGf?^rv^|4tJOgdd'
    'D2#?RIZAan1O3iGu`^KY3|2YLK%+BI<qT9g169sIl`~j_ID^%#fYKPkUAH4Q+mV~?P^=w_wL`IXDAtbLY{yzxJ2JH$nc9xrY==he'
    '$jx>r){fk4hkotI&35S5j@)clm^0TDQK^Db#oCd#?a149=-!UJZHEim;evMLZ9CS%+ToCP<a9gy(vF;NhkM%Lo_4sW9qwsIPPfBL'
    '?O4xhx1E;)3VeoSX-{9!p1z<x&T5ad+T*PDIIBH<L3{GOJuBVq$$n7$nMG%{$4l*TPkXYzJ??3bL)znz_PC%uy0=I7_GsH4HQTd}'
    '*&a39vjW+kwe9vO-5#aeqjY<;ZBIYZ9&J0&PjsN4=zy9XP_qMSc0kPz^b;NECpyqGbYM-q1N}q?R<k>xZ3lXd4y<N(K=%&xAstxh'
    '?tmvc(4%y~6CLPLI?$tZz%L!}O9y(C4)iD;@KOhQlnywn1J3F|kJ5o2r30?(K#$S^4|ZT>y#tQyKyT9le|Es19atgnfImCn&kp#r'
    '13gg(+}eSjsKa({E%rozVjcQVtV92ab?85_4*e(Aq5s4>^q*LH{u3+fe`4kNPpmxuiIwL+vGV+<Y_=5Ewrl>Bu@sINjPESiEPP7f'
    'KA`kd;;J@9$*0651yop{ub>)Gh~Z3lITK#agqJhn<xF@v6JE}Qmor(BKNDWggqJhn<xF@v6JE}QmowqzOn5mHUe1JxGhw15Yh4{#'
    'o9W2fOh?vcI<i*Tk=4nLmHsTQbUHF)@5qe3BQx)gthjV!CBGx<FCAIY?Z|3OM^^GXvNqF^wV95r<acDHrX#Dw9a*>O$l85JR&hGA'
    ';?j}1eMeSYIx^Gm$f{;XR^d9ba@mnpxU<mjEY?`gVvXf2)>zJBt@12ZC(lB^v(WD>^gD}Hm9tRuEY?xZLb0=8_bgaC3trBGiL;2k'
    '6Dv`jV4@RF?u3&&;p9#@xf5%So$z%hR-!t=QYTpI1WTRZr4ugigs(f{<W6|E6W;BFTRY*;PB^j?j_d^2op59)nD2xmJE21-)(1PW'
    'O4SLsc0#eUQS59KI~(twjd#z+yJzFwvso=X8z-NQVrQe+*(i24ik*$G&qlwq@%7p8c{U854QFS=(%JCR8D2WGmfo4Q^v<lMcgE$N'
    'ad~H4-WgwahL_Ip0*X4rQfF8K#a9+t>dZ=MXFT5-&v(Z2o$-8UJl`45cgFLb@qB02(mS&j+nKfW&aBLKW-Yxl>$IK8qt58wnLO%@'
    '3p$f4opHfA=zb1s>F2PPehzEt=a4JskSphqE9a0M=b-yJ=njg`LHBde9h6*I$rVuCR`kR<WX?G_<Q!Jd&q1+s(C8dgIR_oif%$Xb'
    'x(i%)q3`KJ9(5s)x{ya*7%jSxRb3b@x>QaWjd|(<^Ic%R3+#4*vo2&#7c!>{nbU>L=|bjoA#=KrIbFz{F1Wl4>~_KBUEsP4qeT~b'
    'zAj`ym+e$3juu_$70*Snb5ZPEGT>Y?;9N4`Tt<s?$%k_pEzU);b5ZPE6gwBi&LsoRMZa_L{JHRXE)1RvXXnDwx$x2zUb-?`bY-;Y'
    '%4pFQmv_bGU2%C=eBBjZKv7p%>IzGsaAkorP~2AJtSdc3S2Cb08PJss=t>53B?G#W0bR*}u4F)0#*VJ^L|qv>y3#LoW$frmFV&T-'
    '>WT}xl2u*tL{~DWE1ozH7o5k~aUNsGd5j(BkvZp)Ip>i%=aDPt;Q~-}9xgZ!7l6W*1s8zQwmgqOaa++L=aE(C;g|CmNzOyR^HA(O'
    'G&&De&O?XuVE)e;*EJzoGE^#{uwGD8U7Mp)1qB^KL^&$uC|!dHbNd{Hw+O2<R4TM3-w@U2sFb5bv2Y}GDMO_)%2p)e`E>N>@_yRz'
    'D?>F^87d_!ClwS{;r^VjU4#{$3W{gfp)GVwb+zFfv)VtG*Df-YzKIonv7@Ty&*j~x@n^<e%Ad<`Tg9IeC+nZ{b&cvI+GHUy{><9s'
    'uG5u_9EJ2x-`opVhG}FRLyW5alB*KmXw6@89cp9d|B^EwMvuQ#)_Y<;|591+iNF0XmGz$Z-(PY*!?*t>XE3br`~?R80)u~nv%lml'
    'g*BbO<SeDA7<&cPq^Qh9P4ewUUjCBvQUfZt6<DgEnldVKmZ7k2bUq$D9}k|72hYcY=i|Zi^EI*<)nurYql!Pz$Diltt7#!uGE^#~'
    'qIb`S`SW4^e7t);I-HMp&&Rvx<K6R7<$RbwAFj`b>+@mv{K`sO9K!{;?gCtQ0j|5CvdS2xe^>F~1(h|&<THzoyZ~M<fR_tk;sP9b'
    '0gk+Y*e}457vRVX;N=1wc>ye4081C($P3`?0vvfkW#ux7w#es&^uia??_Nkxdm+BQ5MN)2lP|=d7vj1LVfVs(-8-!4UI@Dv;<F3!'
    '*@gJ*Li)%H=@l<ThYR8QLfE|!b}xj_3(K5^h3=^8BKpXS=p!$pkGu%CUW8jO!mStK&x>&6MR0ZzoLvNG7vac@aO6cWaS@KZ2uEH7'
    'OBdnDi{R`cIJ*c(UIc>|;mC`&<1<5HW&L8<y%=^chTV%{_hQ(+7<Mm)-HY>Q4B@H5#c+KwTwe^=7sKwwuzN9lUJRcX!{^2Dc`<xm'
    '41*WL*~PGQ3E6lF*?0-rcnKrPCFJHMj24%Wsh7aSB`|RbuDgUxy@X7?giO5z4_*Q<m%zj&IO`I;bP4Xcg#PSOo<d#9Q>aUM3Uw(@'
    'p)Tbq)TKOyx|FALm+}<qQl2|q%5$endD3(#&z3Ib+0vyI-K&!;Gu`7qy|kix5?}G@+@(B|x|C;9mysQpksX(j9hWguUPi85#z=V?'
    'xpEl}xeSL~hC?nRb1oxuF2fU-kw=%2N0;H3%gCe4aL;A9=Q6VDGQ4ydId&P&x{Qpwj8XJ5Tz5IHyBybDj_WSRb(iD1%W>W1Jo~&H'
    '*Ikb5F2{A3<GRan-Q~FMa$I*guDcx9U5?K#$7fgIvn%k~75MB5e0Bvsy8@qGK@WWeuDb%)U4iSaz-L$Bvnz1c6*%h(oOK1xx&mii'
    'ftRkpJy+nDEAYz|_~lAg9j+{#6<A$!C2J5@vIcP_YY<nm25}|p3|F$2a3$-|SF)%3O4bWN(UqKTd?h=zuVjVbDo#ecioIJ`v3Kh#'
    'PDZ?{5N&l$hN1#WW3S3ll%vWSidS)l;#HiXcok<TUd0)TS8;~oRh*%C6=x`3#TklMafaem><+t%lf<s#)WoYe0q`pJ@La|2o2$w@'
    'WrE3TYpyC+xbbI}QTa3D|E?<6yEVyj(^Z_*balaJRi&%Z=xQ{&8jY?-qpQ*AYBahUjjl$cs|#+epeRR~Ta!CWP*g#=4p*bY)#z|F'
    'I$RB(SHtJk@Od?SUJajD!{^oT*$oD}!C*HS>;{9~V6Ynuc7wrgFxU;3cf;k~aCtXe-VK*`!{yyzw;SwsgWYbh+l{@_-FS1M8yV0I'
    '&v!$WZm80&vV$S!x?6eYSWu-VK^4Wip;5Q;dSqDatuCYFy@G_Z;u{Fvc;}!SZy9vsErV;wm1|J?8kD{UrLRHhYf$<cl)eU~uR-Z+'
    '$dzlzm21eAYsi&rQ1cqpyaqL|LCtGW<r-AE234*>m1|Jt8dSLkRjxsmYs#y{3G)dGF@#@r2r(3OxR!UoudU1mW7l8Hj<ahkbHgY~'
    '+tRsVO^V9ZMVu_xQfFPuJK)z+bzMuXe=Swlwd^>%mKy9@YOrg|{YzK_ud2Sb+@qAj55C7Jt0$_HJIkw!6cwubYpJuYgO}^z<vMt|'
    '4qmQ<m+Ro=I(WGbUao_e>!?PrgO}^z<vMt|4qmQ<m+OfAI-<RvXs;*Q>xuSyqP?C<{CaBd>#4o3C-&=!{d!`*9#33P?AH_f^~8QX'
    'v0sn2*AwjxM0*3#-axcB5bX^_djrwlK(sdy?F~eG1JT}q(l-$84Mckb(cVC`HxS>A)Vnw4J!V{1*4)UG*Bg2AdLvI>Z{*4AjXYhw'
    'k$U$=>fIZ8S_X=4q!zxB_Y`mBiP()iLA{Y@rZ@7G^hTbG-pG^C8+np;BTqta<hk07JPEy#r))R!MDs?TtK9_GH!-)kiMhp1%q?zW'
    'ZgCTHi<_8R+yvJ*!SzjW4T^4p>zkN&fZ{8QI^2W~H!%yjiCM@^uzM4H-UNd;!P(8Mg6Ak<{$`#`-pmU5%{-aBnf3CUc`|u3>uxvm'
    '%;sihv^Vp_;bzuRZf0%mX4ckjW)=MA{7GRLWp3uV;m!F9c^HpwX1)C8e6MtM5_`5gx;kO0I7_}cUs(w2Ha9a%zL_<aTUgP(rP80p'
    '-*5}-ySK2udkZTBx3CIu3!L2oXScxFEvyOL!kWM>IcH%!x&_W|fu&pErGjcwRA8xsYBH3sGu#4$x4>Wp)nq7NgSZ8DZ`qFB;u^%Q'
    'IQdqbd@J6)6}R4sKW~NITUled6?SjMk+<T=TXE#A@Odk)yA^hCh0j~z>{d9tHDAvPirorJx5Cn`tnA&!2zwhN>}`y&w^2RaM)h<X'
    'W9n^;qPI~q+{P$+8>8rLjH0(Oirz-ObQ^W#ZM@ZR8}BjP#;V_Ktoq$X{aHaZpftW>#c~^KfVVNe-%f_#PKMu3hTl$x-%f_#PKMu('
    '2XDuNx8uRv$?)6B@Y~7o+wtJ-xbAjx`gS~cJ2`zjIek0+yd8huPEOyBTPvuhfGVF^aq{gr`F8UCc6@z1E0A~K@;h+(9k~1sTz&^G'
    'zXO-wfy?ipR=fk3-+{~Tz~y(~@;h+(9r*eVe0>MLz5`$1fs^mR$#>x0JMiwEc=t}cdnew#6Yt)Mckg7y`c9mDCr-W-C*O&8@5H-z'
    ';@vy(=bbq6P8@kBj=U2O-ihn(#C3P#x;ydNojB_*oOKt@x(jFB#SG;xW+-<tL%9o|-G$HYqBp$@pWTJe?!sqx;j_DN)?GO3E}V52'
    '&bo_!@GiV`7hbv>UhamMyW!<-c)1&1?uM7U;pJ|4xtsjE8(!{)m%HKRZg{yHUhamMyW!<-c)1%U?uLnbn1$TKjPD+1eD^TpyN4Oy'
    'J<Ry-Va9h4vygk(EeVS5VTN)KGZavKWpSo)4>P`dnDO1ijPD+1eD^TpyN5Z+J<Ry-VTN)KGroJ6uiV3o?;d6^_rmqP%=qqQ#&<6>'
    'zI&PR-OG&cUS@pv!u7py4T|oC>wDoElw4Vv|AFGRq7L^m$GaCk?}fp8;p|>mx(}A_!;$yl$op{QeK_(y9C;s(ypO%Tpy)mryblIJ'
    ';mQJMpt!Bb%YFFsKKywf{=5%=-iJT$gU|c$=Y6nyAO5@#uJ6O2_rd)AFn>S(ydQtwk3a9npZDX>`|;=fFb|6Ehxz+q9u%%DFb_)G'
    'a<_uwwxTNc<JS9O_kQ@i9|rG-vj>>RJ-|Hf0ahd)U{?14D-sVd$9sSki3iv-^Z@g}2UwqYfcoVD=GqTXi9f(>@BwCn4=@{ifE9@c'
    'm<>KaUH$<3Lmr^Ed4P)L0d{>nK-K&pRo;VCc@I+MJxG=JAp02}q~?2&D(^v9dJvW#grx_m`5vU^dyv>4q~?1NCLUxz!-G_S55m%e'
    'RCy1=*@JNQAiEnL+>XIwJ@^p*d<cI&gd-oqgAd`lhj86PF!&I4@<TBA5I%bdpFM=n9>Q4<!R|xw`4F5v1WOOW(nIj_5Hqlc@!7-p'
    '>|uQNFg|-2pFNDv9>!-6!_vdB^e`+vjL#m%XAi@~!}#oBczGC~J&eyDhO>w9*~2jSFbqD7&mM-)hw<6N+p$}mg**b+kHGaKaQz5e'
    'KLXc}!1W`{;~s(eM_~RDn12MWAA##fVD}ODd;~rpfzL<a^AY%b1O^|0vqxa5J5RE66o%<2Ls0>R(Kj9_a};H$@C3X&Pr$qL%)2|!'
    'yu0(vyF1UkyR*BYJG&dYv%8@?yBoT*yP-R~8@ls6ygSdsyYoD}JI}*GakRz#4Bgq$)1BQ7-PzI8ou}&Ed8*!>C+FSSfzqAl=-t_Y'
    '(w!YB-OK05M@hldz5LrqHOY%-kFtZ|QFMP4-5*8wN74OJbbmDcQGmM8vsX}*p@JtK#S@R>iAV9oqj=&`Jn<;|ARc8O#G~wkc$9q*'
    'kD~jd=>90WKZ@?4IHIC{kD}kB==Ui4J&JyhqTi$F_bB>3ihey%tOttqK(QVu)&s?Qph^!^>47ReP^AZ|^gxv!WNHsGwFjBngG}u~'
    'ruHCHd!Sek6zhRvJx~l3M_b&L)Pr3~J;>r7<ZTa>?t#)h*#FXl{VzRmK@W8Afwn!^4by|&Fg@6#)Pp@rJ=mkvgS|05$?%@|r6+#r'
    'iC=o+m!9~gCmG(84DX4Tdg7&?c&R5|>WP<n;-#Kscuz9CCmG(84DX3wdg7O!_@yU)0mTs&b?=GpJ<+`<y7xr)p6K2a-Fu>YPjv6e'
    'E~uXDg6fIVk7a6xS95C~V}HnFnVLbQv@NM^LV58RE0B+|=J*(^{ExB9{}`)`kFh`GG1eR(V=eYE)*K&W&G9kT93NxN@iEr?ALGf^'
    'V?3dHjFtSySc`p(HOI%{>~T1I9L^qxv&Z4=aX5P%&K`%e$KmX8IC~t<9%r5QaX5P%&K`%e$KmX8IC~sk9*2o1VB!gwcmgJ#AoeGS'
    '{R!5npJ0vp3D&5efQcty;t7~|0{1)t6Hmaz6EN`vOgw=Lo*?!oiTz1pf0EdrB=#qX{YheflGvXl_9uz`Nn(GJ*q_7&PZIl+#Qr3)'
    'KS}IQ5^b+AA~Z>R{iwQExxcOo<kn;;0+lK#{9Q=63W~yi8H#8tl~Fh>v%Gd#m7yps0tA$fzG2#*pkxIkbf+l_cO9lOF-o5*g!xxZ'
    'O$F6vD7i9xXa$8iUhgd0FvY9xokd#{BFaz%DpgREbhV<of=VIU3`Mk+%BUP|@=IkI3hR$G0j1G~31))Q^`5E>m9;I!s2pEyh_-@i'
    'GgMxmC>2oniau!D2W|VHW*^k-gPMKNuMhh5$xcZPCu-y<)vpiw^+CTr=+_7R`k-GQ^y`a$ebKKkiuFaYz9`lgjryWd-z=i=>Q#<X'
    'jryWdUo`5AMt#w!FB<hlqkd@A4~_bvQ9m^5herL-s2>{jL!*A#8bmm6CP%48{m`f%8ude?erVJWjrx_>5|W33RsFKwCUl=w{n4*K'
    '`t?V@{^-{q{raO{fAs5*e*N<mm+Asa_3Mv*{n4*K`t?V@{^-{~i#EyW{)KU+RP_|vK83bVq2^Pl`4sv+g?>+=-&5IW7!IV)QL5il'
    'X!H~sJ%uU*P-OtB3_yng=r9202f+LQm>*CWwQF*eGCu%z2f*$C_#6m>1Idno@Hr4Z2a+8F;d3B;)<E)MAbbwYo{uF@y#{8d6erpa'
    'Bv%HKD+AGCAUX_!>p^6|AebKn^MlBMK`=jvK5G!39|ZG*vWS9y@n@DJN?b6Ad>BMN3_`I%C^i_42BXnnG#ZRXgVAU(8V$ztgVAU('
    '8VyFH!DuwNJm;zj&uC+mX%yC|2czF$^c$Qj77nx;jGBW{b1*&MU~+5-N)JKlAt*frrH7#O5R@K5jtxQSAt*frrH7#Okc^jPSJ{wU'
    '>A=enTrdO|3@OaAO4UQ~#1K3&gg$ZzIXx7=48<WsamY|SF%(Y>r5_xMCx+sQp?G2_o*0_VBEy0HF)Hdl6y1lS`%si_K<NgwZ9v-w'
    ')NDY_271f})NDY_2Gndo&4$9fxF$wL#Trno0mT~7XjnEr1U{o2B~M~96cyUSJSU!L<R~hm^f`Jsx4yaxl(r=ig=mN6b#fS2K*^P1'
    '=3NTn)(*>7@4~dI3KR{?`@xv%Dp1mvtj2^1SQRL3%TBSV0)@81bHiagHyoC&{v=Ndhh?ijwehVasQeAFCx-EaaagwA6RccD^>yJS'
    '{Mr<S^`7dO!UQF&el;NlhGnaMaXhsNO4fn`^`&7v2O7qcpJCaPpRkM>r6_0=#kV@Vygpc!{A%xTbRUlH!_j>>x(`S9;bo<h-#Mrn'
    'jtfBPmAMOsqx5i;28F*Xs0m8jay3Drt)S*`)EthQ!_jXz`VEKc;cz_y21mf)2pAjzgCk&Y1e}4=ww$vOWDY2~vcl&G_yk2G$Q)48'
    'R^b|yw&h%dLR*3B5pX>MUys1oBeK=(xcjcH8G*}3WGkLkAy-DA!-(y4D0+Sbo=;GCsu1UC@+pOL7Dkc}BT;iCYK}zBk*GNmHAj*U'
    'BheO=UYTn<68%P^A1M4?K_gJwmTLqGZ3T@+qR~j$9SOT5;cQgKSs2Em3`L+)1*M~XeAlCxEoCU8t(2ic%`l2ps!>#&qo^lFu`V@='
    'igOfmu2HN@f#Pp3&KN*RTctJyrEPgt0*c#;_2($+&rwt!qo_Pa<rQbx8BjsB8A|^yDiu&TWo0x@9*vVn<K)pec{ENQ%|5cx>>L}-'
    'Ua`@fTR57N3P-b7Y&4!9O@9W8|E}0efs(e0%Rxz7el}qhC~eD5qN)OgwnBD{CObwm+K*;@7|l+#(d;K0&DcMhv41pU|7iNi(e#m{'
    '=@mzlsiVo%(e#6(=?BMTc^ejua}<F}6_nPrakyhxJs6X_r`T4?P@ys&!+Pr&W<+DCn#ZuhI))k17}g-hu)+$8zr8pw1|@Bkxf3XD'
    '%WH2?+*X_)jbVN?hWdI8_4Sy1Milb4f@(8Vc3r7}Lf(!gZ^x3iW69gG<n37Ub}ZRAmTVl$NuguO&9R&YI+jcwOQwS2&n#vtC~2!?'
    'Dky2IWGX0a%QF=e+6tLEmP{Q>9*rfB#!_pHC9B3#Ym6nw#*$-W$+5BI*jQ?fv5cGJ$iH#q-#GGb9Qikn{2NF9jU)fYkt^fK6;Qac'
    'kSn01t&%ICv@OpSP~2AZ{5U*64$qIn^W*XScsxHImygGh<EfX%Q!jy{@%cPFPTQ*SxD}LKS*ff*X<P1OP-rVSay*V4&rD-HBguH?'
    '9pf2S#xr(|XY3fy*fAc@kH_=lart<BJsw|ApcbBhDics;0;)`)-kpF(6VPZvwwpfj=L8f3MH5hL0;+(LD=VsiLR&$V38*pwRVJXr'
    '1az1HXA|ITA}mdWrHQaK5nd+3%S4y}MH69SBHjfhS5{a8rENJ&pwL!eX(B95#90$@)<k;KiTG?Hz3D_4oVXo>#XfQp9-IWblVEoe'
    '>`uaili+$1Tu;J-lVBbcO@jGJunS7Atgs6TZ3T8G!R{n@nFKGB;AJv%uF1@@CNs;L%q(j%^Qy_rt0ps(n#@dUGIOWN%$+8)PCJ>|'
    '5-6I?YzdUM<+CMF+*X_|O=h+<nc320W=oTqElp;&G@04bWM)fK@Yxi6HU*zeVMa8C8PODGL{q52rci@Tq3W7~Tc_Z<DdamSnu6;<'
    'Nn53|0;O$vWd#at1-DMYty37erqD-DVGcBfInWfwu_=sWQy9ml(A!L*x0yo!GKI{ULgq}R&YDVPHI>S0DwWk#YN@HrWu`KFnab>C'
    'D)W`8)L>J20x*@T3lvSI>H?*0dDR7q+ln)ksmxHOGDDfl3}q_S+El8wsZ?uIsn({EE7Qo8Y2?Z@GGH1RFpXKrH1c5@vyf?I$278I'
    '8rcDgrjZ?>q^*)2ptLQ|4p3+-WXCkJV;bI_hIgkiQclCk(-<kI;p=JmdKx3bbX-0imruv#({cH9Ts|GQPRFg&aVseNUBRuOv@Lfl'
    'C~hmdZaS`;j_ao5x*603Gw|RHJU9an&Y&)sftO}b7tEk8n1Rn`WWNp_I{F-?l>jK3f$Kn_t>B&+xMv3S=M4JR8F*p_o|p+QGvQ?>'
    'yv&4`neZ|bUS`6}On8|IFEim~CcJ>6neYM%Z3SLt!plrzpSfM^#eA3r6SH7q7EH{7iCHi)3npd}`z&IgMeMWkeVjD~ltv2*-&crs'
    '7SYZ^_gTa~i`Zuq?QEi*O|-L#b~e$@CfeCVJDX@{6YXrGolUf$@O_17XA|vg;+wr)d_`^NQ2oxK`kh1dJBR9b4%P1*s^2+OzjLU5'
    '=TQC5q57Re^*e`M3UjD;LD3xQT~ORstas;7@6Ms#okP7lhy5sXsD9^A{mx+r!yIbiIn=^)@zPwpG#4+;r52t`Ej*W6crKN|Tq=RN'
    'jQw+Q<Xk*B7oUNmx%u9TsC;E*d<Ugh=Hojkv=!Vs7q`wOH|J9C&ZXX+i?8S6>v@dY^BA?~F>23a)SkzvJ&)RS9<}K_YSVetrt=u>'
    '=P}yPV|U6t#&=LOkMSK8w-u|=c~qnGs7B{ejm~2S(LAbzc~lAW*ts%~nqeL_!+e}PA1BYp$@B5&eEd0|N_9SNolm7YAMeh`yYulb'
    'D4LIV=i^;adS&iiP-rW7cRt>ok0a;f$ocfN3-IRx{J8*sF2J7)@aF=2wg8_kz-J5a87NwS&p>fo(Ju?|%L4qe0KY82FAMO?LPnW|'
    'j4KNnR~9moEM)9h$Y`;U(PAN^#X|P9Eo6KE#ot~W0~Rs{ETm^&NYB2Io_!Jdu!wwEL_RFS$%}CEBAg5ge^+qwqI`#2U}6#81%<yW'
    'cy|%rT|~dTh@N&4zFvf{pC;O;iS}uteVS;WCfcW|be<-5Q23NW>`xQ>)5P~Q@jXp^PZQD8MDz@~`3%|k4B7Y$<HIwI2+xq4&ybtX'
    'keko2L-8515fp!Wv1fmVp8Xl}?-}y%8S?L06nhrMo<*@|QS4b1dlrpA;qM9>J&Q)q;!jZcyMlhtqTjP9_AH7$OW*n&@jXX;&k^5q'
    '#P=NWJ%=NoBU(`SltQ%65$$tC^c)dAM?}vN(Q`!fJdS)GM?Q}upT~92<GSZ@-SfEad0YpIzoF=?=W*8aIO~PF>JVXaCRbH$KygBp'
    'Pn!xT6s}d()wNZn7&WO&P<T$7qvTh66BHK)=}A;6s&5ot@Qtby6qf?wo#hnO$CsvOPrXn%)jIz7Lgi$r>QWIUpPB!fPI6_ExXIh;'
    'rT9~lO~J{zX(?)ypOpPV`9!JoS9o41_bBPF_AU;wH_m>~dofHbhKa>6u^1*6!$gYe8z-@+C@zY^YtT`&7$z1cOvG);FMltFm&Ne1'
    '7+w~`#NxU%J;J-yrD!p{EQXiG@Uj?Q7Q@Snl{e+%zk3m0UWADkVd6!Yco9#$SUE{7{=OHBCl4g39BovSqD*&D^kOCU<jUe*zm(l|'
    'xRvUcvbzpPj@7=D-E~d4>zA_otO=Lqs8s%x^sW=dUdo)DoQwKW7DM>6s+Y1Dq7cJNSqx#@M~cFo1!+Z5hQd#tge%K2gaZs}UdE9x'
    '!~DxI|1!+K4D&DJ!I$yi%ed}keD*Rvdl{d-jL%{eI<53=|LT{^zl<Fvu6w!s%h*Aq1QlHOGOl~MqF-`lQO#GfXu|;l0hJZ2jVr<&'
    'g`cS}x5d%MM3mb?wAC@HeI<)FId$Qcq-U>dTndK-RAs0(e55FPr7oSahjWHX@i(LoW`bZTii1zaj^xTPkxSlEPEj0gKyl6TN-|o6'
    '?+f3*gou_9(GntBLPSf5XbBN5scV$%stIFGxH7I~l6wj9Whjjg6fGgXCB(Oc_?8gg65?ADH>KZ~#uq|J@1?4CDbXe<&8j%SrNq9J'
    '*q0Lf(mWgEZ%qF#XJRQ#EJfR;XuFhX6BK`DjN%VnO6&=W+oB}efWii*nh<S@^4OOqPv`0y*M!*PwxZI@h<zEcFC+G4#J-H!ml69i'
    'VqZq=%W%OmT(ArmEQ5(<FtH3Kmchg_m{<lA%W%OmT(F!TY&m1<a{9C7^k>WI&z3WiET_6y&X~HKQFM9b6v{aE0!lum*z+x?=UdL0'
    'vz#$?Ib-T_dbj1}Cl%Gnp_I$%&z8skGelG!l`<5VkJ5VysJ>A+*)qfsD!%w*gX{?k5v3<vu3&sv0lO<;cLnUOfZY|ayMobT1*63Z'
    '*j>Tcu>!7F!1W5)T>-l*7)e&Z?h4pl0lO<;cLnUOfZY_;H%|CWQ5;cq$gyYz?5;@IjoWHVNkm1iS5gJ7gzJ^CyApO+!tP4EyOJts'
    'B~{SMqCZ8^N-Ct4R7jxs$|6fEVQD2St;B<?sGe3)J*}d8T1EA=it1?<)zd1fr&Ux>tEiq<Wzh!3MA0fLt5sB1p!mvi?4diWSw&^F'
    'DvP~T%23ktrQcA_zuJ(0tI4s|=)M}=SEKuCbYD$YttP8hlSiw`oYiE`YBFavnX{T2Y&A95YBFba#S=+e(IKm;!B*p!)%ayKS+$z1'
    'T1_6UA#>Ki;2IcQ1A}W|a1EKWhRj)0IeR#szk{MRWYrq73Y1(~$s<tQmhOR!LVz`E;A{;nt%0RAWL1pnk})+(Kcz`sGNwl1K3^r{'
    'UM1sRCF5Qt<6b4>UM1sRCF5Qt<6g~J3g;(_qF2erSII_Da%Cm|Kyh1{vzid?t7PM=WaF!3<Ev!jt7PM=8H1(tGs_H?(z_0*zEKoh'
    'SN&S0vWorrTBWjzC48+?S(VCdX)P5G0<UFbTy?0CUaM4A@z=kWjd4|B{qD6;XC;+!IQ$J1U)d<RnK-(bK~UaS3Z+}xmQ+X~Azmxj'
    '*I_XxT$xr@wc*gc`1>-JYLXbjafjhkLJjy@x$3G7hpz=xW+|NZ7Eq(|omJJomRDpoNkn;lRz~Uf)g<v{C`7v!KG(wMTKHTGpKIZB'
    'Eqtzp&$aLgiZWD6>ejV+g&T(#P=U|2@VOSw*239ZI9m&6YvF7yoUMhkwQ#l;&ep-%IyhUGWokIGE?SpmYG5$^yPUIiu(S@A*5R{t'
    'FtH9M*5Rdf@UjkG*1^j<cv%N8>xg|Fv9Blg^~AoO*w+*LdSYKs?CXhrJ)T&PC)UHndYD*G?CXhrJ+ZGR_VvWRp4itD`vzj)K<pdH'
    'l?~*|24depu55sb4KM+UHk6qNzc*iQ%TQ=5_yv@<rE~l0a$AP-wv@pQ^imse)&|(!0G}J+a|3*CC}&l;&k9O2ZUY&&0p>Tr{6^-}'
    '8<|gUWInx-8T3YG&>LAj*vRSuDB8#@c_V8j8(Aya$Siqdg{9=qit7a%D=fwTZLF{qU%IivQYl60X9gxV5&I@$-$d-2h<y{WZ_4v1'
    'xCaz%Vr5|yD+`-gSpda<S7d1uENz0NO|Y~HmNv1nunCqn!O|vJ+EnpU5?^seViOE*CT};Bx0}h^&E)N7@^&+MyP3S*Ox}W`&Ezd8'
    'Z%cc(&1B<dGHx>&x0#IFOvY^{<2I9Vo5{G%WZY&lZVRs4g6p>6x-GbF3$ELeM;qeXf(Jp-7Cg8G4{pIPTky*k{IUhVY{4&E@XHqb'
    'vIW0v#V=d&%T~s?t&DM7@yk{mvK5DH#S>fUy|>a|Z^aW^>65qOkgYgmD-PL;L$>0Ot+-$-F4zVW+hAfFOl*URZ7{J7Cbq%EHkjB('
    'K5QfQZA80`XtxpVHlp1|wA+Yw8_~YbjP`YAw68OxeVrNY>&$3hXGZ&a<(GEiXhHwKtNV_(qPp4#e(&5vIUu2nQY};qEg@h*5f$vQ'
    'VL`+OA{|A9NHiu!V~f#Ld-8i@Of0FE#FE&}8(&KjV{DNk(!0F@zu7Zq=Ik&2<?~s?y|bR@S!=I7Gk2zp<-6Ut+3kYDk<tDZl*h{b'
    'Ehvq}``fqK-@eWM_HFjJZ?nIBoBi$E>~90gt{G<!%`RfMyNKQHB6hor*zGQ2x4Vel?jm-(iwXwAfeoN!5j){U?1Vw#$Y}2i%46l;'
    '7nH{0z3(FSzKhuVE@JPyh`sM3_P&eQ`z~VdyNJE-qJry6o^4hfEt<0Hn2YJxi|N;k>DP<7<FJ_Sy_oL3n0aY2^U`A0{>9u!Sj>Hd'
    '#jO2{xudd}&c3*0sVO_NczRk)pI=<E6eL?*@)FwAVtV-!cv%83OW<V*yexs2CGfI@b!-VM*AiB)B}`9C;A{z;ErGKoaJB@NmcY^y'
    'R>LK*v;>xxu>LJ!{aXTqOJHy*3@(Mir7*Y@2A9I%QW#vyT(A^Am%`^#_*@DTOJQOuOe}?or7*D+CYHj)QkYl@6YsRlUW{K2S8400'
    'S&71umo>K%HLIiG`OpSS)T}_Y9vRlE90fkZnY~kX%p|3$MB$<QrW}PMlg3&sV?KPXC`X}VrYQXlS<9*h2R1bX6wWLOXO^S%T=MJC'
    'DaxMp&7NPXq5NFxD17TJNl{+K&9W+fC;NM@&=~^r%Q9Z7VMRz!v_Q=wR4}*<2A5@=g?|@LyFkq%RIs}Yc9+5KGT2=PyUXBn8GJ5-'
    '!DTSGEMqWR|5AT0gU@9dpCJ~qSO&YxV0Rhp7ASn;FR7t|-DR-540hjTMtQgPj9IfRiFcV;-eqDbQI^EJMYh?uFWzMidAIhYS|$9<'
    'fTHW{@5Wyb$x!*dkQ}uP^F%N&C@D~5M*X|BXIS&^8!l&NSYBk5`DHm1#BwHx5>;wHrKVr_ealPzf_axS7c4LG%hX)XHSy&|e%Vty'
    '%ZvQ7&wwm1G72|BMM;6em%@@XR?9CdffcB-g8R2C&}ao3tw5s{MMmNG<^L|bW1E(LK+*iUg86d=_t95yr*{SSc2{suY6bVCRxnkr'
    ';F+NnD7}I^y(_rWyMp^wD|kw11=HvX9I}#obt~a>C48=g&z11Gvgnv0*&Jo}>cUyCgwK`mxsrQ)E4jzF5<XXQ$8RO<u7ur{u)7jI'
    'S91SvC48=g&z11G5<XYL=SuioMGsj8pQ~VS6%4Mzk*nw$tLPJ}xRbq#=lNFACqT(6`ot>EdNpUgnzLTbS+C}-S98{@(RMYpvYL!m'
    'lhJB2TFssdl&mJ()np4wkBl{1O}1<3ifibDYv_Y(=!0wMgKOx6Yv_Y(=zMFq|GtK&7uV4FK*<_9-x@mKT5?!R4r|F_Ejg?uhqdIe'
    'mYw2Sc8Y7+DXt~kwPd@NY}c~m10`!=Vl7O7(j(*j-&&YhM+aMnch}+Fb$E9jJ!>63YaLErN0(Yhms&?(T1O{ZM<-fGCt61*TE~+J'
    '>v$4j9Z!R<qc5$aFRkNAgmqNFIx1j2bKQF8y7kO;>zSI@Gv%#k%3IIWyq=kFJu~0>+RT@gbi?}E%$JpIhJw+uldho<3-iSK+RT?f'
    '=dqp%a6J>?dgkl(<uiNXyVC2+XZFIEq;nLm7lf~vt!Fx1&vdwf`FaEM^#*3>4b0FR;CcgGZ-DC!aJ>PpH^B7<xZVKQ8{m2aTyKEu'
    '4NTh`n6Ed$?grT10J|GtcLVHhfZYwSy8(7L!r(?2+z5jkVQ?c1ZiK;&Ft`y0H^SgX7~BYh8)0xG3~t1&8*%GK_}mDe8{u;!d~Sr#'
    'jqte<J~zVWM)=&sPH_`E#Z5SQ6Hea5PH_`E#Z73m35_<P(Izz7ghrcCWfQ7wLWfQ0un8SDv2WajlQ*$%+=LFB&|wogY=ZesFuw`r'
    'H^KZSnBNS8n_+M>3~q+O%`mtb1~<dtW*FQIgPUP+GYoEq!OeJgGn{RPv(0d}8O}Dt*=9J~3}>6+Y%`p_$Nc#oJMZ^c(cfc5e~%UY'
    'J*Lt3m^j~K=lve@=X>nD->dCR8^hQoO5S5v{vPuuC_S>qOL$D6>AixNB>yS--}g5*=COEXexJGSeRk~cGv&R{l=nVU-up~>?=$7S'
    '&+PU-JNEaP<lbk;{(iwkxbZ4V-e))eK9d|MJ+kmi_@VEYe#w7I;g|4NeeV}6HRVUfGv5dJ<pcck0e<-azkGmSKEN*@;Fk~Z%Ln-7'
    'gW@j?vmFX3`2a6{fR{kok#+Zg(pc=C4{*;1#g*=CHvOQu(w*eLz4kSa#yl4L>;ruEAq;*9XCK1Zhj8{GoP7vqA99xslza$-AHpCg'
    'JF?ChD36t#fznva*@tlUA)I{(XCHDO??V{;5C%Woj=}iO-G|({`-m$3h${YwD*lKn{)j66h${YwD*lKn{)j66h${Z5U^m-=fs&7?'
    '@Q<i)P<CX!ra@^euIZ1c>5r)CkIK6=P5F_vyEOT^<S#NyvK{6}g$_;mk#R5hh+gn9Tz?F^AH(j)u=_FWehj-G!|uo2?F1zs!}Z5-'
    '4a$zJvkS^&CA*+B7PI>??0yWpAH(j)u=_FWe$2hrkKy`bxc+!MuH*ZuA9FwTWA3MZQZgSNy!eE_=lZ0az0(mTk7f6=Qq=4d?udQD'
    'J+M!>>-7nDy*}Z7>L=V!1tp*G7hIok-|!Qjv-*VRtUlqs;V0Zd{giA!CEHKQ_EWO`lx#mG+fT{%Q?mV(`*@#nAMaD{i-M9m%FiWc'
    ';!~LT6ed1}iBDnTQ|=9Z${oMYSY<wAo&Jn9=QGxv&scLlW6k-DHRrQh=L^p{C8Fdr*6`0*b3oz9Xw3oTv2x7;rLlO;`HVH^GuE8X'
    'SaUur?no#3dB$tbXRJA&vF3aZpP$3v=P>v=41NxSpYz-dsEp<8eh#~!aAdUFgYsC(H7JYKxd!F2l50>Ji@E+Bu0MzC&*A!Wxc;2g'
    '{&SfB9OggYj`?`C|D4tSbDq=rf}PtJ?A*TK`otIP<Gx@Y_XXD{zF=4P1-rU0YP-5@k!b)WU)1)+*+S9)%3|3*HQWDzYO!!+s2orp'
    '3;WdUDjcYcRkEGp7wiqcU~l*Zd&4iv-qVmDSzEap@*`_2S3~W{{279DrA~4bp3_ND8mne|%={Ui92L*-q$miOJ+~JAU1qEn;W>ox'
    '@8aiX>ZnpfVV~NR?NjS0)W;UCoNQq?zXca;!3A4z!4_Pw1s80=1zT{z7F@6e7l4v2xByhfD%q8jEj6Vp*}i`ZYHmTzEvUH#HMgMV'
    '7S!B=np;qF3u<mbu`MXJ1;w_Y(N=WWiVj=RVJkXpMTf2EuoWG)qQh2n*oqFIWGgy=vRJ(uLA6*>ji54?E4CHIwxZZp6x)hoTTyH)'
    'ifu))tthq?#kNv^TdBXTsJRt2x1#1&>Tm0I+Q#*_jjNj5sK#wvciV<1w&96wcw!qa*oF(Xq5C#;--hm>q(J%ZY#SA~t)_Io)7XZZ'
    '+fZ{GYHmZ#ZK$~oHMgPWHq_jPn%huw8;Wg1v27@}4UHPAG4nYpn9oqje2OCG1FAD$qKx?rmCWa;V7{RmGY?7{s&Q3;%2>{Pjtb^8'
    'R5IUCjhW9-$$X9q<{PRp^BF3c&r!jAKy~JGR50IAjq4~!MIEImQYA-)Dh<_Gl{%`_P^?j0M~&5Z2c4nvYDHr;-cL7H<Nb7rGGjMZ'
    '<Nb7FHQrCBEJXY13}xSO2#SG{0_C-mqG&%23P(o!X;2<3_tT&>7VoDUtMPuiu^R8E8>{hty0IGXryHyBe!8(#GtZ$=GaT4hjd#}p'
    ')pyq!DtFfjIwUZkz<dJp3Ct%jpH$;#x<N^TDhaB9!jaJx5KtZ~H3DU^x<;TpR%!%FW3fgF8YO6ypizQG2^uA6l%P>kjjx9!D3+jD'
    'vYle_^^gpe*F$ntTn`DT{(O0kikfb!##awYlwCc@QE~O4sT#itCqw16gr;hIEg?t6wS)|n*AfD%UrT7J##c@XlwUn)s>W9cnyT^J'
    'Zknp`^@65q{KR!rHGbkcL*?~?Cc0FLqU$IXn5e)+1tuymQGtmHOjKZ^0uvROs8r*tDwS${Ri!{VFLjikOUzOQmMXARfu#y8RbZ)7'
    'jjyVtD7vcBtQzn81FAoz*Q^>}1t?K=6`)x)z6#K+8b9@zq4FucX4UxlmkgCpa^<La>M=v*Q+my+@pF02s_}a{B9#4<_(_=zl~2k<'
    'sCH!iDnPSp{LEg8qG$F3sy`dktQ!ACPKL^-VVYIry?wK4{P#H-D*rwwN5z|kGE~0%CZPJ;Zkku)=a8DCQFAnEjz-PVsChMhDyexj'
    'ek!Rs8Z}3w=GFKarRLT68KvfE)Vvx$vD6&Jnxj~AG-{4U&8zYAOU+TGIjS^AmFB3@995d5N^?}nQSt7S43+OrX^tw*tMQvunxj#R'
    'YJB~y1sb(Ll@_Sdg34(D^DU^37S;IrS&M3X*Q-Tb0ivWuHGT%NMO*=*?8y2xGEf?e*=+&4Env3=?6$!3Etx}FGKaKe4r$38(vmr('
    'C38s2YW!?r%WC{=Vasa#Y+*~Ll9tu@{z}Vg{I_MGq(J#|hb^n|bBCbp$ok{~N@MZgowcmS&mFd8?QdC){|c>THU2BKmeu&L(5iHX'
    'Dz2;Ix+<=#(hI8ef+`-YQvFq`ze>GVsqiWlUZujTRCtP_Clmv!KcQHq!mHKzT}f3OS*^xTC|2=j6@OOoXO-%&QvFrxy%iPS3a(qh'
    'bt|}TMTNJ5-Bwh1D=NHIHNFZCN?K9<t*Cxbc4WQYL0PO`@1QgmU(Id>*R5c;73{Wx-Bwh8t7?3uyHz#5(%qWQ(3;NBn$FOg&d{39'
    '(3;NBn$FOg&d{39(3;NBnmq|9X-(H?P1gWrN7nlUD2vtm1SpNgJBHSDjn;IH)^v^5bdA<@jn;IH*6b}>v$tr?-eLzlzXP7%0nhJ%'
    '=Xb#KJK*^p@ca(d_>K{%jOF#P1N8t3M@AI@%41~(fU;P<0zhdju7Dk=fE}oS9jJgEsDK@)fE}oS9jJgEs`0&^Hq=8K>Y)ww(1v<w'
    'Lp`*i9@<b3ZK#Jf)I%Hg_MoH<wbF)K0fi%@>Hy`jvN}LntX>_UG!|D!8>*uX)zOCPXhU_hp*q@79c`$NHdIF&s-q1%?>6kbzf`+c'
    '8Lr4x0t%b1pkGRGi7H_wD^OC#!g*Gj!dC4|wbeJ}x~YcJb4g>(8uKI5wJP16q(1mkZ7mLKYD0=@&#;D<JT!nRU#eZ5Y|P$NQJ^GD'
    '>7sCCc0nX$)Yt&ZV)^@?n$=<@%47MSvZ)p;P>5wCbwd~hk}uV+38X!wsUbzR9c{MR%~9)WxYt@kL5HTM)S+L>FI-l`ecz@u+g9Pj'
    '=GDgRcFUJ)R{_F(--ZkYKGPqO@tLposU@0fDE*mfEaNj@`@^>&8nd4n_-tyZWPG-2k)L&_qc7F2EQCJM5K!)yY*U`2aMt1C!Iuj6'
    'q`x6)`ci&LH9Sk4E*}B4sBzYiqZ&&M&DvJ;`wtD_{ThvJ@lsp7)D|zb#Y=7RQd_*#7B98MOKtH|+nReCvv+;8#aW<ATb$Jv_khBY'
    'k$XUStaJ}3#3J{!#XW6tL0eqV78kU|1#NLbTU^i<7qrC%ZE-<cT+kL5w8aH&aY0*L&=wc8L-%&*-VWW{p?f>DZCC5;sqSgRZimwC'
    'YWw#TRq|L}_ja}YdnJ6rB8|nmw?pZ6^pJMw-VUYPp=~?VY=@fdsP}fo_0}Xsm3CBrj;bxflNKQsyPzE|Xou46YF$4SDB~s8y<KhJ'
    'A3jc$$LcO<SKIfeDB~seL_0ju4&B=oYe)L~l1e*VkfV@8a8Elt(QZ3Wl<&Ste|vlSM0@<w9>285FYWP5d;HQKzqH3M?eR-{{L&u3'
    'w5Myd$35+FPka2*9>285FYWP5d;HQK-P@ykdvtG)?(NaNJ-W9?_x9-C9^KocdwX<mkM8Z!y*;|ONB8#V-X7gMpmc}Y1ejkI?oiv?'
    'SF+yIp*9azvUBNB+v!)b-`)X-big4Ua7YJMk`AmS9dJ(v{L%r3bU^nGbPZ7YGh-Kk@>uB!P>5yXW;0j=s1_^S(*gH%s1|Ri4E_XV'
    '|E_jLzNr=~P#Vjx&xduTsfO}(rG{#*Yii0+&1X$16Y-?efk~$Wov#DEt^+RbfXh4J$PPHN1J3GzvpV9Xj`*cxZU0coyxS4?bgW%7'
    'u4LZrh?hFzrH**1BYx>fx9Ny`I?`=A;-!vsn~pfEBhKoGmpbB}j`*b`4(W(PI^vLyc%mapcdXq-4E?34(h=Qrl=qh`7Af74HLfGN'
    'cVvz0hzmO6f{wVLBQEHO3p#G+g1EnQVqNKkLpq^!CzS3)pXfxN=!EW_P`VS^c4F=5gtnb(t3?>yk`m=>2dL5s-9dS*bO9*DA{TVR'
    '1)X5N6U=vF#_Yt5*@+dX6KhT<R+&!d*9rYPp<gHT>x^QZQLHnHbw;tysM48g?2Ja8sm9JI)|qPTjDDTbuQU2}M!(J|))|dDqe^E~'
    '>5M9!QKd7?cV_MHj1HYy`#YmbXV(7CXw(^vI-^nN?KFyOY)2H^5yf^yu^mxtM`~<GYHUZ;+!6hDM6n&wXh$^K5sh}N7H@v6L@3t?'
    'RM`>5Kp__Cw<G%Ph<-bw-;Qv-BV6wY*E_;>7uf9ryIo+n3+#4*!7kK87x?T#J#>NHF4RL8xb6biUEsP4Tz7%%F0k7LKD)qY7x?S~'
    'pIzXy3w(Bg&o0~X8GCmp*xd<scY@uWV0R~&*a;?ff{C4AVy9~H=DD!??gSH{^vq&jc7m6k;AJOx*$G~Df|s3OVrO#SncR0K_npao'
    'XL8?}+;=AToymP?a^IQUcP87N$#!S5-I;86Cfl9KcIWM~jdkxzwq4nGbY<Vsl{vC2lVev{>IzFaN@wBl+1G{)g})CEpAgMZz4LXY'
    '^L3?eyHcrLsm-o1-<28zRl348D8#a*BwOAax-v(CYDX3tbw#7DOqHPQ-_>VKP#TN(9bMUXbY&Xt%KX_CPjtl-UGYR$JkgcT&=rSt'
    '!xP=my&L<7Zn&Tu`-g6Lq8py*h9|n=iEilLjegw?7j&avcf%9i=-1tFNH-kP4Nr8#1>JB#H+1iY?%mM68%lRWzi#X%x}jz_b`#yu'
    'wj0`ZL)&g>+YN2IZKrKq{oPTzJJsKv>hF#Vx}$q{l<tnw-BG$bN_VIFyHow$aY1)<?~c;l(Y8C<f-2on8WduY?%h$kJ4$!27H<g;'
    'UB5fJgR-AlcL6Ak#oBg9+wN%F9c{a#ZFjWofto!~r3b3?K$RY-(gRg`ph^!^>47ReP^AZ|^kDt#fkvQ84>SUWSfo)8H0psyJ<zBJ'
    'T=#(M9&p_Qu6w|B54i3L*FC9@p7h9`)Jji!WKT5eiAFuqs3#irM2DXA$eyUulOEX<je61}d!krRH0p^eJ<*{jI`l+`p6Jk%TIor3'
    '^hBecXw(ypdZJNJH0rsXMscs}g<`#6z8B2*g85!B-wWn@!F(^6?*;R{V7?d3_k#Ie)JiXO=!Fiw(4iMP^g@ST=+FzUd%<-txb6kl'
    'z2LeRT=#<OUEq2bxZVY>cY*6&;CdH$*@fIe>F<k~*aaqbfr(vUVwdu{?QmUj7aR#ne?!dKE^xLBob3W<yTH<}@Ukns><TZt!ppAk'
    'vMapoieGkRZ?P+!fhxPg*{*Q5E1c~LXS>4LuJE!eyzB}uyTZ$^@Uk1c>;^Bp!OL#&vKzeY1~0pj`)*{r8`<tgw!4w-Ze+U~4%v;|'
    'cO&=R$bC0*-)+0x<I33`CU%F3-C<&PnAjaAc87`GamemCWOrEF9hP>7rQKm^cUamTmUf4i-Qi_-c-b9Zc88bU;iY%&Zv&I;-}SEj'
    'ZD5l9yWY&Ly_s8kvoiN)E$$7wy<xXE?DmG;-b_fnnUH$3KJ;cq=*=3?yY^Rv8B0m;YVp3x@TXV3>H45bZxjQCSfpQXb}yjXk%hLs'
    '(Y811G${Lb^$Gx`v3L*Ln>}oA_CUSa_4LmCQgdti+k->0zk*3Cpf_tyZyeGGPxQePebBuR6ImZz(1(ev51#0QC;H%tK6s)Jy7yr&'
    '=z|OTFc<W}6MdKq`rwd0IHV5_>4PWw;DSE5pbxtDLH9oB-Up@opkE*MuzgUo4|~`?Xxj&E`=D)~?X-=nzb{JnMd`j&e_yJ<FD~ed'
    '?tM|ZFG}}C>Aoo4m+J3J_4maEebK!yO7}(EzG&MQZ9$d3C=Cj+NcX-d-4~_%(!KklJ1F~^br*orSgdVdv<;~CEv@v|_eJTxDBTZj'
    '`=M<=H0p;&{m`f%8ude?erVJWjryTcKQ!uxM*YyJA8Tqq6a!WIp%^H{BE|ZlSU(i&hhqI;z8}o@gZX|i-w)>d!+d|3?@#6Qr+@aR'
    'j{4I-`=eNY6zh*-{ZXtxs`RIS_D7@s^w0h%)}Q{_AN~5HUw;(qk4F7br9Z0lN0t7l(w{o&Pv!JSvHmF5AI18kSpV%5i@V|g^c#SF'
    '1JGdrIt)OE0q8IQ9R{Go0CX6D4g=6(06GjnhXLp?fI1q0Dg#hu0ICc?l>w+S096LS`~a9A0P_Q2egMo5fcZUOeh--61LpUD`8{BM'
    '518KrmiB<9JzxTqo=eQj9`LdUyzBuldoZ)_fm=c8Z-^P(0|xhi!9B{qL=Jx@vIh+A31@r4*`9E=C!FmGXM4igo^ZA&ob8FT_GH(y'
    'Cwzh`d&1|Q@VO^^?g^iJ!sniFwkMqJ31@r4*`9E=7o6<{XM4ffUU0S-ob3f?d%@XWaJCn`>;)5h!NguLu@_A21rvMWti9l6FL>Dt'
    'UiN~Qy|&{euExD#X>VBC8<zHlrM+QkZ&=zJmiC6Fy>ZswIBRbh+#3e>hQYmIaBmpg8wU4=v%TSLZ#df<&i010z2R(Nah)N&&MFzm'
    'Rfhs4MJ!@)AW!}cWX>AMoHdY@WFTwDKvs)^JWC8pK$U@9*BHoCfuIBw{$2D`5-0&>N7h#$Py))2ER_Z&p!CT2+0cPJ8#<6D1_$zt'
    ';6SdU4CFe>K%Pw-$g^n!c|vL+&qNL6DX4*5jTy+*n1THL!$AK2VIa>#59A5xfvlnf@!%kyv>1d32jRg%cyJIN9E1l4;lV+8a1b6G'
    'ga-%V!9hIBF$hP35>RCjjvR!~KnW=PyU1st1e70H`V5qS(j#NP48kvi@XH|lG6=s6!Y_mH%OLzR2)_)%FN5&QAp9~2zYM}JgYe5>'
    '95NV(48|dYamZjCG8h*OW~LpCCk8Xq4#pvanP~^(5KuB0PYk9@fx?lIUqD%`?hsHOD?I^9V{u0r%rnS?=`VwM26-^<8H{@d<B-8T'
    'b2%8l4Ca~3!MJBI&s+}1OM~&!VEi(ezqc5Sdj|9O7K8E9;O)E=uYW`6L__e|5PUWSpAErhL-5%Ud^QB14Z&wa@YxW2HUysyp)U=='
    'b)aMjt{Z~0K;g*9S)e>tIt!G>VuuXDAwzJ;5F9cDhYZ0XLvY9t95Mul48b8oaL5oGG6aVV!68F%$PgSd1cwa86GQRDP&_e|E09CE'
    '0y&iHC_}k&G88Wj#Y;n3)rPXF4aH|ean?}0G!#z^r4xY?Q2HBUhkz1Leq`wvPyz}^M%ST12`D?VejNprfbt{Dy#*)%rANm1CWdlv'
    'Vkp<PhjKN0D6`v8X1Aeq+M)E;q14JyYGo+C9*VDr;?JS@^UFog3LimE3Y0`BdvjT(j*=4PP7b`3DC{j7zg#-G9?RaFR;i<;h6*nQ'
    '_k6kZOK=t_99dJdF^|<z7R&VuFPQ-4u`Jv0Itox4%ik)Ws+ktnmuv4oOHo=?U#{(lnwmAFC->#rj;NBNW;x3KU8t%r*ZEAV>dW<d'
    'PwVI_F}szo#C&F`WU!6`6HQ-<IZI<POQ7T{aP}2g`U<>!1tz{i?q7+sZTw1{ZH|g;1B$X8Mn4-yKO06r8%EC>#<kyJbg*Gu`yEC<'
    '8%94HM$a0?+Bl33HjK4#82xM*YvVAw+c3HtD9tGDXP`V*b}&$gMLi3Y#p+!Ol*h`x1WIFZw;9Hrv|;p~Vcba@Mz<NpTsMr~GmN=z'
    '7@cSsooE=HXc(Pn7@cSsooE;<<yYxTU!^a7mEQAJde2wsJzu4AzDlit!jVzsfU;P<jzD>=tSV3%i#y6!=_p^NqkNT)@>P1saHh)P'
    'RNQbXZaB3voYj6ftNm~)XE?Pooaz|PtT>$N7|!1#3}-q7C7{Z1DhHH+@*~SS0wtjI$k>s?apZ9Jsl(Z)4rj(3&Qv*^IdV9@9*(bv'
    '<Llx0dIb87K)(^_Hv;`epwS4r+XxgJL3bO0ek15^BT#b$YK}n75vU1DMxY-kkClpn(pap~2s9dj4kMWLN1)0GX8jRpG=f=w1d5G7'
    'u@NXXVmrm+PP7mD?Sp>%px-{|w-5EV5B0YX+U|pz`=H-GD7FuZ?So?ba0PiEGy)}{%04ItN<it6v3~oY-#&1?4_xm9*ZaWrzOcJ5'
    '?CuM@`@-(NFt{((u`hh?OLgoEyZcfd`@;3UaJ?^F?+e%a!Zj$_7j{8uEar1x_}mvh_l3`W;d9^Z_>8@~AMEZ2yZgcJez3bAOzZ~}'
    '`@zJ1FtH!^E%qaKPy$NNGiG8xnAi^{_JfK2$bEmZ-JfjtC)@qWc7L+npKSLh+x^LQf3n@5Y(eR7kMrA~{Prim{mF0t?edGY9Z7y8'
    '$!{cA4@PqJU?h|HNM`Sm@G_EnStGfZHInW&lI}K=+8jwWj->uZ!u3e%2$X;-BjFm9fWnc{-LjF)-k=1O{k!@k4oX1zk>y+tN<it6'
    '@%4g{TrU{O1V56QeI)J~iF-!ko{_j`Bz<BeUOIsJ`T%zN2QXhBz<hlGyZHl{uMa4>P9l^~)S&S1qKO)m$I6Ksl*Zy+>jBKy2QXhB'
    'z<hlG^YsDjVGm&1K9C*zf$Z21WXFCWJN5(Fu^$L8pyWVU0+q3xvjbu2KzKP2CJto(ejxkz1KGbHNbaNPA*1Laqv#W(*s+hIYm8#Y'
    'K8hYPiXJkG9x{qPF^V;O6kTH!YxpR7$SBtEQFN41bQDlBiXH+Av8Zc|qHBP%BkO$vl*h`>07_$Vy^mtYK8ore#g2Uxy<il*U=+Pz'
    '6un>+y<il*U=-`hL3D<L=miJS3l75N2jT03a55-42w#KpSm|<58jI`wAnN@f>ir<<{U9oQG@c)g=SQ<{j%M8)O+AdJ0!HKc(Rh9|'
    'o*&J+Ihu8IH1#l=3K)&&N8|F*xEz##Dx>i{C;^2dqY4<!lO&_@JSYKWKc!v)pahg28T)!Pz8;OQN8{_!_<A(HJ{YABM(Kl5>|hi-'
    '7{v}ov4c_UU=%wT#STWXgHh~Y=E#H550ro^2csV-0fi$Y{SHRIgW>vMxIP%J4~FZ5;rd{>K7_7u2=l}t^pHd7A%`$e970DqgpP7Z'
    'nL}!<66HMvlpI120j05c-8_VjatJ--5PHZVtec0>Q4VEhIFy;;P-cchnHdgcW;m4GLCK*o0m@=^UO;6mXX#LQIkaRV{Q5)T<<OFs'
    'ki?<P6NfTS911UEsJJmy+!*@j80LvFbki}+6Jw~<F;wapDs>FiIEHy*47E9id14HeI)-^-40St(N(Cijs7+9aMb$WlY8*p11!e!P'
    '-akQUEUw})RPh+9cnnoMhAJLI6^~&O7>k-?QFAP+j762Ps4^B+#-hqtR2hpZV^L)+s*FXIv2@e1Xaq{eq7f*>B8|qP(O9@13)f@e'
    'dMsRzh3m0!Jr=GHqkkSo$2^RVc^G}-Fgn9w^n$~veo%54y#SQP;;wiYUGXrw;$if`!|}`E_~mf?ayWiD9KRfnwuhq_C;?RtN58|-'
    '?{J=dJ)EinC7|?Y#=0Ml?uVoM;pl!iN*@6)N5IPw@Nxva904y!z{?SM{s^u_9RX*c1XMW!&W?byBjD@^m^cC^j(~|HVB!dvI1-m1'
    '$&_#;o<9=LAIX$(Bo%NZ6>uaKaAcW7;Os~|4@!S#y#5_Y1ssXzk7UI=k_tGAN#H0ZfuooNj$#rxib>!o@&hGDku4~T)pG~sv62Z;'
    '8OwP&in-t@csYu>;3y`6qu}LeJbyHvKN`;;jpvWX^GD<PqwzH;{SC2`kH*PI<K&~Meo*>TVwWF{%a6w8N8|FNarx17_G4h;7??N)'
    'CXRuLV_@PKm^g;&KZfc*29`kSZ;x3z29}P2rDI^?7??N)CXRuLV_@PKnD`pi|269UYt;MKsDQ8G`LE&fui@*j;bc(y8{(S&8a4ej'
    's`%Ji-8N-kaxPG_5@lb%&OShUEMFHsw)R&d`KM}+<y*tY@~z<#g^z$#a#VZ={8+v`d@NrcK9(;JADe&Vq?&yxv*Fm<Uza4=7le<k'
    '{dGzHWvydtcQL|mZxmH>l>hc3RzqbhT*FDySnh&m*_Shqt$o8cum0m|+Gd|oDN(Zs6?`5CpU2g7Z_2)4a~$7pJ`S#rgX`nq`Z%~g'
    '4z7=b>*HYeIM_W7c8@Ebgw4JLd>mXKS3EnCeck3bm_H8YkArzor9k0>KuIlDaD5zH9|zaR^S!0xi|-|8DIL$(mr4|xP33sLzH~fa'
    'Upk(zC>>vX1v&i8fbz3$48i01s@U<h@9j1PdNUO6&L`RDr;q2mNuZ=ajoIh6kLTM+DGDQJ_-0gk)+g|dqZ9Z#^a*_Ns6>_8zl*+j'
    'bOK*II)N`9oxrz>PT&jBCzOhX+)v=UUMCc}hi@@uD9b%*Dp2`#B2ZGG#_%QHG!}n>=!7EorjWylsCgo4p2#;nPej`j(e^~Xw0a_6'
    '@jQ{QZk@<iw@&0st0(dm&lCA>=ZQGvM84{GB4718kuPf%sIj3^JF@PO6Zxj+iG0)ZM85c!q5P+0DE{i!i8$*-oHdT`B94RWad17Z'
    '=+NQDa)#>6kAwMfd^2$z-%K0_^W$KC9A8iz#}^dG!TdPBr#KEB#-YPFbQp&Y<6wRq-&!08^W$KC9L$e{`Ef8m4(7+f{7H1MlVJWN'
    'm_G@2Pr}zH(X&n>_mk*SC-HUDlj^zGP`yiml9T9CCy~)fWOOnaolHh2lhMg!bTS#8j3-W}8c!zMlgajEvOSq>Pv*;ZpyXtjI2k5D'
    '>5;LvC&R?aFmVd~`V>0!DRk&l=+LLop--VhpF)Q|g`Rv0J^2*A!g@-PU)G^dp(lfqQ|QU3(34N0C!b1wr;^{P<aa9hol1VElHaL('
    'bMI8Xxpykx+&dK}PKAk6Vd7MnIF&Eyfs#{U=~P$(rANl!&N~&BPKBlM^w#mz!+7dpJiT>1)iIuKI-YJio?01C{~S;M98bp_PvwlK'
    'M~<gQj;BYCr$>(Gd$i;E9&LtdRh6NrV~(d|j^}%{<EgRn)Yy1x>@=p|)0lowWBNUf>Gw2t8mBP}pT;bF8nf_e#S>D2&IVBBwAy5x'
    'wTT8$7R&Z=*%u-~wOBYZ%vqp3mhCqKOQ15AD|Q<5HK=kLI~!0MOV!Mt`AQ2uL#?v!KBhu6omRUyAAVhuoL0Lx-`Fhdy-#B<KaIJ3'
    '0{ff^>~kitmzls`W&&zXK+OrLIRP~%pymYBoPe4WP;&xmf+`bG6I90XJ<tSpJrhu60;+&26Ho<|#$r__pvnYPnSd%2P-OzDoDTD+'
    '!~E$me>%*c4)dqO{OK@%I?SIA^QXi7=`atfoDTD#ELN{0P%T!}5vYvi8l8?tr=t<5aylA;(pap~>1cF18l8?tr=!v7Xf%<l2NSt^'
    'Fp;X7NL5Yb>cK>=9!x~{iReBN-6x{^M0B5s?h{dZB1%t0>4_)}s!Zg{!bGZSB3BkBqTfXHn}~j(^f$yBO+=%KXfzRxCZf?qG&%#W'
    '&w%SQ;Q9=>J_D}Lfa^2h`V6=}1Fp}2>oef`47dhW&Y*HYWi03V47ff6uFrsLQ2JA1uFrt$GvN9RxIP1}&w%SQ*-f0u6`nJhrOsrQ'
    'I+N+?O!gLM7QBRup_Mb)O`OT~o->({&SY<KCf9q;tX=a6*M$>NawgY;&SY-^N{_5D7;Z*X&MX)Vw=J5^EEr7kpP9ezrm-=P#S_w*'
    ')%>z_V`KhP;(6&TX7;nVhIAGa{8>!!XEDK_#RPvA6Z~1F>jF(@F{Piy6{WM7+0SBTKZ`3$XBB*g8$Y7tEUq@4#mo*$k1YHdcsZ-|'
    'XZRIomHy0sX5r5ir5V+@Zpx30XZ^DZuAB0o8BhLa<K46I?%8<vY`l9m-aQ-do{e|U#=B?Z-LvuT*?9Nt8oNoh69y$`<Lk5WH7Gl>'
    '?qpCJi=BKnPCgqapI!V7c(!{vyZAfIBtMtD6(x;%EcX1_c>ZiWe>R>!2OZ9V`Ey|Y9GE``=Ffrob71})xIU-&s(W~9wE>izgAV7Q'
    '11LMP&O9iOmCS?ESj_x6Fn<orp9Ayf!2CJIcjLpewoT`t!#U`14mzBJ4(DvAL+u?lN&Yiy@0bWr{U?*?OOxnJljuv6=u4C6OOxnJ'
    'ljuv6=u4C6OOxnJljuv6=u49djk2o;pkxv~YZ5&RlpR^`QlK;zcd1EqsY!IHNpz`6g__xwlSze|mHf<Vf6ts<Ihj<b*_0m{cehD&'
    'w@GxjNp!c#C^i|5CZo}0G@6V?lhJ508cjx{$*3~9sH&z=W1wU*icLl_P<CWpBTybIH3FrvSfj~kG#QO1qtRqEnv6!1(P(l}f8j4='
    'nkJ*zWE7i>Vv|v9@^*^V>aUXj%v$|ba?Wb+cxjfR#&hYI=dyC0OaDBV{&_C_^IZDpx%AI->7VD;>MtE{)43ItoXe_qE}iyV`X?y-'
    'yQqJH@>tnFL1`@RpXbs)&!vB!OaDBV{uxk8TkFh9DT@2&x%AI->7VD)KhLFqPC=C^=r9Exrl7+VbeMt;Q))T{yEHX`k|}631&u)A'
    '$Vinbtbd?n3W|ZUSY0tt9xD|CrLkDCDJV7t#ipRx6cn3+VpCZErl8*x^qYcyQ_ye9cKXHZ-xSurfb!oSm_Lub;d$&0&tq?R9@k&a'
    'W2bl?JH_+ZDW1pPus~T;Yyc(aas8!0SsQEsWk=Tclm*IKRs*PZWN~e#Kv@H80Od!PS3C=pwX+6Ld1NKqr=G{o^gOQHoX0-(Joc&Q'
    'u}?jZed>8-_io6Ktaa~({K#7OZm1oZsTpn@COK-|qAA=aO=J0Mj=~?-g#7ZCi)4R86=K<o{jvvvk{pFtxZ8PNZI|4X?UL)LQbS?S'
    '+?4H^>nK$2RIU?E<%+~qd^Q!IO~q$Z@!3>-HWi;u#b;CT*;IT6N~YqosrU?39$Cq*6HTr8rIKB(n2HOg;)1ETU@9({iVLRVf~mM*'
    'DlV9c3#Q_NskmS&E|`kaQ&D;<N>4@GY3Mf%{idPcH1wN>e$&uz8v0E`ziH?<4gEmLH1wN>exU5gdY_m^p8(a4Ec(PW`UI#vGIzl='
    'Trdq6Ov44!aKSWOFbx+>!v)iD!8BYj4Hrzq1=DcBG<v}_dciatG7X1J!y(h?1=F_kOWX^lGqX=;mo=RUemWEUbSC)eOz_j0;HNXe'
    'PiKOkUd#-cdqBx_c3{()^`|qzgTlXyCU{UDD<^nR8jC0R=}hp`nc$~0!B1y`pUwn7oe6$=se7JZp?lD8I`jN==K1N&^V6B<r!&vb'
    'K+PHGHv|1<px+Gin}L2a&~HXD4`#IqN@k$#473G>BO^6uuyX??Gf*0o#p+6f@>r=fD2>HR&p_!JC_MwEXQ1>9l%9doGf;X4O3z>)'
    'Hv`>gp!*DTpMmZ(w$nY{$IW0LH-mlLjAE*+<cehv0oVG=OzthsWJ;LHJ&l>HIWt*vX0qnYWX+k$Dl?N+W+to5OjenhtTLdaKzW~-'
    '$s{ndwsz!>oXLtXlNDhmE5c0HfSIfTGg$*>vIfj#4VcLqFq1W4CTqY<)_|Gx`I+?jne_RYboN<jGz*Ppq0uZfnuSKQ&}bGK%|fGD'
    'Xfz9rK*=oD_gSp(pz_FEu~{fK3&m!k*en#Ag<`W%Y!-^mLa|vWHVegOq1Y@Go5iX<i&c9TYR*E<S*SUSReRQU+QzH)Y<Bvy+3C;b'
    '3C!8-`)9N7pUtzcvv~q@Hct@E=4rdxJo`GECopI8%;jvZ0?e*GPn18o5~1v8#?Knf=2@fJJeN0{o&Ic|$DGacn6r7hXm&Lp^BTin'
    '&Nj{Fd7|0u*k`jxpIv)HUSpE~yZl{jjY)pi`McP{iyuSo`P<jRFUV0~qA_#99G>}_gMM?+Zw}9V%|XpMs5yrxz~=A-*c{ZHgPL=A'
    '9&8TJgUvzBIXoRU2W{t|?Hsh7gPL<ta}Ljn%|X98=r;%b=Ahpk^qYfzbI@-N`pv1m;V@GyM``Zil1|7y)^ASj?Rkx1-Av}7=J{NA'
    'J0CUAN6qt5?0o9)d{jA~8atmWZRf-F`P?x&KdvKDaz0PHp3l>+pzO%{)ih8Vi<v(k=Ff-u^I`scm_MJ&xqwOa0w&c9m{c!dQoVpl'
    '^#Uf<3wToW0-hATfG0&SU{bw+Y4if_6<kp88T=wjF5oHB3wVkYlpR^0MnP$;#%{KFT)<PL7cc={z|40+!EPo0cQtk^`I*)FQuxcg'
    '#<}#Kxwv&MZk<c-nTvPl(rxC_ZRX<Sx%8L0^q0AGl)3nNE<I!}J!CFDWG+2qF3+3J<$2S&^pLrACugzP*K>K^bS^HRi_7QY^0~Nt'
    'F8yUL{bep4<wAPMg{X2Ns$7T;7t%v6g!v2UAs5m^E`;j~xgrlrE~LL)NPhukN7g$ED2vrQ3Mh@m*U~RUhYMl;LYTi0<}ZZ#3+XQx'
    'a%KHOuB^|a_spaB%%k_rqxa0C_spaB%%k_rqxa0C_spaB%%k_rV<!ws=Fykt(U(Bkk@Zdl%3}3S1WIG^&U7AqX&!xP9(`#ZeQ6$j'
    'X&!xP9(`#ZyViN^TIaEAy@*=5h+4UbTDgc?xrkc1h+4UbTDge3UZ66T*U?4P(M8k|DEzyqazJ^ktQ=4lt5*&vjm4F75tVZhm2(l5'
    'a}kwu5tVZhm2(l5a}kwu5%;9#Q%Ccuqxsa)eClXEbu^zknok|gr;g@RNAtN71xn^qWAmx8`P3LF{JW^CKzXdJDo_@yR~0CY#Z@(*'
    's+vz#&8Mp7Q&sb+s`*sae5z_bRW+Zgnom{D=UUKwt_3Y9{~kR_Wm>@7V;7WfoG)Vazu{lNmkk#1H~b6uLcs#w9kzgXhb`c}I16|a'
    '&H~<jvw-*0F5r7TpahiuhWH)cpahg1S$}5^C;{b1mTwmTC7|@k_^s;;c<cHC-uAtK_j@nkjou6R0@wn+0Jebd^(^2EJqvjA&H~;_'
    '@O9opP@-%{^mV>8@O9o$@^!v|^7T@cpu^Wo=7UC{aAb|^FxP>ySk7)zi<Kyk<!|C>sKp8tV$r*OKzXcu3j!#O#c%WZI&VSvI&bj!'
    'I`2fdm^YhT9CKES74JE@7+yfh#jtcSyj%<u7nA$NWP36BUCi6bF6Nyi7n9LK>U|;gzL0ufNWCwl-WO8u3#s>o)bv8$b+wQRU&y<z'
    '7E<pEdDqoKs(&HX4@%E0u6Ixtt5-NEkCinIN@H=QF66!Z3#r?MyqA9=RlJb*@-L)r7xJC0g;eoEzO%KEnqEjvFXT-l-=M<3L4|*V'
    '3jYRf{RaL7g(D-kg0fiMyP!N)IvEsVk*`5{taLdjjm1^`4XXGX)a@lOaS2RZ0uz_e>n@?!UBcU0E`hU4cvs6Md}9Ta{*?Hgu%Ikf'
    'X9ASRN+v*QEPe~@CGc_yyj(&rxCE9irMq29ce|ACb}8>|x)dfr$))fDDq}fIm%_`XFmWllU&?!)FQxNcO6R+jY`=*MzKILIi3`4o'
    '3%-d9zDc&<q*g%Lk@fsQAr@r|%3}50L3ylX0+hyL7km>Jd=nRZb30yQ7hHx5F2e<v;eyLx0+d_^FPFi@W#oPt*<MC|m!b4!D18}9'
    'Uq(jXLg{az^tVv@Th#Qo$mm;m_gmxuN`Fe65h#n*^8@9vGFwm@i`D!VYJLkfzlDC^CiicX`?tyc+hqG~6a!^P)^i7iSd=>`i`8=n'
    '<*_n%P#TMK|2DaQo7}%m?w2#$T+VEBIn&JL%rBR-L%EzC%H>QmmovXy&ct##Gs@+BGvjim5>NuFT+WOFN<jIM<-`I?K<Sb3F644{'
    'A(u1TT+TFeIrGcqOdgjrd3*=geFxWlhi>{ET=$)lrLedE4$}oF{JUtn0OhfAx&Vb(<Uvp#D?JEGW3lVLgX_LSxA_hpyn_CD1^x31'
    '`sWoe0ZOib7f>0?S-JvVu7HUv$o&eky@GCf1>N)t^1G6%x{|88lB&9rs=AWOxsrXrmDJId>;tZ(s;*=oa3wW%B{g;>H3mwqq^dx9'
    'tgItY8jGvrN+$m+sg*04{I8^Pu4MARk~+GQI=Yex{<~Dwcd4rH;-2r~m+#^bQ1V^;0?K2hdq5!;c?p!qN@s!6SX@WnrH;N!<y=L!'
    'SCQ>i^pLB_{VH<5s(dSCQ;wqdBwj@hpyVoY0Hv`whpWipDr)5_GP;^xa5cT)YI?!dWCTjCCO=RXt7i)eu_$*?8Oxctn%uAE-KSUc'
    'w$rQW8duXbt}dAfzyE4@xw_;fP;m_%<r+H5HFT6~=qT5)PG7@1eGT2_8v4sMbd+o8A=l7DuHl`c*U&XU38-=nJp`11(j(*QzlQ3+'
    'mI}C*3b>XExE8-$i$ku(6W3DjpyXQW9TZ}bLqK_~^b07B#kF!RwQ?<<xRzSEj#{~nTDgu|xsKdH$#pOR%3^h1KxHgv={k714koT6'
    '_v@&K>!^q8sE6yw{W|L5d+7c>bpIaNevkaVM@HYH-oM9LgOcx&11OEf`h5@mzK3GhQ^nU)#n)5C*HgvUQ>oW87hF%>Ue8=`Jym=?'
    'bHVl0^!3#A_0;tB)HEo$o+<{VvAAxpr*5xj)&4$eejhczkDA{{&F`b;_i-dB`9A&xg;=CJD36u8gVI>6`}fiP`{;fH`Q1Q%H_)YS'
    'Aln<r_6D-Op?rID(C-GEd;@PczJVM->F<lr`UWcQ26DKOZgV5u=0>{BjpP7IZX_d67OUq6%421=pb(342j#Jn2~Zi!dAX4_{6^OB'
    '8|hLv(xq;Mvm5DBKcL=!K)wHfdjA3S{sU_B2h`>dsLdbn4(}gOji3Zn`2p4VL;U$e{P{!t`9rk*A!_~*{eFmIKcxOZ;b%rVfYMm('
    '&mY3|5Ao-Z@aK>4=a2B`kH`U({D_P|S*)HPD36udg34H)`;W->M>y+8IO|7b`y-t7V-))_iv5`UeoRI`CWjw$)<33>eoW>3n6n0@'
    'zdhFI$EflXD&Qwnz)z@vpHKlmp#pwF1^k2x_z4y86Dk0d{)X7|KVb#>DSZAEK7R_IKZVbq!sk!n^QY(zN`FJlCn$}@eEt+ZZ{j>}'
    ';yiDnQg7lq?M>ux6W3{P;yw8{adi@u+{8)=%420lpfna=oxF*4^Cq&r3D4g|?l)86H&fv^Q{gvrx8-JX2PHSd1SrHJUO;6mXX$2m'
    'xfv#I=8F8yOusi%{Wp{QEhv2pO5cLEw~*g0WONHT+`?Idl3U0Dl*h`9Kxr)2_7=3g1#NFZ&0ERuR`R<QC*Ml8x03CxWP2;w-bz2a'
    'mHa@-t>gzvV{t~elF_Xwb}RYahFfpLt+(OU+i>e`<OfP_BU@02MY)5rSe*$_8OwRO4JK}5Cc2H8=r){u8&19rUT#O}+fn*<w7s3&'
    'ZztQ^$?tYDx}6+A$?aqWN@KCMx1;UtsCfrD+(8a^;MP0H=ngWvgN*JVqdUmx4p!eg$N`l8zWA)~fcZPf;b%DVXE^d_IPzyW@@M1#'
    'N`6L0pb(4l17)##wxB##<_;=jITJs_pFhK&Kf{qfgO{J9=Fd^{=jiuya{oEm{+#@NPDVc`ho5uSp!B!L`u!Zm{$K4W((oK^V`GZK'
    '4ADBQBMnU@3V(i^6ey|1@@G67!@p}NQ26V=B%u6R>F}_0hQc$K;i;LX9JNY+dsAZ#h39C(v{Xq^t8i$Fnx*OgPjP19Vadk-DbA%S'
    '{Pq%sM=p~BCAC=X%)-BGC{TE8I|(R1vu5GU{--#zX5q~Kr#Q1_jWv{=S+j6v|5Kb<xE#{-3po2l?XUL3Q_e|15re;g!C$~&fhu*B'
    '|CIE<U%>7!YJa_*y)&mo;jcxT0?OZUmht(E+FxOZ`x`Y>vipmWLl#SAZ~6sX-$_PylEa<ka3?w3Ne*{%)_3BGJ2~q+ambzIa3?w3'
    'Ne*|C!=2>tOZ@W7LY1(s3Mg{VFLBQ=aZiCNb(H^<^uJ%?tX~$Ygx^r2@W^vhKzT-)mws7f6#fJ#N2RlVS!5K7vFVri>@G68iyZDE'
    'hr7t(E^@ewv%ZUZxQnyCi|V+G9PT2AyU5`#a=42eeucAsg|mKzvwnqpepNgfo~86F{PHV0%CG1szrruS!Xdwg&tJpmui^98aQ5rs'
    'Trxs`4NJeKhy0oz@@rW7HN4ynFL%>J?uMniVd-uv?ryrq-7t7JUE^-}yt{alLs$$;l-J+g)Zg9kc{lZUH|*X+M)#1zJ>+l?Io!ip'
    '-@|#{gYNfmp7(H`_i&!~aGv*Yp7-K{d+8JR;)#3l#JyD2y>y0q@yoq*hI?_(y#@2(eHSIlYwTWX>|We+FEw^AUb>Hr?jwi$$l*S6'
    'xR0~GkMq0_m*2;E-p6^~$9dkzdEUo){sxEq28a9xhx`Ul{02|_rdDxH;qQn_l=p()&<lQpCw_wqehX*6g|pwn*>7R#x3Kiv;#|Vt'
    '%akbZ1;3>i{1%pe3opNem*2t5@8IQk@bWu&`5nCcuJ+rraW_NZw}(-&sYE$1zk`<)g{x12!Ahm!_ng`9IkVq$X20jme$Scxo-_MB'
    'XZCv(`#op&d(P|+DE0>w`vZ#o0mc4+Vt+ufKNRPZRpTEDmcqxrOOz}22Ne55!BVrp(jPgqKXPV&<jnranf;M7`y*%eN6zezc<GOv'
    '*&jKx`%&zE)|LCw?|$^VpPqa_>&pFTdq3;S{V07u>&pGLJ`vs!Qb&2ez8|IUr(fTX?)L|-vsh5&e*F0W%s)Uce*hgGK!*qDgAdTl'
    'A3&oA=;aTf*aP(P2a0UNdrnG}_s9oO>;Zb@1L*fak!?1SJ%G<1MB4|^_Cd6L5N#hs%?DBQLDYN@H6KLH2T}7uI?98n`5^i|h++?+'
    '*h47x5Q;s7Vh^FwLum968a;$Y524XRX!H>E{ty~HgeniA!=K>#PjLMw82l6S%b!@Q{zT{d6Ab>TnqMr*G)jMF?Qa+}-Twr;e}=O^'
    '!`Yu<;?Jz;e`c-vGyUbyF!AT&TmskW&#awGrr)1o>0x+z7+xNxzdVd1ABMAsaoxkrd=Jw@9)`1r;VeUiuLFu0e7Jb)S5`R>(|aC<'
    '-ABmi5i)v&j2<C}N6`Hda(ILs9wCQE$l(#r`Vr3a5zg~bT<|C^c$8lED0TEG4tbPXd6b#&QTo}VIOI_r@@T<)_71m4@ynwH^I5$='
    'N*{a_FFi&^kCD-1Wb_z0Jci33BZtSx;W2V}j2s^0tRLe%ALBg#f<yj-L;iv%{=yXW7ka^8=mmel6Mw-If58)fsr@~3xQ3dfDE7o('
    'Veqdo_*XdlE0f1x=?s6RGyE0K{t9P*g|ojFXBPhOIYlvNkHgvHaP~NyJq~A&GdVua3iLRfJq~A&!`b6-_IT}Yz_Uxn8LIuv^w7sk'
    'J{!}Mc^q~hXH|QGjGiE)C&=gtGJ1lHp1=i9kkJ!l^aL3_K}JuI(G#5YlX&7uJn<x+coI)M$u#;T>*kYq;z>O5B%XK@Pdr(iXVwdz'
    'ESRqZ=ASJ65}1Dy_dLm3{1h2IMMh7N(Nkpf6d65*%by~nr^x6jGJ1-Po+6{CIP0fz$kRCFX;zY_SsS0mJx{YXKFvh-H0#RKxaVoy'
    '^E7MY(|GA=*2br6Z^TUhH$%k=6f}C8_2_A8<!M~^G!y*ORL(Q#_YC?yL!W<!mFpR_eTJ3m8K%5v==#r~?K5cm3@g_&DE$m8*E0n#'
    ';SGl=D%OX<%QLJN&*0=|@WeCB`p@9&XYtFk_~ls~@+=N{7Kc2GL!PB$K8r)1#Uan)kY{novpD2g9P%vv^I1IcES`847d(dxp2G#t'
    'q5E^_{v5hLhwjhOrJh6g=g|E*bbk)rpF{WO(ET}j)^jNR97;cjwtp-3K;bl#zp<+;P*TJq7yONTFMnen_c!jgfYP55PotnLR-Z#a'
    'd8}NIKv}Hr9#9&KmHu0)bhzd4zeTp$PbpE*udzT$Jr;D&erAD^2(@n6kTf)FR-&YaioIcA;(yEg9f2iKc4Vv8)s~fT+RgsAoE*cK'
    '^g!Xr+Dw#gFdIO5EL%G&MXW#}mi~XWWq1HA`wgvfPvj`~S-3&m*z~`(m823LD$7y+Q!>=5MgCKQdH=WWtQ7sd<TL!fzq7mkd&y@l'
    '7S-6_xnuNq_S1jo9uX-0De-&_%3}4&5tPTu6&94m>a__<V{sk*y{w~fGSB0s=ke0>c<Fh(^gLdA9xpwQm!8K<&*LRfc4Xa4&*LRf'
    'I5P4QD36t10)<%QrRVX|^El*r9P)gfvy_Ve!!Q4bU;Yoj{2!k9KRf{nM@F6iWwE*^KzXe61SpHuJpoE%u?t?Ho4!CdeSvOTph_K;'
    '*Uw&{)4o8beS!Jx1^Vs_Tt9n(yWF7k_r+HMKv}FlyMgjp*=a#(ES|w$pzpp=PF>;k=`YZQUxc$4;p{~?dlAlFgryf@=|xz25td$L'
    'bpj<X!Wk&UqLmAj$4WjyS**?{D36tVg3?&b=Zo<9B7D9GpD$5WFHu!5QB?)1)KPi;^Cdd;OLXX$n1x@WHecfU=S$qv2c^F+z8(U~'
    'V)Z#0l*h_y1f{Wf-hGLF{ZcvM2F_lhZeND8m*MPXIC~k+UWTQYVd-U9dKs2prh|c!m*ET)Vo`Sk<*|}aP!_B63Cd$7pP)1r^Z7D-'
    'z6_r)!{<NX^B?f}5BU5CeEtIu{sYebfwTSrOQ7_p#7uy)Se*$_9xIsurLj2Me~|4z$@ZUQ`%kj{C)xg!{Qik2K>3knwxAG;JORpM'
    'B@>`5R%Zf~$4VwZX)I>qpD^(+dilTT<^Q5z|BIgdFZPZ9qSJzsf3ZgZ<*{;)0Lo(ZP76w7ac}(>-Sidax>uO%USX1Zh1u;DrnOg?'
    '$X+S;jls#UFrR_KPl@I;P#!DiGf;>{^VuuRXRk2pzrw8l3bXzzOmeR<$^9G8{~OQ$o38k8T>fwN%>Tx_pyc07YoI(<PHUhnR`)I_'
    'jl~`8-+1>`lztVZUq$IxQTkPseifx(Md?>j8Wes?q%<gxl}dv`EK>SalztWcUPZrGnZ*Btn*Tw~|DfN0(C<I!2TJ~fexN*7>IceV'
    'b^SnTELQ9_y3K2Jo7b2XUt_+0jZX9$v*K&?rPr9KU!zOC#?`IYm;gb^YfONkJXZE4P#TLTz}M(fuQ36>M$dX3US5Zn*Wu-Ln0Or~'
    'UWbX-$^CUYG$?r;CO}!N&IBlrl}v!rSj@!hF!4G}ybcp@;OjT=^&70kZ!mehK?i$-N$w5m;SHveH>i#`xFYxlYcVK!gS8lx$I5yD'
    'rLlNEdxP%w2J7@2RL-05@+Q2z2`_KL#G5ejCQQ6Z?r+i=K*^gh0m@=^CO~<tWCE1NVkX{%i8o>5O_+EKCf<UHw_xHe9P$>qzl96l'
    'f{C|q!CT}GO5P%OP#!CD2c@w%zqiQmzvTB{^7}9O{g;gXOAh}<O;GY*G6H3>dPbl;R%QfBV{u0RC8M|LZg11w-lm_uO$U3M4)!+p'
    'KHp}l1SM}XRf4iuy=Q^aSlp%FrY|jG)>y=>v4~k?5wpf3W{pM68jF}U7L|7x!~1v_F<pR?MNAi<5R0aZMNAiqm>d@|IWA)ISj6P9'
    '7)LI~k&Edzi*e*)9J!b~sEe63K*?fe4Nw-Vdk~by;vTXX4=zE!CFr*V{g$BL67*YweoN4A3HmKTKTxs+{XiiW>9+*^mY~rRG+M%R'
    'xD>^fqS#V2T8c(X(P$|efs&<Y1j=G{jX-HER^=T!!#i|_cjyf7&>7yLGrU7*c!#GV-r=t0J5)a?{q1q}zr!8IcjyJnIO}Dc^)k+S'
    '8E3tWvtGtoFXOD2(ZN8;GI9W=u{eiiob|hS;$1xPE>-+44tW=cyo*EL<vECVxo7$=E&!#!J+9Puxxe`?4p~m!E~jpnQ@6{h+vU{l'
    'aw>H>mAbslp(#RnZGytjjB0Z^wYi*bx|~W~PNl9uhZX3s0v%SM!wPg*fetIsVFk4bN>-o>D2>IctU!mAob^i1dL`$%lJi{2d9LI<'
    'SK^nIoEa$neX&DUa%QV=$SNGN3Wu!1A**o6Djc#3hpfUOt8fS?{LIK9t8mCFJh2K-tfG6bhU?XEy&A4p!}V&oUJci)@dPMY4fCKh'
    '7IVFZ&bNlnw}yS{8ussN=!$FDwXUH@u3`VahK{+0{rei8PFce~6_l)@V}jCHyiZ+2|6Ie9M{C%%u3>#xL#JJferwThEff4&b|`D9'
    '{<ZAf)}s4bb}wsj!CH1NYk8_=Ez><HS&IumX)NBWt))+_<vFCa>;u+Pw`=jzI#^l<OY2~19W1SbiFGis4kp&Y#5$N*2NR%V9ZZ1I'
    'Se)%TvRy~E>&SLJm9w78Sx>F3r&iWe9qXx%^;E}ts$)IXv7RYtJ@o)e&n&Kh^|*XJF5iHD8_;h9ifzEx8_;h9`fWhJ4d}N4{Wh?6'
    'Y(OzkdS<a(H=xl5G}=f;8_8%R8EqtojpVSA95#}}MsnCl4jah<l%7j`)*CtN{|^IW3$_'
)
_DB682_H2_RECORDS = None
_DB682_H2_FULL_ROW_GROUPS = None
_DB682_H2_ROW_MASK_TABLES = None

def _load_db682_h2_records():
    """Decode the frozen exact H2 language in compact 14-byte records.

    Each record is: little-endian uint16 C8-parent index, six edge IDs giving
    the complete edge-2 row in the program orientation, and six insertion
    positions (0..5) of edge 2 into the corresponding partner C8 rows.
    """
    if _DB682_H2_LANGUAGE_COUNT <= 0:
        raise AssertionError("v0.15 H2 language data were not frozen into this build.")
    raw = zlib.decompress(base64.b85decode(_DB682_H2_LANGUAGE_B85.encode("ascii")))
    record_size = 14
    if len(raw) != _DB682_H2_LANGUAGE_COUNT * record_size:
        raise AssertionError("v0.15 H2 language byte length mismatch.")
    if hashlib.sha256(raw).hexdigest() != _DB682_H2_LANGUAGE_RAW_SHA256:
        raise AssertionError("v0.15 H2 language SHA-256 mismatch.")
    out = []
    pos = 0
    expected = set(_DB682_H2_PARTNERS)
    for _ in range(_DB682_H2_LANGUAGE_COUNT):
        parent = int(raw[pos]) | (int(raw[pos + 1]) << 8)
        pos += 2
        order = tuple(int(x) for x in raw[pos:pos + 6]); pos += 6
        gaps = tuple(int(x) for x in raw[pos:pos + 6]); pos += 6
        if not (0 <= parent < _DB682_C8_LANGUAGE_COUNT):
            raise AssertionError("v0.15 H2 parent index out of range.")
        if set(order) != expected or len(order) != 6:
            raise AssertionError("v0.15 H2 edge-2 row is not a permutation of its six partners.")
        if any(g < 0 or g > 5 for g in gaps):
            raise AssertionError("v0.15 H2 insertion position out of range.")
        out.append((parent, order, gaps))
    if pos != len(raw) or len(out) != _DB682_H2_LANGUAGE_COUNT:
        raise AssertionError("v0.15 H2 language decode count mismatch.")
    if tuple(out) != tuple(sorted(out)):
        raise AssertionError("v0.15 H2 language records are not in canonical sorted order.")
    if len(set(out)) != len(out):
        raise AssertionError("v0.15 H2 language contains duplicate records.")
    return tuple(out)

def _db682_h2_records():
    global _DB682_H2_RECORDS
    if _DB682_H2_RECORDS is None:
        _DB682_H2_RECORDS = _load_db682_h2_records()
    return _DB682_H2_RECORDS

def _db682_h2_complete_rows(record):
    """Reconstruct one complete H2 selected restriction from one frozen record."""
    parent, order, gaps = record
    c8_rows = _db682_c8_language()[int(parent)]
    rows = {int(e): list(r) for e, r in zip(_DB682_C8_EDGE_ORDER, c8_rows)}
    for e, gap in zip(_DB682_H2_PARTNERS, gaps):
        rows[int(e)].insert(int(gap), _DB682_H2_EDGE)
    rows[_DB682_H2_EDGE] = list(order)
    return {int(e): tuple(rows[int(e)]) for e in _DB682_H2_SELECTED}

def _db682_h2_full_row_groups():
    """Group exact H2 members by their complete row, returning bit masks.

    This is the compact basis for exact subsequence-support masks.
    """
    global _DB682_H2_FULL_ROW_GROUPS
    if _DB682_H2_FULL_ROW_GROUPS is not None:
        return _DB682_H2_FULL_ROW_GROUPS
    groups = {int(e): {} for e in _DB682_H2_SELECTED}
    for i, record in enumerate(_db682_h2_records()):
        bit = 1 << i
        rows = _db682_h2_complete_rows(record)
        for e in _DB682_H2_SELECTED:
            row = tuple(rows[int(e)])
            groups[int(e)][row] = int(groups[int(e)].get(row, 0)) | bit
    all_mask = (1 << _DB682_H2_LANGUAGE_COUNT) - 1
    for e in _DB682_H2_SELECTED:
        union = 0
        for mask in groups[int(e)].values():
            union |= int(mask)
        if union != all_mask:
            raise AssertionError("v0.15 H2 complete-row groups do not cover the frozen language.")
    _DB682_H2_FULL_ROW_GROUPS = groups
    return _DB682_H2_FULL_ROW_GROUPS


def _db682_h2_row_mask_tables():
    """Precompute every exact ordered-partial-row support mask for H2.

    Each complete H2 row has length five or six, so there are only 326 or
    1,957 possible ordered subsequences. Enumerating these tables once replaces
    millions of production cache misses/scans over complete-row groups. The
    value for a key is exactly the union of frozen-language member bits whose
    complete row contains the key as a subsequence; a missing key has support 0.
    This is an implementation accelerator only and introduces no new pruning
    predicate.
    """
    global _DB682_H2_ROW_MASK_TABLES
    if _DB682_H2_ROW_MASK_TABLES is not None:
        return _DB682_H2_ROW_MASK_TABLES
    groups = _db682_h2_full_row_groups()
    tables = {}
    for e in _DB682_H2_SELECTED:
        e = int(e)
        full_groups = groups[e]
        universe = tuple(sorted(set().union(*(set(row) for row in full_groups))))
        table = {}
        for k in range(len(universe) + 1):
            for seq in permutations(universe, k):
                mask = 0
                for full_row, group_mask in full_groups.items():
                    if DB682FactorizedSearch._is_subsequence_tuple(seq, tuple(full_row)):
                        mask |= int(group_mask)
                table[tuple(seq)] = int(mask)
        tables[e] = table
    all_mask = (1 << _DB682_H2_LANGUAGE_COUNT) - 1
    for e in _DB682_H2_SELECTED:
        if tables[int(e)].get((), 0) != all_mask:
            raise AssertionError("v0.15 H2 empty-row support table is incomplete.")
    _DB682_H2_ROW_MASK_TABLES = tables
    return _DB682_H2_ROW_MASK_TABLES


@dataclass(frozen=True)
class Edge:
    id: int
    u: Vertex
    v: Vertex


@dataclass(frozen=True)
class SixCycle:
    """One simple 6-cycle with a fixed local traversal direction."""

    id: int
    vertices: Tuple[Vertex, ...]  # v0,...,v5
    edges: Tuple[int, ...]        # ei joins vi to v(i+1)


@dataclass(frozen=True)
class _CrossingNode:
    """Private internal crossing node; cannot collide with a user vertex label."""

    a: int
    b: int


@dataclass(frozen=True)
class _SubdivisionNode:
    """Private internal subdivision/block node."""

    eid: int
    left: Hashable
    right: Hashable


@dataclass
class SearchStats:
    recursive_calls: int = 0
    partial_planarity_tests: int = 0
    partial_nonplanar_prunes: int = 0
    c6_consistency_checks: int = 0
    c6_prunes: int = 0
    full_planarity_tests: int = 0
    backtracks: int = 0
    cache_hits: int = 0
    max_active_edges: int = 0
    max_modeled_crossings: int = 0

    # v0.8.1 search/implementation instrumentation.
    screening_states: int = 0
    screening_candidates: int = 0
    screening_survivors: int = 0
    lookahead_states: int = 0
    lookahead_dead_ends: int = 0
    lookahead_reused_screens: int = 0
    incremental_graph_updates: int = 0
    partial_graph_rebuilds: int = 0
    locked_prefix_tests: int = 0
    locked_prefix_prunes: int = 0

    # v0.9 exact C6-projection-domain / factorized-stage diagnostics.
    local_domain_planarity_tests: int = 0
    local_domain_planarity_prunes: int = 0
    local_domain_signatures: int = 0
    local_domain_seconds: float = 0.0
    domain_stage_states: int = 0
    domain_signatures_considered: int = 0
    domain_pruned_stage_assignments: int = 0
    factorized_core_slot_states: int = 0
    factorized_extra_choices: int = 0

    # v0.10 exact completed-restriction superdomain diagnostics.
    superdomain_tests: int = 0
    superdomain_prunes: int = 0
    superdomain_cache_hits: int = 0
    superdomain_cache_entries: int = 0
    superdomain_candidates_pruned: int = 0
    superdomain_seconds: float = 0.0

    # v0.11 exact whole-stage / reusable-certificate diagnostics.
    whole_stage_calls: int = 0
    whole_stage_cache_hits: int = 0
    whole_stage_dead_parents: int = 0
    whole_stage_projection_classes: int = 0
    whole_stage_candidates_pruned: int = 0
    whole_stage_seconds: float = 0.0

    # v0.12 exact endpoint-hoisting / direct-encoder diagnostics.
    endpoint_queries: int = 0
    endpoint_cache_hits: int = 0
    endpoint_dead_signatures: int = 0
    endpoint_candidates_pruned: int = 0
    endpoint_seconds: float = 0.0
    direct_pi_batch_calls: int = 0
    direct_pi_batch_graphs: int = 0
    direct_pi_batch_seconds: float = 0.0

    # v0.13 exact C8-language support diagnostics.
    c8_language_queries: int = 0
    c8_language_prunes: int = 0
    c8_language_candidates_pruned: int = 0
    c8_language_row_cache_hits: int = 0
    c8_language_row_cache_misses: int = 0
    c8_language_seconds: float = 0.0

    # v0.14 exact incremental-C8 / early-slot-bundling diagnostics.
    v014_c8_incremental_refinements: int = 0
    v014_c8_sensitive_slot_bundles: int = 0
    v014_c8_sensitive_slot_dead: int = 0
    v014_c8_sensitive_candidates_pruned: int = 0

    # v0.15 exact selected-subgraph / support-driven diagnostics.
    v015_h2_queries: int = 0
    v015_h2_refinements: int = 0
    v015_h2_prunes: int = 0
    v015_h2_candidates_pruned: int = 0
    v015_h5_queries: int = 0
    v015_h5_refinements: int = 0
    v015_h5_prunes: int = 0
    v015_h5_candidates_pruned: int = 0
    v015_support_prefix_states: int = 0
    v015_support_prefix_dead: int = 0
    v015_support_prefix_bundles_skipped: int = 0

    v011_kuratowski_checks: int = 0
    v011_kuratowski_hits: int = 0
    v011_kuratowski_learned: int = 0
    v011_iso_checks: int = 0
    v011_iso_hits: int = 0
    v011_batch_calls: int = 0
    v011_batch_graphs: int = 0
    v011_batch_seconds: float = 0.0

    # Exact search-space accounting. Python ints are arbitrary precision.
    total_candidates: int = 0
    resolved_candidates: int = 0
    planarity_pruned_candidates: int = 0
    c6_pruned_candidates: int = 0
    full_candidates_resolved: int = 0

    # v0.8.1 batched-screening / depth diagnostics.
    batch_planarity_calls: int = 0
    batch_planarity_candidates: int = 0
    batch_planarity_seconds: float = 0.0
    depth_planarity_tests: dict = field(default_factory=dict)
    depth_nonplanar_prunes: dict = field(default_factory=dict)
    depth_batch_calls: dict = field(default_factory=dict)

    # v0.8.1 compiled-parallel / exact-certificate diagnostics.
    planarity_workers: int = 1
    openmp_enabled: bool = False
    planarity_parallel_threshold: int = 4
    kuratowski_certificates_learned: int = 0
    kuratowski_cache_hits: int = 0
    kuratowski_certificate_seconds: float = 0.0
    kuratowski_cached_edges_total: int = 0

    elapsed_seconds: float = 0.0
    planarity_backend: str = "networkx"
    planarity_seconds: float = 0.0


@dataclass
class SearchResult:
    status: str  # THRACKLEABLE, NONTHRACKLEABLE, INCONCLUSIVE
    witness_pi: Optional[Pi]
    stats: SearchStats
    reason: str


@dataclass
class DB682CoreResult:
    """Combined result of the exact eight-core DB(6,8,-2) decomposition."""

    status: str
    witness_pi: Optional[Pi]
    total_candidates: int
    resolved_candidates: int
    exact_core_count: int
    excluded_core_patterns: int
    core_results: List[dict]
    elapsed_seconds: float
    reason: str


class SearchLimitReached(RuntimeError):
    pass


class ThrackleGraph:
    """Simple connected abstract graph with stable integer edge IDs."""

    def __init__(
        self,
        edges: Iterable[Tuple[Vertex, Vertex]],
        *,
        label: Optional[str] = None,
        source_kind: str = "edges",
        source_parameters: Optional[dict] = None,
    ):
        self.edges: List[Edge] = [
            Edge(i, u, v) for i, (u, v) in enumerate(edges)
        ]
        self.edge_by_id = {e.id: e for e in self.edges}
        self.label = label or "Custom graph"
        self.source_kind = source_kind
        self.source_parameters = dict(source_parameters or {})

        self.graph = nx.Graph()
        for e in self.edges:
            if e.u == e.v:
                raise ValueError("Loops are not supported.")
            if self.graph.has_edge(e.u, e.v):
                raise ValueError("Parallel/duplicate edges are not supported.")
            self.graph.add_edge(e.u, e.v, eid=e.id)

        if not self.edges:
            raise ValueError("The graph must contain at least one edge.")
        if not nx.is_connected(self.graph):
            raise ValueError(
                "v0.8.1 currently expects a connected graph so that one Euler "
                "walk can activate all edges."
            )

        # Fixed data used repeatedly by the search.
        self._endpoints: Dict[int, FrozenSet[Vertex]] = {
            e.id: frozenset((e.u, e.v)) for e in self.edges
        }
        self._nonincident: Dict[int, Tuple[int, ...]] = {}
        for e in self.edges:
            self._nonincident[e.id] = tuple(
                f.id
                for f in self.edges
                if f.id != e.id
                and self._endpoints[e.id].isdisjoint(self._endpoints[f.id])
            )

    def nonincident_edges(self, eid: int, allowed_ids=None) -> List[int]:
        """Return E_e, optionally restricted to a supplied active set."""
        base = self._nonincident[eid]
        if allowed_ids is None:
            return list(base)
        allowed = set(allowed_ids)
        return [f for f in base if f in allowed]

    def candidate_count(self) -> int:
        return prod(factorial(len(self._nonincident[e.id])) for e in self.edges)

    def total_required_crossings(self) -> int:
        # Every nonincident pair is counted from both endpoints in the sum.
        return sum(len(self._nonincident[e.id]) for e in self.edges) // 2

    def euler_walk(self):
        """
        Return edge_order and an orientation induced by the traversal.

        The order is used for activation. The orientation is a valid arbitrary
        orientation for the crossing-order lists. C6 tests convert these global
        directions to a local direction around each 6-cycle when needed.
        """
        odd = [v for v, d in self.graph.degree if d % 2 == 1]
        if len(odd) not in (0, 2):
            raise ValueError("The graph has no single Euler trail/circuit.")

        if len(odd) == 2:
            walk = list(nx.eulerian_path(self.graph, source=odd[0]))
        else:
            walk = list(nx.eulerian_circuit(self.graph))

        pair_to_id = {
            frozenset((e.u, e.v)): e.id
            for e in self.edges
        }

        order: List[int] = []
        oriented: Dict[int, Tuple[Vertex, Vertex]] = {}
        for u, v in walk:
            eid = pair_to_id[frozenset((u, v))]
            if eid in oriented:
                raise AssertionError("Euler walk repeated an edge.")
            order.append(eid)
            oriented[eid] = (u, v)

        if len(order) != len(self.edges):
            raise AssertionError("Euler walk did not visit every edge exactly once.")

        return order, oriented

    def simple_six_cycles(self) -> List[SixCycle]:
        """
        Enumerate all simple cycles of length 6, deduplicated up to rotation
        and reversal. Intended for the small sparse graphs studied here.
        """
        pair_to_id = {
            frozenset((e.u, e.v)): e.id
            for e in self.edges
        }

        seen_edge_cycles = set()
        raw: List[Tuple[Tuple[Vertex, ...], Tuple[int, ...]]] = []

        for start in self.graph.nodes:
            path = [start]

            def dfs(current):
                if len(path) == 6:
                    if not self.graph.has_edge(current, start):
                        return
                    vertices = tuple(path)
                    edge_seq = tuple(
                        pair_to_id[frozenset((vertices[i], vertices[(i + 1) % 6]))]
                        for i in range(6)
                    )

                    rots = []
                    seq = edge_seq
                    rev = tuple(reversed(edge_seq))
                    for base in (seq, rev):
                        for k in range(6):
                            rots.append(base[k:] + base[:k])
                    canonical = min(rots)

                    if canonical not in seen_edge_cycles:
                        seen_edge_cycles.add(canonical)
                        raw.append((vertices, edge_seq))
                    return

                for nxt in self.graph.neighbors(current):
                    if nxt == start or nxt in path:
                        continue
                    path.append(nxt)
                    dfs(nxt)
                    path.pop()

            dfs(start)

        return [
            SixCycle(i, vertices, edges)
            for i, (vertices, edges) in enumerate(raw)
        ]


def cycle_graph(n: int) -> ThrackleGraph:
    if n < 3:
        raise ValueError("A cycle needs at least 3 vertices.")
    return ThrackleGraph(
        ((i, (i + 1) % n) for i in range(n)),
        label=f"C{n}",
        source_kind="cycle",
        source_parameters={"n": n},
    )


def dumbbell(c1: int, c2: int, l: int) -> ThrackleGraph:
    """Construct DB(c1,c2,l) using the same convention as v0.2."""
    if c1 < 3 or c2 < 3:
        raise ValueError("Cycle lengths must be at least 3.")

    edges: List[Tuple[Vertex, Vertex]] = []

    if l < 0:
        shared = -l
        if shared >= min(c1, c2):
            raise ValueError("The shared path is too long.")

        A, B = "A", "B"

        def path(prefix: str, length: int):
            vertices = [A] + [f"{prefix}{i}" for i in range(1, length)] + [B]
            return list(zip(vertices, vertices[1:]))

        edges += path("s", shared)
        edges += path("p", c1 - shared)
        edges += path("q", c2 - shared)

    elif l == 0:
        x = "X"
        first = [x] + [f"a{i}" for i in range(1, c1)]
        second = [x] + [f"b{i}" for i in range(1, c2)]
        edges += list(zip(first, first[1:])) + [(first[-1], x)]
        edges += list(zip(second, second[1:])) + [(second[-1], x)]

    else:
        first = [f"a{i}" for i in range(c1)]
        second = [f"b{i}" for i in range(c2)]
        edges += list(zip(first, first[1:])) + [(first[-1], first[0])]
        edges += list(zip(second, second[1:])) + [(second[-1], second[0])]

        if l == 1:
            edges.append((first[0], second[0]))
        else:
            middle = [f"p{i}" for i in range(1, l)]
            connector = [first[0]] + middle + [second[0]]
            edges += list(zip(connector, connector[1:]))

    return ThrackleGraph(
        edges,
        label=f"DB({c1},{c2},{l})",
        source_kind="dumbbell",
        source_parameters={"c1": c1, "c2": c2, "l": l},
    )


def DB(c1: int, c2: int, l: int) -> ThrackleGraph:
    """Friendly constructor for DB(c1,c2,l)."""
    return dumbbell(c1, c2, l)


def Cycle(n: int) -> ThrackleGraph:
    """Friendly constructor for the cycle C_n."""
    return cycle_graph(n)


def Edges(edges: Iterable[Tuple[Vertex, Vertex]], label: str = "Custom graph") -> ThrackleGraph:
    """Build a custom graph from vertex-to-vertex edge pairs."""
    return ThrackleGraph(edges, label=label, source_kind="edges")


def crossing_vertex(eid: int, fid: int):
    a, b = sorted((eid, fid))
    return _CrossingNode(a, b)


def is_crossing_vertex(v) -> bool:
    return isinstance(v, _CrossingNode)


def modeled_pairs(pi: Pi, active_ids) -> set[Tuple[int, int]]:
    active = set(active_ids)
    pairs = set()
    for e in active:
        for f in pi[e]:
            if f not in active:
                raise ValueError("pi contains a crossing with an inactive edge.")
            if e not in pi[f]:
                raise ValueError(
                    f"Inconsistent partial Pi: {f} in pi[{e}] but {e} not in pi[{f}]."
                )
            pairs.add(tuple(sorted((e, f))))
    return pairs


def validate_partial_pi(G: ThrackleGraph, pi: Pi, active_ids) -> None:
    active = set(active_ids)
    for e in active:
        if len(pi[e]) != len(set(pi[e])):
            raise ValueError(f"pi[{e}] contains a duplicate crossing.")
        allowed = set(G.nonincident_edges(e, active))
        if not set(pi[e]).issubset(allowed):
            raise ValueError(
                f"pi[{e}] contains an edge that is not an active nonincident edge."
            )
    modeled_pairs(pi, active)


def validate_full_pi(G: ThrackleGraph, pi: Pi) -> None:
    all_ids = [e.id for e in G.edges]
    validate_partial_pi(G, pi, all_ids)
    for e in G.edges:
        expected = set(G.nonincident_edges(e.id))
        if set(pi[e.id]) != expected:
            raise ValueError(
                f"pi[{e.id}] is incomplete. Expected {sorted(expected)}, got {pi[e.id]}."
            )


def build_prefix_planarization(
    G: ThrackleGraph,
    pi: Pi,
    active_ids,
    oriented: Dict[int, Tuple[Vertex, Vertex]],
    *,
    current_eid: int,
    current_complete: bool,
    validate: bool = True,
    crossing_cache: Optional[Dict[Tuple[int, int], Hashable]] = None,
) -> nx.Graph:
    """Safe monotone prefix graph used for immediate planarity pruning.

    Older active edges are represented completely.  The currently activated
    edge is represented only from its oriented start through the crossings
    already modeled; its final tail is added only when that activation stage is
    complete.  Every later UPDATE only subdivides an older edge and extends the
    current prefix, so this graph is a minor of every descendant completion.
    """
    active_ids = tuple(active_ids)
    if validate:
        validate_partial_pi(G, pi, active_ids)

    H = nx.Graph()
    for eid in active_ids:
        u, v = oriented[eid]
        nodes = [u]
        for f in pi[eid]:
            pair = tuple(sorted((eid, f)))
            x = crossing_cache[pair] if crossing_cache is not None else crossing_vertex(eid, f)
            nodes.append(x)
        if eid != current_eid or current_complete:
            nodes.append(v)
        H.add_nodes_from(nodes)
        H.add_edges_from(zip(nodes, nodes[1:]))
    return H


def build_partial_planarization(
    G: ThrackleGraph,
    pi: Pi,
    active_ids,
    oriented: Dict[int, Tuple[Vertex, Vertex]],
    *,
    validate: bool = True,
    crossing_cache: Optional[Dict[Tuple[int, int], Hashable]] = None,
) -> nx.Graph:
    """Compatibility rebuild of the v0.8 safe prefix graph.

    The newest active edge is treated as current.  It is considered complete
    exactly when its Pi list already contains every older active nonincident
    edge.
    """
    active_ids = tuple(active_ids)
    if not active_ids:
        return nx.Graph()
    current = active_ids[-1]
    active_set = set(active_ids[:-1])
    expected = {f for f in G._nonincident[current] if f in active_set}
    complete = set(pi[current]) == expected
    return build_prefix_planarization(
        G, pi, active_ids, oriented,
        current_eid=current, current_complete=complete,
        validate=validate, crossing_cache=crossing_cache,
    )


def build_locked_prefix_minor(
    G: ThrackleGraph,
    pi: Pi,
    active_ids,
    oriented: Dict[int, Tuple[Vertex, Vertex]],
    *,
    current_eid: int,
    current_complete: bool,
    validate: bool = True,
    crossing_cache: Optional[Dict[Tuple[int, int], Hashable]] = None,
) -> nx.Graph:
    """Stronger safe minor retaining already-forced crossing-locking structure.

    Begin with the safe prefix graph.  A represented segment whose endpoints
    are both modeled crossings is replaced by one stable block vertex; any
    future crossings inserted into that segment can be contracted into this
    block in a full completion.  At each modeled crossing x, add exactly the
    edges of the Fulek--Pach K_{2,2} locking gadget supported by arms that are
    already represented.  The missing forward arm of an unfinished current
    edge is never guessed.

    For any complete extension, deleting future-only edge pieces/gadget edges
    and contracting future subdivisions inside represented segments yields a
    graph containing this locked prefix.  Hence it is a minor of every complete
    extension.  Nonplanarity is therefore a sound pruning certificate.
    """
    active_ids = tuple(active_ids)
    if validate:
        validate_partial_pi(G, pi, active_ids)

    H = nx.Graph()
    paths: Dict[int, List[Hashable]] = {}
    positions: Dict[Tuple[int, Hashable], int] = {}
    blocks: Dict[Tuple[int, Hashable, Hashable], Hashable] = {}

    for eid in active_ids:
        u, v = oriented[eid]
        nodes: List[Hashable] = [u]
        for f in pi[eid]:
            pair = tuple(sorted((eid, f)))
            nodes.append(crossing_cache[pair] if crossing_cache is not None else crossing_vertex(eid, f))
        if eid != current_eid or current_complete:
            nodes.append(v)
        paths[eid] = nodes
        for i, node in enumerate(nodes):
            positions[(eid, node)] = i
        H.add_nodes_from(nodes)
        H.add_edges_from(zip(nodes, nodes[1:]))

    for eid, nodes in paths.items():
        for a, b in list(zip(nodes, nodes[1:])):
            if is_crossing_vertex(a) and is_crossing_vertex(b):
                block = _SubdivisionNode(eid, a, b)
                if H.has_edge(a, b):
                    H.remove_edge(a, b)
                H.add_edge(a, block)
                H.add_edge(block, b)
                blocks[(eid, a, b)] = block
                blocks[(eid, b, a)] = block

    def represented_arms(eid: int, x: Hashable) -> List[Hashable]:
        nodes = paths[eid]
        i = positions[(eid, x)]
        out: List[Hashable] = []
        if i > 0:
            y = nodes[i - 1]
            out.append(blocks[(eid, y, x)] if is_crossing_vertex(y) else y)
        if i + 1 < len(nodes):
            y = nodes[i + 1]
            out.append(blocks[(eid, x, y)] if is_crossing_vertex(y) else y)
        return out

    for x in [n for n in H.nodes if is_crossing_vertex(n)]:
        e, f = x.a, x.b
        if e not in paths or f not in paths:
            continue
        if (e, x) not in positions or (f, x) not in positions:
            continue
        for a in represented_arms(e, x):
            for b in represented_arms(f, x):
                H.add_edge(a, b)

    return H


def build_active_augmented_minor(
    G: ThrackleGraph,
    pi: Pi,
    active_ids,
    oriented: Dict[int, Tuple[Vertex, Vertex]],
    *,
    validate: bool = True,
    crossing_cache: Optional[Dict[Tuple[int, int], Hashable]] = None,
) -> nx.Graph:
    """Full Fulek--Pach augmented graph of a completed active-edge prefix.

    This is the stage-complete specialization of ``build_locked_prefix_minor``.
    It is a minor of every full completion after inactive edges are deleted and
    their subdivisions along active paths are contracted.
    """
    active_ids = tuple(active_ids)
    if not active_ids:
        return nx.Graph()
    current = active_ids[-1]
    return build_locked_prefix_minor(
        G, pi, active_ids, oriented,
        current_eid=current, current_complete=True,
        validate=validate, crossing_cache=crossing_cache,
    )


def build_augmented_graph(
    G: ThrackleGraph,
    pi: Pi,
    oriented: Optional[Dict[int, Tuple[Vertex, Vertex]]] = None,
    *,
    validate: bool = True,
    crossing_cache: Optional[Dict[Tuple[int, int], Hashable]] = None,
) -> nx.Graph:
    """Build the complete augmented Fulek–Pach graph G'(G,Pi)."""
    if validate:
        validate_full_pi(G, pi)

    if oriented is None:
        oriented = {e.id: (e.u, e.v) for e in G.edges}

    H = nx.Graph()
    paths: Dict[int, List[Hashable]] = {}
    positions: Dict[Tuple[int, Hashable], int] = {}

    for e in G.edges:
        u, v = oriented[e.id]
        middle = []
        for f in pi[e.id]:
            pair = tuple(sorted((e.id, f)))
            middle.append(
                crossing_cache[pair]
                if crossing_cache is not None
                else crossing_vertex(e.id, f)
            )
        path = [u] + middle + [v]
        paths[e.id] = path
        for i, node in enumerate(path):
            positions[(e.id, node)] = i
        H.add_nodes_from(path)
        H.add_edges_from(zip(path, path[1:]))

    subdivision = {}
    for e in G.edges:
        path = paths[e.id]
        for a, b in zip(path, path[1:]):
            if is_crossing_vertex(a) and is_crossing_vertex(b):
                s = _SubdivisionNode(e.id, a, b)
                if H.has_edge(a, b):
                    H.remove_edge(a, b)
                H.add_edge(a, s)
                H.add_edge(s, b)
                subdivision[(e.id, a, b)] = s
                subdivision[(e.id, b, a)] = s

    def two_neighbors_along_edge(eid: int, x):
        path = paths[eid]
        i = positions[(eid, x)]
        before = path[i - 1]
        after = path[i + 1]
        if is_crossing_vertex(before):
            before = subdivision[(eid, before, x)]
        if is_crossing_vertex(after):
            after = subdivision[(eid, x, after)]
        return before, after

    handled = set()
    for e in G.edges:
        for f in pi[e.id]:
            pair = tuple(sorted((e.id, f)))
            if pair in handled:
                continue
            handled.add(pair)
            x = (
                crossing_cache[pair]
                if crossing_cache is not None
                else crossing_vertex(*pair)
            )
            e_side = two_neighbors_along_edge(pair[0], x)
            f_side = two_neighbors_along_edge(pair[1], x)
            for a in e_side:
                for b in f_side:
                    H.add_edge(a, b)
            if validate and H.degree(x) != 4:
                raise AssertionError(
                    f"Former crossing {x} should have degree 4; got degree {H.degree(x)}."
                )

    return H


def _format_big_int(n: int, significant: int = 5) -> str:
    if abs(n) < 1000000:
        return f"{n:,}"
    s = str(abs(n))
    exp = len(s) - 1
    head = s[:significant]
    mant = head[0] + ("." + head[1:] if significant > 1 else "")
    sign = "-" if n < 0 else ""
    return f"{sign}{mant}e{exp}"


def coverage_percent_string(resolved: int, total: int, precision: int = 10) -> str:
    if total <= 0:
        return "n/a"
    if resolved == total:
        return "100.0000000000%"
    with localcontext() as ctx:
        ctx.prec = max(precision + 8, 24)
        pct = Decimal(resolved) * Decimal(100) / Decimal(total)
        if pct == 0:
            return "0%"
        if pct < Decimal("0.000001"):
            return f"{pct:.{precision}E}%"
        return f"{pct:.{precision}f}%"


@dataclass
class SearchChoice:
    """One immediate backtracking choice at a partial-Pi state."""

    old: int
    pos: int
    child_remaining: Tuple[int, ...]
    child_subtree: int
    base_rank: int
    lookahead_viable_count: Optional[int] = None
    lookahead_surviving_weight: Optional[int] = None
    lookahead_screen: Optional["ScreenResult"] = None
    lookahead_state_key: Optional[Tuple] = None


@dataclass
class ScreenResult:
    """Immediate screening result for one exact partial search state."""

    choices: List[SearchChoice]
    total_choices: int
    pruned_choices: int
    surviving_weight: int




# ---------------------------------------------------------------------------
# Planarity backends
# ---------------------------------------------------------------------------

_BOOST_CPP_SOURCE = r"""
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/boyer_myrvold_planar_test.hpp>
#include <boost/graph/properties.hpp>
#include <exception>
#include <iterator>
#include <vector>

// Keep the hot planarity path as lean as possible.  Edge indices are needed
// only when we explicitly request a Kuratowski certificate, so ordinary and
// batched planarity use a graph with no edge property at all.
using PlainGraph = boost::adjacency_list<
    boost::vecS, boost::vecS, boost::undirectedS
>;
using EdgeProperty = boost::property<boost::edge_index_t, int>;
using CertGraph = boost::adjacency_list<
    boost::vecS, boost::vecS, boost::undirectedS,
    boost::no_property, EdgeProperty
>;
using CertEdgeDesc = boost::graph_traits<CertGraph>::edge_descriptor;

static int build_plain(PlainGraph& g, int n_vertices, int n_edges, const int* endpoints) {
    g = PlainGraph(static_cast<std::size_t>(n_vertices));
    for (int i=0;i<n_edges;++i) {
        int u=endpoints[2*i], v=endpoints[2*i+1];
        if (u<0 || v<0 || u>=n_vertices || v>=n_vertices) return -2;
        boost::add_edge(u,v,g);
    }
    return 0;
}

static int build_cert(CertGraph& g, int n_vertices, int n_edges, const int* endpoints) {
    g = CertGraph(static_cast<std::size_t>(n_vertices));
    for (int i=0;i<n_edges;++i) {
        int u=endpoints[2*i], v=endpoints[2*i+1];
        if (u<0 || v<0 || u>=n_vertices || v>=n_vertices) return -2;
        auto ed=boost::add_edge(u,v,g).first;
        boost::put(boost::edge_index,g,ed,i);
    }
    return 0;
}

extern "C" int thrackle_openmp_enabled() {
#ifdef _OPENMP
    return 1;
#else
    return 0;
#endif
}

extern "C" int thrackle_is_planar(int n_vertices,int n_edges,const int* endpoints) {
    try {
        PlainGraph g; int rc=build_plain(g,n_vertices,n_edges,endpoints); if(rc) return rc;
        return boost::boyer_myrvold_planarity_test(g) ? 1 : 0;
    } catch (...) { return -1; }
}

extern "C" int thrackle_kuratowski_edge_indices(
    int n_vertices,int n_edges,const int* endpoints,int* out_indices,int max_out
) {
    try {
        CertGraph g; int rc=build_cert(g,n_vertices,n_edges,endpoints); if(rc) return rc;
        std::vector<CertEdgeDesc> kur;
        bool planar=boost::boyer_myrvold_planarity_test(
            boost::boyer_myrvold_params::graph=g,
            boost::boyer_myrvold_params::kuratowski_subgraph=std::back_inserter(kur),
            boost::boyer_myrvold_params::edge_index_map=boost::get(boost::edge_index,g)
        );
        if(planar) return 0;
        if(static_cast<int>(kur.size())>max_out) return -5;
        for(std::size_t i=0;i<kur.size();++i) out_indices[i]=boost::get(boost::edge_index,g,kur[i]);
        return static_cast<int>(kur.size());
    } catch (...) { return -1; }
}

extern "C" int thrackle_batch_split_planarity_serial(
    int n_vertices,int n_edges,const int* endpoints,
    int n_candidates,const int* mods,unsigned char* results
) {
    try {
        PlainGraph base;
        int rc=build_plain(base,n_vertices,n_edges,endpoints);
        if(rc) return rc;
        for(int i=0;i<n_candidates;++i) {
            const int* p=mods+5*i;
            int a=p[0],b=p[1],c=p[2],d=p[3],x=p[4];
            if (a<0 || b<0 || c<0 || d<0 || x<0 ||
                a>=n_vertices || b>=n_vertices || c>=n_vertices ||
                d>=n_vertices || x>=n_vertices) return -4;
            PlainGraph g=base;
            if (!boost::edge(a,b,g).second || !boost::edge(c,d,g).second) return -4;
            boost::remove_edge(a,b,g);
            boost::remove_edge(c,d,g);
            boost::add_edge(a,x,g);
            boost::add_edge(x,b,g);
            boost::add_edge(c,x,g);
            boost::add_edge(x,d,g);
            results[i]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        return 0;
    } catch (...) { return -1; }
}

extern "C" int thrackle_batch_split_planarity(
    int n_vertices,int n_edges,const int* endpoints,
    int n_candidates,const int* mods,int n_threads,unsigned char* results
) {
    try {
        if(n_threads<1) n_threads=1;
        PlainGraph base;
        int rc=build_plain(base,n_vertices,n_edges,endpoints);
        if(rc) return rc;
        // OpenMP startup can cost more than it saves for tiny batches.  Copying
        // the already-built base graph is faster here than reconstructing all
        // unchanged edges for every child.
        #pragma omp parallel for schedule(static) if(n_threads>1 && n_candidates>=4) num_threads(n_threads)
        for(int i=0;i<n_candidates;++i) {
            const int* p=mods+5*i;
            int a=p[0],b=p[1],c=p[2],d=p[3],x=p[4];
            if (a<0 || b<0 || c<0 || d<0 || x<0 ||
                a>=n_vertices || b>=n_vertices || c>=n_vertices ||
                d>=n_vertices || x>=n_vertices) {
                results[i]=2;
                continue;
            }
            PlainGraph g=base;
            if (!boost::edge(a,b,g).second || !boost::edge(c,d,g).second) {
                results[i]=2;
                continue;
            }
            boost::remove_edge(a,b,g);
            boost::remove_edge(c,d,g);
            boost::add_edge(a,x,g);
            boost::add_edge(x,b,g);
            boost::add_edge(c,x,g);
            boost::add_edge(x,d,g);
            results[i]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        for(int i=0;i<n_candidates;++i) if(results[i]>1) return -4;
        return 0;
    } catch (...) { return -1; }
}


extern "C" int thrackle_batch_prefix_planarity_serial(
    int n_vertices,int n_edges,const int* endpoints,
    int n_candidates,const int* mods,unsigned char* results
) {
    try {
        PlainGraph base;
        int rc=build_plain(base,n_vertices,n_edges,endpoints);
        if(rc) return rc;
        for(int i=0;i<n_candidates;++i) {
            const int* p=mods+6*i;
            int a=p[0],b=p[1],c=p[2],x=p[3],d=p[4],close=p[5];
            if (a<0 || b<0 || c<0 || x<0 || d<0 ||
                a>=n_vertices || b>=n_vertices || c>=n_vertices ||
                x>=n_vertices || d>=n_vertices || (close!=0 && close!=1)) return -4;
            PlainGraph g=base;
            if (!boost::edge(a,b,g).second) return -4;
            boost::remove_edge(a,b,g);
            boost::add_edge(a,x,g);
            boost::add_edge(x,b,g);
            boost::add_edge(c,x,g);
            if (close) boost::add_edge(x,d,g);
            results[i]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        return 0;
    } catch (...) { return -1; }
}

extern "C" int thrackle_batch_prefix_planarity(
    int n_vertices,int n_edges,const int* endpoints,
    int n_candidates,const int* mods,int n_threads,unsigned char* results
) {
    try {
        if(n_threads<1) n_threads=1;
        PlainGraph base;
        int rc=build_plain(base,n_vertices,n_edges,endpoints);
        if(rc) return rc;
        #pragma omp parallel for schedule(static) if(n_threads>1 && n_candidates>=4) num_threads(n_threads)
        for(int i=0;i<n_candidates;++i) {
            const int* p=mods+6*i;
            int a=p[0],b=p[1],c=p[2],x=p[3],d=p[4],close=p[5];
            if (a<0 || b<0 || c<0 || x<0 || d<0 ||
                a>=n_vertices || b>=n_vertices || c>=n_vertices ||
                x>=n_vertices || d>=n_vertices || (close!=0 && close!=1)) {
                results[i]=2; continue;
            }
            PlainGraph g=base;
            if (!boost::edge(a,b,g).second) { results[i]=2; continue; }
            boost::remove_edge(a,b,g);
            boost::add_edge(a,x,g);
            boost::add_edge(x,b,g);
            boost::add_edge(c,x,g);
            if (close) boost::add_edge(x,d,g);
            results[i]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        for(int i=0;i<n_candidates;++i) if(results[i]>1) return -4;
        return 0;
    } catch (...) { return -1; }
}


// v0.11: exact batch planarity for a list of independently constructed graphs.
// edge_offsets are measured in edges (not endpoint integers), with n_graphs+1
// entries.  Each graph uses local vertex IDs 0..vertex_counts[i]-1.
extern "C" int thrackle_batch_graph_planarity(
    int n_graphs, const int* vertex_counts, const int* edge_offsets,
    const int* endpoints, int n_threads, unsigned char* results
) {
    try {
        if (n_graphs < 0) return -4;
        if (n_threads < 1) n_threads = 1;
        #pragma omp parallel for schedule(static) if(n_threads>1 && n_graphs>=4) num_threads(n_threads)
        for (int i=0; i<n_graphs; ++i) {
            int n = vertex_counts[i];
            int lo = edge_offsets[i];
            int hi = edge_offsets[i+1];
            if (n < 0 || lo < 0 || hi < lo) { results[i]=2; continue; }
            PlainGraph g(static_cast<std::size_t>(n));
            bool bad=false;
            for (int j=lo; j<hi; ++j) {
                int u=endpoints[2*j], v=endpoints[2*j+1];
                if (u<0 || v<0 || u>=n || v>=n) { bad=true; break; }
                boost::add_edge(u,v,g);
            }
            if (bad) { results[i]=2; continue; }
            results[i]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        for(int i=0;i<n_graphs;++i) if(results[i]>1) return -4;
        return 0;
    } catch (...) { return -1; }
}


// v0.12: construct COMPLETE selected-edge Fulek--Pach augmented graphs
// directly from crossing-order lists and test them, without NetworkX objects.
// This routine is an implementation-only accelerator.  A caller supplies one
// fixed selected edge set and n_graphs complete Pi restrictions on that set.
extern "C" int thrackle_batch_complete_pi_planarity(
    int n_original_vertices,
    int n_original_edges,
    const int* original_endpoints,
    int n_selected,
    const int* selected_edges,
    const int* pi_lengths,
    int n_graphs,
    const int* pi_flat,
    int n_threads,
    unsigned char* results
) {
    try {
        if (n_original_vertices < 0 || n_original_edges < 0 || n_selected < 0 || n_graphs < 0)
            return -4;
        if (n_threads < 1) n_threads = 1;

        // Fixed selected-set validation and edge-id -> selected-index map.
        std::vector<int> sel_index(static_cast<std::size_t>(n_original_edges), -1);
        for (int i=0;i<n_selected;++i) {
            int e=selected_edges[i];
            if (e<0 || e>=n_original_edges || sel_index[e]!=-1) return -4;
            sel_index[e]=i;
        }
        auto incident = [&](int e, int f) -> bool {
            int eu=original_endpoints[2*e], ev=original_endpoints[2*e+1];
            int fu=original_endpoints[2*f], fv=original_endpoints[2*f+1];
            return eu==fu || eu==fv || ev==fu || ev==fv;
        };

        int stride=0;
        for (int i=0;i<n_selected;++i) {
            int e=selected_edges[i];
            int expected=0;
            for (int j=0;j<n_selected;++j) {
                int f=selected_edges[j];
                if (i!=j && !incident(e,f)) ++expected;
            }
            if (pi_lengths[i] != expected) return -4;
            stride += pi_lengths[i];
        }

        #pragma omp parallel for schedule(static) if(n_threads>1 && n_graphs>=4) num_threads(n_threads)
        for (int gi=0; gi<n_graphs; ++gi) {
            bool bad=false;
            // crossing node indexed by selected-local pair (i,j), shared symmetrically.
            std::vector<int> cross(static_cast<std::size_t>(n_selected*n_selected), -1);
            int next_vertex=n_original_vertices;
            for (int i=0;i<n_selected;++i) {
                int e=selected_edges[i];
                for (int j=i+1;j<n_selected;++j) {
                    int f=selected_edges[j];
                    if (!incident(e,f)) {
                        cross[i*n_selected+j]=next_vertex;
                        cross[j*n_selected+i]=next_vertex;
                        ++next_vertex;
                    }
                }
            }

            // Decode and validate each complete crossing order.  Store selected-local
            // partner indices so path construction below is branch-light.
            std::vector<std::vector<int>> orders(static_cast<std::size_t>(n_selected));
            int off=gi*stride;
            for (int i=0;i<n_selected && !bad;++i) {
                int len=pi_lengths[i];
                orders[i].reserve(static_cast<std::size_t>(len));
                std::vector<unsigned char> seen(static_cast<std::size_t>(n_selected), 0);
                int e=selected_edges[i];
                for (int k=0;k<len;++k) {
                    int f=pi_flat[off++];
                    if (f<0 || f>=n_original_edges) { bad=true; break; }
                    int j=sel_index[f];
                    if (j<0 || j==i || incident(e,f) || seen[j]) { bad=true; break; }
                    seen[j]=1;
                    orders[i].push_back(j);
                }
                if (!bad) {
                    for (int j=0;j<n_selected;++j) {
                        if (j==i) continue;
                        bool required=!incident(e,selected_edges[j]);
                        if (required != static_cast<bool>(seen[j])) { bad=true; break; }
                    }
                }
            }
            if (off != (gi+1)*stride) bad=true;
            if (bad) { results[gi]=2; continue; }

            // Symmetry validation: each modeled crossing must occur on both lists.
            for (int i=0;i<n_selected && !bad;++i) {
                for (int j : orders[i]) {
                    bool found=false;
                    for (int k : orders[j]) if (k==i) { found=true; break; }
                    if (!found) { bad=true; break; }
                }
            }
            if (bad) { results[gi]=2; continue; }

            // We know an upper bound on extra subdivision vertices: sum(max(len-1,0)).
            int subdivisions=0;
            for (int i=0;i<n_selected;++i)
                if (pi_lengths[i]>1) subdivisions += pi_lengths[i]-1;
            PlainGraph g(static_cast<std::size_t>(next_vertex + subdivisions));
            int next_sub=next_vertex;

            // arm_left/right[i*n_selected+j] gives the neighbor of crossing (i,j)
            // immediately before/after it along selected edge i after subdivision.
            std::vector<int> arm_left(static_cast<std::size_t>(n_selected*n_selected), -1);
            std::vector<int> arm_right(static_cast<std::size_t>(n_selected*n_selected), -1);

            for (int i=0;i<n_selected;++i) {
                int e=selected_edges[i];
                int u=original_endpoints[2*e], v=original_endpoints[2*e+1];
                if (u<0 || v<0 || u>=n_original_vertices || v>=n_original_vertices) { bad=true; break; }
                int len=static_cast<int>(orders[i].size());
                if (len==0) {
                    boost::add_edge(u,v,g);
                    continue;
                }
                std::vector<int> cn(static_cast<std::size_t>(len));
                for (int k=0;k<len;++k) cn[k]=cross[i*n_selected+orders[i][k]];
                boost::add_edge(u,cn[0],g);
                arm_left[i*n_selected+orders[i][0]]=u;
                for (int k=0;k<len-1;++k) {
                    int sub=next_sub++;
                    boost::add_edge(cn[k],sub,g);
                    boost::add_edge(sub,cn[k+1],g);
                    arm_right[i*n_selected+orders[i][k]]=sub;
                    arm_left[i*n_selected+orders[i][k+1]]=sub;
                }
                boost::add_edge(cn[len-1],v,g);
                arm_right[i*n_selected+orders[i][len-1]]=v;
            }
            if (bad || next_sub != next_vertex+subdivisions) { results[gi]=2; continue; }

            // Fulek--Pach K_{2,2} locking gadget around every selected crossing.
            for (int i=0;i<n_selected && !bad;++i) {
                for (int j=i+1;j<n_selected;++j) {
                    if (cross[i*n_selected+j] < 0) continue;
                    int a0=arm_left[i*n_selected+j], a1=arm_right[i*n_selected+j];
                    int b0=arm_left[j*n_selected+i], b1=arm_right[j*n_selected+i];
                    if (a0<0 || a1<0 || b0<0 || b1<0) { bad=true; break; }
                    boost::add_edge(a0,b0,g); boost::add_edge(a0,b1,g);
                    boost::add_edge(a1,b0,g); boost::add_edge(a1,b1,g);
                }
            }
            if (bad) { results[gi]=2; continue; }
            results[gi]=boost::boyer_myrvold_planarity_test(g)?1:0;
        }
        for (int i=0;i<n_graphs;++i) if (results[i]>1) return -4;
        return 0;
    } catch (...) { return -1; }
}
"""

_BOOST_LIBRARY_CACHE = None
_BOOST_LIBRARY_ERROR = None


def _boost_library_path() -> Path:
    digest = hashlib.sha256(_BOOST_CPP_SOURCE.encode("utf-8")).hexdigest()[:12]
    filename = f"_thrackle_planarity_boost_{digest}.so"
    # Prefer a cache next to the module when writable (good for Colab uploads),
    # otherwise use the system temp directory.
    try:
        base = Path(__file__).resolve().parent
        test = base / ".thrackle_write_test"
        test.write_text("x", encoding="utf-8")
        test.unlink()
    except Exception:
        base = Path(tempfile.gettempdir())
    return base / filename


def _load_boost_library():
    global _BOOST_LIBRARY_CACHE, _BOOST_LIBRARY_ERROR
    if _BOOST_LIBRARY_CACHE is not None:
        return _BOOST_LIBRARY_CACHE
    if _BOOST_LIBRARY_ERROR is not None:
        raise RuntimeError(_BOOST_LIBRARY_ERROR)

    so_path = _boost_library_path()
    cpp_path = so_path.with_suffix(".cpp")
    try:
        if not so_path.exists():
            cpp_path.write_text(_BOOST_CPP_SOURCE, encoding="utf-8")
            base_cmd = [
                "g++", "-O3", "-DNDEBUG", "-std=c++17",
                "-shared", "-fPIC", str(cpp_path), "-o", str(so_path),
            ]
            proc = subprocess.run(
                base_cmd[:6] + ["-fopenmp"] + base_cmd[6:],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if proc.returncode != 0:
                proc = subprocess.run(
                    base_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    text=True, check=False,
                )
            if proc.returncode != 0:
                raise RuntimeError(
                    "Boost planarity backend compilation failed.\n" + proc.stderr[-4000:]
                )

        lib = ctypes.CDLL(str(so_path))
        lib.thrackle_is_planar.argtypes = [
            ctypes.c_int,
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int),
        ]
        lib.thrackle_is_planar.restype = ctypes.c_int
        lib.thrackle_openmp_enabled.argtypes = []
        lib.thrackle_openmp_enabled.restype = ctypes.c_int
        lib.thrackle_kuratowski_edge_indices.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int), ctypes.c_int,
        ]
        lib.thrackle_kuratowski_edge_indices.restype = ctypes.c_int
        lib.thrackle_batch_split_planarity_serial.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_split_planarity_serial.restype = ctypes.c_int
        lib.thrackle_batch_split_planarity.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.c_int,
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_split_planarity.restype = ctypes.c_int
        lib.thrackle_batch_prefix_planarity_serial.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_prefix_planarity_serial.restype = ctypes.c_int
        lib.thrackle_batch_prefix_planarity.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.c_int,
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_prefix_planarity.restype = ctypes.c_int
        lib.thrackle_batch_graph_planarity.argtypes = [
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_graph_planarity.restype = ctypes.c_int
        lib.thrackle_batch_complete_pi_planarity.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
            ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.c_int,
            ctypes.POINTER(ctypes.c_ubyte),
        ]
        lib.thrackle_batch_complete_pi_planarity.restype = ctypes.c_int
        _BOOST_LIBRARY_CACHE = lib
        return lib
    except Exception as exc:
        _BOOST_LIBRARY_ERROR = str(exc)
        raise


class _NetworkXPlanarityBackend:
    name = "networkx"
    supports_batch = False
    openmp_enabled = False

    def is_planar(self, H: nx.Graph) -> bool:
        return nx.is_planar(H)


class _BoostPlanarityBackend:
    name = "boost"
    supports_batch = True
    parallel_threshold = 4

    def __init__(self):
        self.lib = _load_boost_library()
        self.openmp_enabled = bool(self.lib.thrackle_openmp_enabled())
        # Stable integer IDs avoid rebuilding a node-index dictionary on every
        # planarity call. Nodes absent from a particular partial graph simply
        # become isolated vertices, which does not affect planarity.
        self.node_ids: Dict[Hashable, int] = {}

    def _id(self, node: Hashable) -> int:
        try:
            return self.node_ids[node]
        except KeyError:
            i = len(self.node_ids)
            self.node_ids[node] = i
            return i

    def is_planar(self, H: nx.Graph) -> bool:
        flat = array("i")
        append = flat.append
        for u, v in H.edges:
            append(self._id(u))
            append(self._id(v))

        m = len(flat) // 2
        n = len(self.node_ids)
        if m == 0:
            return True
        if flat.itemsize != ctypes.sizeof(ctypes.c_int):
            # Extremely unusual platform fallback.
            buf_type = ctypes.c_int * len(flat)
            buf = buf_type(*flat)
        else:
            buf_type = ctypes.c_int * len(flat)
            buf = buf_type.from_buffer(flat)
        answer = self.lib.thrackle_is_planar(n, m, buf)
        if answer == 1:
            return True
        if answer == 0:
            return False
        raise RuntimeError(f"Boost planarity backend returned error code {answer}.")


    def batch_split_planarity(self, H: nx.Graph, modifications, *, workers: int = 1) -> List[bool]:
        """Test many exact one-crossing local edits of the same base graph."""
        modifications = list(modifications)
        if not modifications:
            return []

        # Assign stable ids to base nodes and every candidate crossing node first,
        # so n_vertices is valid for the whole batch.
        for u, v in H.edges:
            self._id(u); self._id(v)
        for a, b, c, d, x in modifications:
            self._id(a); self._id(b); self._id(c); self._id(d); self._id(x)

        flat_edges = array("i")
        ae = flat_edges.append
        for u, v in H.edges:
            ae(self._id(u)); ae(self._id(v))

        flat_mods = array("i")
        am = flat_mods.append
        for a, b, c, d, x in modifications:
            am(self._id(a)); am(self._id(b)); am(self._id(c)); am(self._id(d)); am(self._id(x))

        edge_buf_type = ctypes.c_int * len(flat_edges)
        edge_buf = edge_buf_type.from_buffer(flat_edges) if flat_edges else edge_buf_type()
        mod_buf_type = ctypes.c_int * len(flat_mods)
        mod_buf = mod_buf_type.from_buffer(flat_mods)
        result_type = ctypes.c_ubyte * len(modifications)
        result_buf = result_type()
        worker_count = max(1, int(workers))
        # The serial entry point has no OpenMP setup overhead and is faster for
        # the many small screening batches.  Parallelism is reserved for the
        # large late-search batches where it pays for itself.
        if worker_count <= 1 or len(modifications) < self.parallel_threshold or not self.openmp_enabled:
            rc = self.lib.thrackle_batch_split_planarity_serial(
                len(self.node_ids),
                len(flat_edges) // 2,
                edge_buf,
                len(modifications),
                mod_buf,
                result_buf,
            )
        else:
            rc = self.lib.thrackle_batch_split_planarity(
                len(self.node_ids),
                len(flat_edges) // 2,
                edge_buf,
                len(modifications),
                mod_buf,
                worker_count,
                result_buf,
            )
        if rc != 0:
            raise RuntimeError(f"Boost batch planarity backend returned error code {rc}.")
        return [bool(result_buf[i]) for i in range(len(modifications))]


    def batch_prefix_planarity(self, H: nx.Graph, modifications, *, workers: int = 1) -> List[bool]:
        """Batch exact safe-prefix UPDATE edits of one base graph."""
        modifications = list(modifications)
        if not modifications:
            return []
        for u, w in H.edges:
            self._id(u); self._id(w)
        for a, b, c, x, d, close in modifications:
            self._id(a); self._id(b); self._id(c); self._id(x); self._id(d)

        flat_edges = array("i")
        for u, w in H.edges:
            flat_edges.append(self._id(u)); flat_edges.append(self._id(w))
        flat_mods = array("i")
        for a, b, c, x, d, close in modifications:
            flat_mods.extend((self._id(a), self._id(b), self._id(c), self._id(x), self._id(d), 1 if close else 0))

        edge_buf_type = ctypes.c_int * len(flat_edges)
        edge_buf = edge_buf_type.from_buffer(flat_edges) if flat_edges else edge_buf_type()
        mod_buf_type = ctypes.c_int * len(flat_mods)
        mod_buf = mod_buf_type.from_buffer(flat_mods)
        result_type = ctypes.c_ubyte * len(modifications)
        result_buf = result_type()
        worker_count = max(1, int(workers))
        if worker_count <= 1 or len(modifications) < self.parallel_threshold or not self.openmp_enabled:
            rc = self.lib.thrackle_batch_prefix_planarity_serial(
                len(self.node_ids), len(flat_edges)//2, edge_buf,
                len(modifications), mod_buf, result_buf,
            )
        else:
            rc = self.lib.thrackle_batch_prefix_planarity(
                len(self.node_ids), len(flat_edges)//2, edge_buf,
                len(modifications), mod_buf, worker_count, result_buf,
            )
        if rc != 0:
            raise RuntimeError(f"Boost prefix batch planarity backend returned error code {rc}.")
        return [bool(result_buf[i]) for i in range(len(modifications))]

    def batch_graph_planarity(self, graphs, *, workers: int = 1) -> List[bool]:
        """v0.11 exact batch planarity for independently constructed graphs.

        This is an implementation-only accelerator: every NetworkX graph is
        encoded literally with a fresh local vertex numbering, and the compiled
        routine applies the same Boost Boyer--Myrvold predicate to each graph.
        """
        graphs = list(graphs)
        if not graphs:
            return []
        vertex_counts = array("i")
        edge_offsets = array("i", [0])
        endpoints = array("i")
        edge_count = 0
        for H in graphs:
            node_id = {u: i for i, u in enumerate(H.nodes)}
            vertex_counts.append(len(node_id))
            for u, v in H.edges:
                endpoints.append(node_id[u]); endpoints.append(node_id[v])
                edge_count += 1
            edge_offsets.append(edge_count)

        vc_t = ctypes.c_int * len(vertex_counts)
        eo_t = ctypes.c_int * len(edge_offsets)
        ep_t = ctypes.c_int * len(endpoints)
        vc = vc_t.from_buffer(vertex_counts)
        eo = eo_t.from_buffer(edge_offsets)
        ep = ep_t.from_buffer(endpoints) if endpoints else ep_t()
        out_t = ctypes.c_ubyte * len(graphs)
        out = out_t()
        rc = self.lib.thrackle_batch_graph_planarity(
            len(graphs), vc, eo, ep, max(1, int(workers)), out
        )
        if rc != 0:
            raise RuntimeError(f"Boost graph-batch planarity returned error code {rc}.")
        return [bool(out[i]) for i in range(len(graphs))]


    def batch_complete_pi_planarity(
        self, G: ThrackleGraph, selected: Sequence[int], projected_pis: Sequence[Pi], *,
        oriented: Optional[Dict[int, Tuple[Vertex, Vertex]]] = None, workers: int = 1
    ) -> List[bool]:
        """v0.12 direct exact planarity for COMPLETE selected-edge Pi restrictions.

        The selected subgraph and every crossing-order list are passed literally
        to C++.  The C++ routine constructs the same completed Fulek--Pach
        augmented graph (including subdivision vertices and every K_{2,2}
        locking gadget) and runs Boost Boyer--Myrvold.  No graph hash or
        approximate representation participates in the answer.
        """
        selected = tuple(int(e) for e in selected)
        projected_pis = list(projected_pis)
        if not projected_pis:
            return []
        if len(selected) != len(set(selected)):
            raise ValueError("Direct Pi batch selected edge set contains duplicates.")

        # Stable local numbering of original graph vertices.
        vertices = list(G.graph.nodes)
        vertex_id = {u: i for i, u in enumerate(vertices)}
        if oriented is None:
            oriented = {e.id: (e.u, e.v) for e in G.edges}
        original_endpoints = array("i")
        for e in G.edges:
            u, w = oriented[e.id]
            original_endpoints.extend((vertex_id[u], vertex_id[w]))

        sel_set = set(selected)
        lengths = array("i")
        for e in selected:
            lengths.append(sum(1 for f in G._nonincident[e] if f in sel_set))
        stride = sum(lengths)
        flat_pi = array("i")
        for pi in projected_pis:
            for e, required_len in zip(selected, lengths):
                seq = tuple(int(x) for x in pi[e])
                if len(seq) != required_len:
                    raise AssertionError(
                        f"Direct Pi batch requires a complete selected restriction on edge {e}: "
                        f"got {len(seq)}, expected {required_len}."
                    )
                flat_pi.extend(seq)
        if len(flat_pi) != stride * len(projected_pis):
            raise AssertionError("Direct Pi batch packing stride mismatch.")

        selected_arr = array("i", selected)
        def cbuf(a):
            T = ctypes.c_int * len(a)
            return T.from_buffer(a) if a else T()
        ep = cbuf(original_endpoints)
        se = cbuf(selected_arr)
        le = cbuf(lengths)
        pf = cbuf(flat_pi)
        out_t = ctypes.c_ubyte * len(projected_pis)
        out = out_t()
        rc = self.lib.thrackle_batch_complete_pi_planarity(
            len(vertices), len(G.edges), ep, len(selected), se, le,
            len(projected_pis), pf, max(1, int(workers)), out
        )
        if rc != 0:
            raise RuntimeError(f"Boost direct-Pi batch returned error code {rc}.")
        return [bool(out[i]) for i in range(len(projected_pis))]


    def kuratowski_edges(self, H: nx.Graph):
        """Return an exact Boost Kuratowski edge certificate, or None if planar."""
        edge_list = list(H.edges)
        if not edge_list:
            return None
        flat = array("i")
        for u, v in edge_list:
            flat.append(self._id(u)); flat.append(self._id(v))
        buf_type = ctypes.c_int * len(flat)
        buf = buf_type.from_buffer(flat)
        out_type = ctypes.c_int * len(edge_list)
        out = out_type()
        count = self.lib.thrackle_kuratowski_edge_indices(
            len(self.node_ids), len(edge_list), buf, out, len(edge_list)
        )
        if count == 0:
            return None
        if count < 0:
            raise RuntimeError(f"Boost Kuratowski backend returned error code {count}.")
        cert = set()
        for j in range(count):
            u, v = edge_list[out[j]]
            cert.add(frozenset((u, v)))
        return frozenset(cert)


def _make_planarity_backend(name: str):
    normalized = str(name).strip().lower()
    if normalized not in {"auto", "boost", "networkx"}:
        raise ValueError('planarity_backend must be "auto", "boost", or "networkx".')
    if normalized == "networkx":
        return _NetworkXPlanarityBackend()
    try:
        return _BoostPlanarityBackend()
    except Exception as exc:
        if normalized == "boost":
            raise RuntimeError(
                "Requested planarity_backend='boost', but the compiled backend "
                f"could not be loaded: {exc}"
            ) from exc
        print(
            "v0.8.1: Boost planarity backend unavailable; safely falling back "
            f"to NetworkX. Reason: {exc}",
            file=sys.stderr,
        )
        return _NetworkXPlanarityBackend()


def verify_planarity_backends(
    max_atlas_graphs: int = 1000,
    max_batch_cases: int = 120,
    max_kuratowski_cases: int = 40,
) -> dict:
    """
    Cross-check the compiled backend against NetworkX.

    This release-verification helper checks four independent paths:
    1. ordinary planarity on graph-atlas graphs;
    2. legacy split-batch planarity against explicit Python child graphs;
    3. the v0.8 safe-prefix batch edit against explicit Python child graphs;
    4. Boost Kuratowski certificates verified independently in NetworkX.
    """
    boost = _BoostPlanarityBackend()
    nx_backend = _NetworkXPlanarityBackend()
    atlas = nx.graph_atlas_g()

    checked = 0
    for G in atlas[:max_atlas_graphs]:
        a = nx_backend.is_planar(G)
        b = boost.is_planar(G)
        if a != b:
            raise AssertionError(
                f"Planarity backend mismatch on atlas graph {checked}: "
                f"NetworkX={a}, Boost={b}, nodes={G.number_of_nodes()}, "
                f"edges={G.number_of_edges()}"
            )
        checked += 1

    # Exercise the exact local edit used by forward screening.  We deliberately
    # use nonincident edge pairs, matching a proper crossing candidate.
    batch_cases = 0
    parallel_workers = max(1, min(4, os.cpu_count() or 1))
    for gi, G in enumerate(atlas[:max_atlas_graphs]):
        if batch_cases >= max_batch_cases:
            break
        edges = list(G.edges)
        mods = []
        expected = []
        for i, (a, b) in enumerate(edges):
            for c, d in edges[i + 1:]:
                if {a, b}.intersection((c, d)):
                    continue
                x = ("verify-crossing", gi, len(mods))
                H = G.copy()
                H.remove_edge(a, b)
                H.remove_edge(c, d)
                H.add_edges_from([(a, x), (x, b), (c, x), (x, d)])
                mods.append((a, b, c, d, x))
                expected.append(nx.is_planar(H))
                if len(mods) >= 8 or batch_cases + len(mods) >= max_batch_cases:
                    break
            if len(mods) >= 8 or batch_cases + len(mods) >= max_batch_cases:
                break
        if not mods:
            continue
        serial = boost.batch_split_planarity(G, mods, workers=1)
        parallel = boost.batch_split_planarity(G, mods, workers=parallel_workers)
        if serial != expected or parallel != expected:
            raise AssertionError(
                f"Batch planarity mismatch on atlas graph {gi}: "
                f"expected={expected}, serial={serial}, parallel={parallel}"
            )
        batch_cases += len(mods)

    prefix_batch_cases = 0
    for gi, G in enumerate(atlas[:max_atlas_graphs]):
        if prefix_batch_cases >= max_batch_cases:
            break
        edges = list(G.edges)
        if not edges:
            continue
        H = G.copy()
        mods = []
        expected = []
        for j, (a, b) in enumerate(edges[:8]):
            c = ("prefix-start", gi, j)
            x = ("prefix-cross", gi, j)
            d = ("prefix-end", gi, j)
            close = bool(j % 2)
            H.add_node(c)
            K = H.copy()
            K.remove_edge(a, b)
            K.add_edges_from([(a, x), (x, b), (c, x)])
            if close:
                K.add_edge(x, d)
            mods.append((a, b, c, x, d, close))
            expected.append(nx.is_planar(K))
            if prefix_batch_cases + len(mods) >= max_batch_cases:
                break
        if not mods:
            continue
        serial = boost.batch_prefix_planarity(H, mods, workers=1)
        parallel = boost.batch_prefix_planarity(H, mods, workers=parallel_workers)
        if serial != expected or parallel != expected:
            raise AssertionError(
                f"Safe-prefix batch mismatch on atlas graph {gi}: "
                f"expected={expected}, serial={serial}, parallel={parallel}"
            )
        prefix_batch_cases += len(mods)

    # v0.11 generic independent-graph batch path.  Compare both serial and
    # OpenMP modes with NetworkX on chunks of graph-atlas graphs.
    graph_batch_cases = 0
    chunk = []
    for G in atlas[:max_atlas_graphs]:
        if graph_batch_cases >= max_batch_cases:
            break
        chunk.append(G)
        if len(chunk) >= 16 or graph_batch_cases + len(chunk) >= max_batch_cases:
            expected = [nx.is_planar(H) for H in chunk]
            serial = boost.batch_graph_planarity(chunk, workers=1)
            parallel = boost.batch_graph_planarity(chunk, workers=parallel_workers)
            if serial != expected or parallel != expected:
                raise AssertionError(
                    f"v0.11 generic graph-batch mismatch: expected={expected}, "
                    f"serial={serial}, parallel={parallel}"
                )
            graph_batch_cases += len(chunk)
            chunk = []
    if chunk and graph_batch_cases < max_batch_cases:
        expected = [nx.is_planar(H) for H in chunk]
        serial = boost.batch_graph_planarity(chunk, workers=1)
        parallel = boost.batch_graph_planarity(chunk, workers=parallel_workers)
        if serial != expected or parallel != expected:
            raise AssertionError("v0.11 final generic graph-batch mismatch.")
        graph_batch_cases += len(chunk)

    kuratowski_cases = 0
    for gi, G in enumerate(atlas[:max_atlas_graphs]):
        if kuratowski_cases >= max_kuratowski_cases:
            break
        if nx.is_planar(G):
            continue
        cert = boost.kuratowski_edges(G)
        if not cert:
            raise AssertionError(f"Missing Kuratowski certificate on nonplanar atlas graph {gi}.")
        K = nx.Graph()
        for e in cert:
            u, v = tuple(e)
            K.add_edge(u, v)
        if nx.is_planar(K):
            raise AssertionError(
                f"Returned Kuratowski edge set is planar on atlas graph {gi}."
            )
        kuratowski_cases += 1

    return {
        "ordinary_planarity_graphs": checked,
        "batch_split_cases": batch_cases,
        "prefix_batch_cases": prefix_batch_cases,
        "generic_graph_batch_cases": graph_batch_cases,
        "kuratowski_certificates": kuratowski_cases,
        "openmp_enabled": boost.openmp_enabled,
        "parallel_workers_tested": parallel_workers,
        "parallel_threshold": boost.parallel_threshold,
        "status": "PASS",
        "backend": "boost",
    }


@dataclass(frozen=True)
class PartialGraphUpdate:
    """Exact local edit used to update/reverse the conservative partial graph."""

    x: Hashable
    old_left: Hashable
    old_right: Hashable
    current_left: Hashable
    current_right: Hashable
    close_stage: bool


class BacktrackingSearch:
    """v0.8 exhaustive search with proved-safe prefix/minor pruning.

    Safe prune rules are: published C6 relative-order necessity, nonplanarity
    of the monotone prefix graph, optional nonplanarity of the stronger
    locked-prefix minor, and full augmented-graph planarity at leaves.
    Reordering, batching, and parallelism change execution only.
    """

    def __init__(
        self,
        G: ThrackleGraph,
        max_recursive_calls: Optional[int] = None,
        time_limit_seconds: Optional[float] = None,
        *,
        use_c6_restriction: bool = True,
        branch_order: str = "constrained",
        use_screening: bool = True,
        use_lookahead: bool = False,
        incremental_partial: bool = True,
        debug: bool = False,
        use_cache: bool = False,
        progress_interval_seconds: Optional[float] = None,
        progress_mode: str = "auto",
        graph_label: Optional[str] = None,
        planarity_backend: str = "auto",
        use_batch_screening: bool = True,
        planarity_workers: Optional[int] = None,
        use_kuratowski_cache: bool = False,
        kuratowski_cache_limit: int = 128,
        activation_order: str = "euler",
        custom_activation_order: Optional[Sequence[int]] = None,
        use_locked_prefix_pruning: bool = True,
    ):
        if branch_order not in {"natural", "constrained"}:
            raise ValueError("branch_order must be 'natural' or 'constrained'.")
        if progress_mode not in {"auto", "single", "line", "dashboard"}:
            raise ValueError(
                "progress_mode must be auto, single, line, or dashboard."
            )
        if use_lookahead and not use_screening:
            # Lookahead is defined as screening the next decision state.
            use_lookahead = False
        if use_cache and use_screening:
            raise ValueError(
                "The legacy failed-state cache is not enabled together with "
                "v0.8.1 forward screening. Use --no-screening with --cache. "
                "Lookahead already reuses its exact child-state screen without "
                "the global cache."
            )

        self.G = G
        self.use_c6_restriction = use_c6_restriction
        if activation_order not in {"euler", "optimized", "custom"}:
            raise ValueError("activation_order must be 'euler', 'optimized', or 'custom'.")
        self.activation_order_mode = activation_order
        euler_order, euler_oriented = G.euler_walk()
        if activation_order == "euler":
            self.order = list(euler_order)
            self.oriented = dict(euler_oriented)
        elif activation_order == "custom":
            if custom_activation_order is None:
                raise ValueError("custom_activation_order is required when activation_order='custom'.")
            order = list(custom_activation_order)
            expected = set(G.edge_by_id)
            if len(order) != len(expected) or set(order) != expected:
                raise ValueError("custom_activation_order must contain every edge ID exactly once.")
            self.order = order
            self.oriented = dict(euler_oriented)
        else:
            self.order = self._optimized_activation_order()
            self.oriented = dict(euler_oriented)
        self.edge_position = {eid: i for i, eid in enumerate(self.order)}
        self.active_prefixes = [
            tuple(self.order[: i + 1]) for i in range(len(self.order))
        ]
        self.pi: Pi = {e.id: [] for e in G.edges}

        self.max_recursive_calls = max_recursive_calls
        self.time_limit_seconds = time_limit_seconds
        self.use_c6_restriction = use_c6_restriction
        self.branch_order = branch_order
        self.use_screening = use_screening
        self.use_lookahead = use_lookahead
        self.incremental_partial = incremental_partial
        self.use_locked_prefix_pruning = bool(use_locked_prefix_pruning)
        self.debug = debug
        self.use_cache = use_cache
        self.failed_cache = set()
        self.progress_interval_seconds = progress_interval_seconds
        self.progress_mode = progress_mode
        self.graph_label = graph_label or "graph"
        self.planarity = _make_planarity_backend(planarity_backend)
        cpu_auto = max(1, min(4, os.cpu_count() or 1))
        self.planarity_workers = cpu_auto if planarity_workers is None else max(1, int(planarity_workers))
        if not getattr(self.planarity, "openmp_enabled", False):
            self.planarity_workers = 1
        self.use_kuratowski_cache = bool(
            use_kuratowski_cache and hasattr(self.planarity, "kuratowski_edges")
        )
        self.kuratowski_cache_limit = max(0, int(kuratowski_cache_limit))
        self.kuratowski_conflicts = []
        self._kuratowski_conflict_set = set()
        self.use_batch_screening = bool(
            use_batch_screening
            and hasattr(self.planarity, "batch_prefix_planarity")
            and self.incremental_partial
            and not self.debug
        )

        self.started = 0.0
        self.last_progress = 0.0
        self.last_report_time = 0.0
        self.last_report_resolved = 0
        self._single_line_active = False
        self.witness: Optional[Pi] = None
        self.current_modeled_crossings = 0
        self.current_edge_index = 0

        # Precompute all crossing-vertex names and direct two-dimensional lookup.
        self.crossing_cache: Dict[Tuple[int, int], Hashable] = {}
        self.crossing_for: Dict[int, Dict[int, Hashable]] = {
            e.id: {} for e in G.edges
        }
        for e in G.edges:
            for f in G._nonincident[e.id]:
                pair = tuple(sorted((e.id, f)))
                x = self.crossing_cache.get(pair)
                if x is None:
                    x = crossing_vertex(*pair)
                    self.crossing_cache[pair] = x
                self.crossing_for[e.id][f] = x

        self.oriented_start = {eid: uv[0] for eid, uv in self.oriented.items()}
        self.oriented_end = {eid: uv[1] for eid, uv in self.oriented.items()}

        # For each activation stage, which older nonincident edges must the
        # current edge cross? This is fixed by the Euler order.
        self.older_required: List[Tuple[int, ...]] = []
        self.insertion_slots: Dict[Tuple[int, int], int] = {}
        for i, current in enumerate(self.order):
            older = tuple(
                e
                for e in G._nonincident[current]
                if self.edge_position[e] < i
            )
            self.older_required.append(older)
            for old in older:
                before_count = sum(
                    1
                    for f in G._nonincident[old]
                    if self.edge_position[f] < i
                )
                self.insertion_slots[(current, old)] = before_count + 1

        # Stage factor = number of search choices made while activating this
        # original edge when entered with none of its older crossings chosen.
        self.stage_factor: List[int] = []
        for i, current in enumerate(self.order):
            older = self.older_required[i]
            factor = factorial(len(older))
            for old in older:
                factor *= self.insertion_slots[(current, old)]
            self.stage_factor.append(factor)

        # suffix_after[i] = product of complete stage factors strictly after i.
        self.suffix_after = [1] * len(self.order)
        running = 1
        for i in range(len(self.order) - 1, -1, -1):
            self.suffix_after[i] = running
            running *= self.stage_factor[i]

        self.total_candidates = running
        direct_total = G.candidate_count()
        if self.total_candidates != direct_total:
            raise AssertionError(
                "Search-tree factorization does not match product |E_e|!. "
                f"tree={self.total_candidates}, direct={direct_total}"
            )

        self.total_required_crossings = G.total_required_crossings()
        self.stats = SearchStats(
            total_candidates=self.total_candidates,
            planarity_backend=self.planarity.name,
        )
        self.stats.planarity_workers = self.planarity_workers
        self.stats.openmp_enabled = bool(getattr(self.planarity, "openmp_enabled", False))
        self.stats.planarity_parallel_threshold = int(getattr(self.planarity, "parallel_threshold", 4))

        # Detect actual 6-cycles only. No C6 exists => rule is inert.
        self.six_cycles: List[SixCycle] = (
            G.simple_six_cycles() if use_c6_restriction else []
        )
        self.c6_constraints = self._prepare_c6_constraints()
        self.c6_pair_relevance = self._prepare_c6_pair_relevance()

        # Incremental partial graph starts as exactly the v0.3 conservative
        # partial planarization of the first active Euler edge.
        self.partial_H = nx.Graph()
        first = self.order[0]
        self.partial_H.add_edge(
            self.oriented_start[first],
            self.oriented_end[first],
        )
        self.partial_active_index = 0
        if self.debug and self.incremental_partial:
            self._assert_partial_graph_matches(0)

    # ---------- fixed search-space arithmetic ----------

    def _subtree_size(self, edge_index: int, remaining: Sequence[int]) -> int:
        """Exact number of complete Pi leaves below this recursive state."""
        current = self.order[edge_index]
        size = factorial(len(remaining)) * self.suffix_after[edge_index]
        for old in remaining:
            size *= self.insertion_slots[(current, old)]
        return size

    def _mark_resolved(self, count: int, cause: str):
        if count < 0:
            raise AssertionError("Cannot resolve a negative number of candidates.")
        self.stats.resolved_candidates += count
        if cause == "planarity":
            self.stats.planarity_pruned_candidates += count
        elif cause == "c6":
            self.stats.c6_pruned_candidates += count
        elif cause == "full":
            self.stats.full_candidates_resolved += count
        elif cause == "cache":
            pass
        else:
            raise ValueError(f"Unknown resolution cause {cause!r}.")

        if self.stats.resolved_candidates > self.total_candidates:
            raise AssertionError(
                "Coverage double-counted candidates: resolved exceeds total."
            )

    # ---------- C6 restriction (unchanged mathematical rule) ----------

    def _prepare_c6_constraints(self):
        prepared = {}
        for cyc in self.six_cycles:
            modes = [[], []]
            for i in range(6):
                e1 = cyc.edges[i]
                e2 = cyc.edges[(i + 1) % 6]
                e3 = cyc.edges[(i + 2) % 6]
                e4 = cyc.edges[(i + 3) % 6]

                def local_same(edge_index_in_cycle: int) -> bool:
                    host = cyc.edges[edge_index_in_cycle % 6]
                    u = cyc.vertices[edge_index_in_cycle % 6]
                    v = cyc.vertices[(edge_index_in_cycle + 1) % 6]
                    return self.oriented[host] == (u, v)

                modes[0].append((e1, e4, e3, local_same(i)))
                modes[0].append((e4, e1, e2, local_same(i + 3)))
                modes[1].append((e1, e3, e4, local_same(i)))
                modes[1].append((e4, e2, e1, local_same(i + 3)))

            deduped = []
            for mode in modes:
                seen = set()
                out = []
                for item in mode:
                    if item not in seen:
                        seen.add(item)
                        out.append(item)
                deduped.append(tuple(out))
            prepared[cyc.id] = tuple(deduped)
        return prepared

    def _prepare_c6_pair_relevance(self):
        relevant = set()
        for cyc in self.six_cycles:
            e = cyc.edges
            for i in range(6):
                relevant.add(
                    tuple(sorted((e[(i + 3) % 6], e[(i + 2) % 6])))
                )
                relevant.add(tuple(sorted((e[i], e[(i + 1) % 6]))))
            for a in e:
                for b in e:
                    if a < b and b in self.G._nonincident[a]:
                        relevant.add((a, b))
        return relevant

    def _mode_consistent(self, cycle_id: int, mode: int) -> bool:
        for host, first, second, local_same in self.c6_constraints[cycle_id][mode]:
            L = self.pi[host]
            if first not in L or second not in L:
                continue
            i_first = L.index(first)
            i_second = L.index(second)
            first_before_global = i_first < i_second
            first_before_local = (
                first_before_global if local_same else not first_before_global
            )
            if not first_before_local:
                return False
        return True

    def _c6_state_consistent(self) -> bool:
        if not self.six_cycles:
            return True
        self.stats.c6_consistency_checks += 1
        for cyc in self.six_cycles:
            if not (
                self._mode_consistent(cyc.id, 0)
                or self._mode_consistent(cyc.id, 1)
            ):
                self.stats.c6_prunes += 1
                return False
        return True

    # ---------- progress ----------

    def _elapsed(self) -> float:
        if self.started == 0.0:
            return 0.0
        return time.perf_counter() - self.started

    @staticmethod
    def _format_duration(seconds: float) -> str:
        seconds = max(0, int(seconds))
        h, rem = divmod(seconds, 3600)
        m, s = divmod(rem, 60)
        return f"{h:02d}:{m:02d}:{s:02d}"

    def _delta_percent_string(self, delta: int) -> str:
        if delta <= 0 or self.total_candidates <= 0:
            return "+0 pp"
        with localcontext() as ctx:
            ctx.prec = 30
            pp = Decimal(delta) * Decimal(100) / Decimal(self.total_candidates)
            return f"+{pp:.3E} pp"

    def _progress_values(self):
        now = time.perf_counter()
        elapsed = self._elapsed()
        tests = self.stats.partial_planarity_tests + self.stats.full_planarity_tests
        test_rate = tests / elapsed if elapsed > 0 else 0.0
        delta_pi = self.stats.resolved_candidates - self.last_report_resolved
        delta_t = now - self.last_report_time if self.last_report_time else elapsed
        delta_rate = delta_pi / delta_t if delta_t > 0 else 0.0
        return now, elapsed, tests, test_rate, delta_pi, delta_rate

    def _progress_snapshot(self) -> str:
        _, elapsed, tests, test_rate, delta_pi, delta_rate = self._progress_values()
        pct = coverage_percent_string(
            self.stats.resolved_candidates,
            self.total_candidates,
            precision=18,
        )
        return (
            f"{self.graph_label} | {self._format_duration(elapsed)} | cov {pct} | "
            f"Pi {_format_big_int(self.stats.resolved_candidates, 7)}/"
            f"{_format_big_int(self.total_candidates, 7)} | "
            f"dPi +{_format_big_int(delta_pi, 6)} "
            f"({self._delta_percent_string(delta_pi)}, "
            f"{_format_big_int(int(delta_rate), 5)}/s) | "
            f"tests {tests:,} ({test_rate:,.0f}/s) | "
            f"P:{self.stats.partial_nonplanar_prunes:,} "
            f"C6:{self.stats.c6_prunes:,} | "
            f"depth {self.current_modeled_crossings}/{self.total_required_crossings} "
            f"max {self.stats.max_modeled_crossings}/{self.total_required_crossings}"
        )

    def _progress_dashboard(self) -> str:
        _, elapsed, tests, test_rate, delta_pi, delta_rate = self._progress_values()
        return "\n".join(
            [
                f"Graph:                     {self.graph_label}",
                f"Runtime:                   {self._format_duration(elapsed)} ({elapsed:,.2f} s)",
                f"Search coverage:           {coverage_percent_string(self.stats.resolved_candidates, self.total_candidates, precision=18)}",
                f"Resolved complete Pi:      {_format_big_int(self.stats.resolved_candidates, 8)} / {_format_big_int(self.total_candidates, 8)}",
                f"Newly resolved since last: +{_format_big_int(delta_pi, 7)} ({self._delta_percent_string(delta_pi)})",
                f"Resolved Pi/sec (window):  {_format_big_int(int(delta_rate), 6)}",
                "",
                f"Recursive calls:           {self.stats.recursive_calls:,}",
                f"Planarity tests:           {tests:,}",
                f"Tests/sec:                 {test_rate:,.1f}",
                f"Partial nonplanar prunes:  {self.stats.partial_nonplanar_prunes:,}",
                f"C6 prunes:                 {self.stats.c6_prunes:,}",
                f"Backtracks:                {self.stats.backtracks:,}",
                f"Screened states:           {getattr(self.stats, 'screening_states', 0):,}",
                f"Lookahead states:          {getattr(self.stats, 'lookahead_states', 0):,}",
                "",
                f"Current crossings:         {self.current_modeled_crossings} / {self.total_required_crossings}",
                f"Deepest crossings:         {self.stats.max_modeled_crossings} / {self.total_required_crossings}",
                f"Active original edges:     {self.current_edge_index + 1} / {len(self.order)}",
                f"Detected C6 cycles:        {len(self.six_cycles) if self.use_c6_restriction else 0}",
            ]
        )

    def _resolved_progress_mode(self) -> str:
        mode = self.progress_mode
        if mode == "auto":
            mode = "single" if sys.stdout.isatty() else "line"
        return mode

    def _clear_notebook_output_if_possible(self) -> bool:
        """
        Clear the current notebook cell output when this code is running inside
        the same IPython/Jupyter kernel.

        If the program is being run as a separate subprocess (for example with
        !python in Colab), there is no direct notebook display handle in this
        process, so the caller falls back to ANSI terminal-style clearing.
        """
        try:
            from IPython import get_ipython
            shell = get_ipython()
            if shell is not None and getattr(shell, "kernel", None) is not None:
                from IPython.display import clear_output
                clear_output(wait=True)
                return True
        except Exception:
            pass
        return False

    def _maybe_report_progress(self, force: bool = False):
        if self.progress_interval_seconds is None:
            return
        now = time.perf_counter()
        if not force and now - self.last_progress < self.progress_interval_seconds:
            return

        mode = self._resolved_progress_mode()

        # v0.4.1 display rule:
        #   single -> the full old multi-line dashboard, refreshed in place
        #   line   -> the exact same dashboard, printed again below the last one
        #   dashboard -> legacy full-screen redraw behavior
        text = self._progress_dashboard()

        if mode == "single":
            # Prefer true notebook-output replacement when running in the same
            # Jupyter/IPython kernel. Otherwise use ANSI clear-screen + home,
            # which refreshes the same dashboard in a normal terminal and is
            # also understood by many notebook subprocess output renderers.
            if not self._clear_notebook_output_if_possible():
                print("\033[2J\033[H", end="")
            print(text, end="", flush=True)
            self._single_line_active = True
        elif mode == "dashboard":
            print("\033[2J\033[H" + text, end="", flush=True)
            self._single_line_active = True
        else:  # line
            print(text + "\n", flush=True)

        self.last_progress = now
        self.last_report_time = now
        self.last_report_resolved = self.stats.resolved_candidates

    def _close_progress_line(self):
        if self._single_line_active:
            print()
            self._single_line_active = False

    # ---------- conservative partial-graph maintenance ----------

    def _assert_partial_graph_matches(self, edge_index: int):
        if not self.incremental_partial:
            return
        if edge_index < 0:
            expected = nx.Graph()
        else:
            current = self.order[edge_index]
            current_complete = len(self.pi[current]) == len(self.older_required[edge_index])
            expected = build_prefix_planarization(
                self.G, self.pi, self.active_prefixes[edge_index], self.oriented,
                current_eid=current, current_complete=current_complete,
                validate=True, crossing_cache=self.crossing_cache,
            )
        if set(expected.nodes) != set(self.partial_H.nodes):
            raise AssertionError(
                f"Incremental prefix node set differs from rebuild at edge_index={edge_index}."
            )
        a = {frozenset(e) for e in expected.edges}
        b = {frozenset(e) for e in self.partial_H.edges}
        if a != b:
            raise AssertionError(
                f"Incremental prefix edge set differs from rebuild at edge_index={edge_index}."
            )

    def _activate_edge(self, edge_index: int):
        if edge_index != self.partial_active_index + 1:
            raise AssertionError(
                f"Nonsequential edge activation: have {self.partial_active_index}, requested {edge_index}."
            )
        eid = self.order[edge_index]
        if self.pi[eid]:
            raise AssertionError("A newly activated edge should have an empty crossing list.")
        if self.incremental_partial:
            u, v = self.oriented[eid]
            if self.older_required[edge_index]:
                self.partial_H.add_node(u)
            else:
                self.partial_H.add_edge(u, v)
        self.partial_active_index = edge_index
        if self.debug and self.incremental_partial:
            self._assert_partial_graph_matches(edge_index)

    def _deactivate_edge(self, edge_index: int):
        if edge_index != self.partial_active_index:
            raise AssertionError(
                f"Can only deactivate the newest active edge; have {self.partial_active_index}, requested {edge_index}."
            )
        eid = self.order[edge_index]
        if self.pi[eid]:
            raise AssertionError("Cannot deactivate an edge with modeled crossings still present.")
        if self.incremental_partial:
            u, v = self.oriented[eid]
            if self.older_required[edge_index]:
                if u in self.partial_H and self.partial_H.degree(u) == 0:
                    self.partial_H.remove_node(u)
            else:
                if not self.partial_H.has_edge(u, v):
                    raise AssertionError("Expected zero-crossing edge missing during deactivation.")
                self.partial_H.remove_edge(u, v)
                for node in (u, v):
                    if node in self.partial_H and self.partial_H.degree(node) == 0:
                        self.partial_H.remove_node(node)
        self.partial_active_index -= 1
        if self.debug and self.incremental_partial:
            self._assert_partial_graph_matches(self.partial_active_index)

    def _apply_choice(self, edge_index: int, old: int, pos: int) -> PartialGraphUpdate:
        current = self.order[edge_index]
        old_list = self.pi[old]
        cur_list = self.pi[current]
        if not (0 <= pos <= len(old_list)):
            raise AssertionError("Insertion position is outside the current older-edge list.")

        x = self.crossing_for[current][old]
        old_left = self.oriented_start[old] if pos == 0 else self.crossing_for[old][old_list[pos - 1]]
        old_right = self.oriented_end[old] if pos == len(old_list) else self.crossing_for[old][old_list[pos]]
        current_left = self.oriented_start[current] if not cur_list else self.crossing_for[current][cur_list[-1]]
        current_right = self.oriented_end[current]
        close_stage = (len(cur_list) + 1 == len(self.older_required[edge_index]))

        if self.incremental_partial:
            if not self.partial_H.has_edge(old_left, old_right):
                raise AssertionError("Older-edge segment missing before safe-prefix UPDATE.")
            self.partial_H.remove_edge(old_left, old_right)
            self.partial_H.add_edge(old_left, x)
            self.partial_H.add_edge(x, old_right)
            self.partial_H.add_edge(current_left, x)
            if close_stage:
                self.partial_H.add_edge(x, current_right)
            self.stats.incremental_graph_updates += 1

        old_list.insert(pos, current)
        cur_list.append(old)
        self.current_modeled_crossings += 1
        self.stats.max_modeled_crossings = max(self.stats.max_modeled_crossings, self.current_modeled_crossings)

        token = PartialGraphUpdate(
            x=x, old_left=old_left, old_right=old_right,
            current_left=current_left, current_right=current_right,
            close_stage=close_stage,
        )
        if self.debug and self.incremental_partial:
            self._assert_partial_graph_matches(edge_index)
        return token

    def _reverse_choice(self, edge_index: int, old: int, pos: int, token: PartialGraphUpdate):
        current = self.order[edge_index]
        removed_current = self.pi[current].pop()
        removed_from_old = self.pi[old].pop(pos)
        self.current_modeled_crossings -= 1
        if removed_current != old or removed_from_old != current:
            raise AssertionError("REVERSE_UPDATE failed to restore exact Pi state.")

        if self.incremental_partial:
            x = token.x
            expected = [
                (token.old_left, x), (x, token.old_right), (token.current_left, x)
            ]
            if token.close_stage:
                expected.append((x, token.current_right))
            for a, b in expected:
                if not self.partial_H.has_edge(a, b):
                    raise AssertionError("Safe-prefix edge missing during REVERSE_UPDATE.")
                self.partial_H.remove_edge(a, b)
            if token.close_stage and token.current_right in self.partial_H and self.partial_H.degree(token.current_right) == 0:
                self.partial_H.remove_node(token.current_right)
            if x in self.partial_H:
                if self.partial_H.degree(x) != 0:
                    raise AssertionError("Crossing vertex still has edges after REVERSE_UPDATE.")
                self.partial_H.remove_node(x)
            self.partial_H.add_edge(token.old_left, token.old_right)

        self.stats.backtracks += 1
        if self.debug and self.incremental_partial:
            self._assert_partial_graph_matches(edge_index)

    def _stage_factor_for_prefix(self, prefix: Sequence[int], current: int) -> int:
        """Exact stage factor if ``current`` is activated after ``prefix``."""
        active = set(prefix)
        older = [e for e in self.G._nonincident[current] if e in active]
        factor = factorial(len(older))
        for old in older:
            before_count = sum(1 for f in self.G._nonincident[old] if f in active)
            factor *= before_count + 1
        return factor

    def _optimized_activation_order(self) -> List[int]:
        """
        Deterministic v0.8.1 activation-order heuristic.

        Mathematical semantics are unchanged: every edge is activated exactly once,
        and the same complete Pi systems are represented.  The heuristic keeps one
        detected C6 together at the front (so the published C6 restriction can act
        early), then greedily chooses the next edge with the smallest immediate
        stage factor. For DB(6,8,-2), v0.8.1 uses a separately benchmarked
        target-specific order selected by fresh bounded-search comparisons.
        The selection changes traversal only; it does not skip or pre-resolve branches. Ties in the generic heuristic prefer edges with more nonincident
        relationships to still-unactivated edges, then stable edge ID.
        """
        all_ids = [e.id for e in self.G.edges]

        cycles = self.G.simple_six_cycles() if self.use_c6_restriction else []
        prefix: List[int] = []
        remaining = set(all_ids)

        if cycles:
            # Choose the C6 with the smallest stable edge-ID signature.  Within the
            # cycle, use its local cyclic order; this is deterministic and exposes
            # all six C6 edges as early as possible.
            cyc = min(cycles, key=lambda c: tuple(sorted(c.edges)))
            for eid in cyc.edges:
                if eid in remaining:
                    prefix.append(eid)
                    remaining.remove(eid)

        while remaining:
            def score(eid: int):
                stage = self._stage_factor_for_prefix(prefix, eid)
                future_pressure = -sum(1 for f in self.G._nonincident[eid] if f in remaining and f != eid)
                return (stage, future_pressure, eid)
            nxt = min(remaining, key=score)
            prefix.append(nxt)
            remaining.remove(nxt)
        return prefix

    # ---------- planarity / screening / search ----------

    def _check_limits(self):
        if (
            self.max_recursive_calls is not None
            and self.stats.recursive_calls > self.max_recursive_calls
        ):
            raise SearchLimitReached(
                f"Reached recursive-call limit {self.max_recursive_calls:,}."
            )
        if (
            self.time_limit_seconds is not None
            and self._elapsed() > self.time_limit_seconds
        ):
            raise SearchLimitReached(
                f"Reached time limit {self.time_limit_seconds:g} seconds."
            )

    def _state_key(self, edge_index: int, remaining: Sequence[int]):
        active = self.active_prefixes[edge_index]
        return (
            edge_index,
            tuple(remaining),
            tuple((eid, tuple(self.pi[eid])) for eid in active),
        )

    def _partial_planar(self, edge_index: int) -> bool:
        self.stats.partial_planarity_tests += 1
        self.stats.depth_planarity_tests[edge_index] = self.stats.depth_planarity_tests.get(edge_index, 0) + 1
        if self.incremental_partial:
            if self.debug:
                self._assert_partial_graph_matches(edge_index)
            H = self.partial_H
        else:
            self.stats.partial_graph_rebuilds += 1
            current = self.order[edge_index]
            current_complete = len(self.pi[current]) == len(self.older_required[edge_index])
            H = build_prefix_planarization(
                self.G, self.pi, self.active_prefixes[edge_index], self.oriented,
                current_eid=current, current_complete=current_complete,
                validate=self.debug, crossing_cache=self.crossing_cache,
            )
        t0 = time.perf_counter()
        planar = self.planarity.is_planar(H)
        self.stats.planarity_seconds += time.perf_counter() - t0
        if not planar:
            self.stats.partial_nonplanar_prunes += 1
            self.stats.depth_nonplanar_prunes[edge_index] = self.stats.depth_nonplanar_prunes.get(edge_index, 0) + 1
        return planar

    def _locked_prefix_planar(self, edge_index: int) -> bool:
        """Test the stronger locked-prefix minor; nonplanarity is safely fatal."""
        current = self.order[edge_index]
        current_complete = len(self.pi[current]) == len(self.older_required[edge_index])
        if current_complete:
            # Strongest safe checkpoint: the full Fulek--Pach augmented graph
            # of the completed active-edge subgraph.
            H = build_active_augmented_minor(
                self.G, self.pi, self.active_prefixes[edge_index], self.oriented,
                validate=self.debug, crossing_cache=self.crossing_cache,
            )
        else:
            H = build_locked_prefix_minor(
                self.G, self.pi, self.active_prefixes[edge_index], self.oriented,
                current_eid=current, current_complete=False,
                validate=self.debug, crossing_cache=self.crossing_cache,
            )
        self.stats.partial_planarity_tests += 1
        self.stats.locked_prefix_tests += 1
        self.stats.depth_planarity_tests[edge_index] = self.stats.depth_planarity_tests.get(edge_index, 0) + 1
        t0 = time.perf_counter()
        planar = self.planarity.is_planar(H)
        self.stats.planarity_seconds += time.perf_counter() - t0
        if not planar:
            self.stats.partial_nonplanar_prunes += 1
            self.stats.locked_prefix_prunes += 1
            self.stats.depth_nonplanar_prunes[edge_index] = self.stats.depth_nonplanar_prunes.get(edge_index, 0) + 1
        return planar

    def _complete_candidate_planar(self) -> bool:
        self.stats.full_planarity_tests += 1
        H = build_augmented_graph(
            self.G,
            self.pi,
            oriented=self.oriented,
            validate=self.debug,
            crossing_cache=self.crossing_cache,
        )
        t0 = time.perf_counter()
        planar = self.planarity.is_planar(H)
        self.stats.planarity_seconds += time.perf_counter() - t0
        return planar

    def _ordered_remaining(self, current: int, remaining: Sequence[int]):
        if self.branch_order == "natural":
            return tuple(remaining)

        def score(old):
            pair = tuple(sorted((current, old)))
            c6_priority = 0 if pair in self.c6_pair_relevance else 1
            return (
                c6_priority,
                self.insertion_slots[(current, old)],
                old,
            )

        return tuple(sorted(remaining, key=score))

    def _debug_partition_check(self, edge_index: int, remaining: Sequence[int]):
        if not self.debug or not remaining:
            return
        current = self.order[edge_index]
        parent = self._subtree_size(edge_index, remaining)
        children = 0
        for old in remaining:
            child_remaining = tuple(x for x in remaining if x != old)
            child = self._subtree_size(edge_index, child_remaining)
            children += self.insertion_slots[(current, old)] * child
        if children != parent:
            raise AssertionError(
                f"Subtree partition mismatch: parent={parent}, children={children}."
            )

    def _choice_candidates(
        self,
        edge_index: int,
        remaining: Sequence[int],
    ):
        current = self.order[edge_index]
        rank = 0
        for old in self._ordered_remaining(current, remaining):
            child_remaining = tuple(x for x in remaining if x != old)
            child_subtree = self._subtree_size(edge_index, child_remaining)
            slot_count = self.insertion_slots[(current, old)]
            if self.debug and slot_count != len(self.pi[old]) + 1:
                raise AssertionError(
                    f"Precomputed insertion slots disagree for ({current},{old}): "
                    f"precomputed={slot_count}, actual={len(self.pi[old]) + 1}."
                )
            for pos in range(slot_count):
                yield old, pos, child_remaining, child_subtree, rank
                rank += 1

    def _candidate_graph_modification(self, edge_index: int, old: int, pos: int):
        """Exact local edit caused by one safe-prefix choice."""
        current = self.order[edge_index]
        old_list = self.pi[old]
        cur_list = self.pi[current]
        x = self.crossing_for[current][old]
        old_left = self.oriented_start[old] if pos == 0 else self.crossing_for[old][old_list[pos - 1]]
        old_right = self.oriented_end[old] if pos == len(old_list) else self.crossing_for[old][old_list[pos]]
        current_left = self.oriented_start[current] if not cur_list else self.crossing_for[current][cur_list[-1]]
        current_right = self.oriented_end[current]
        close_stage = (len(cur_list) + 1 == len(self.older_required[edge_index]))
        return old_left, old_right, current_left, x, current_right, close_stage

    def _temp_pi_choice(self, edge_index: int, old: int, pos: int):
        """Apply/reverse only the Pi-list part of a choice for cheap C6 filtering."""
        current = self.order[edge_index]
        self.pi[old].insert(pos, current)
        self.pi[current].append(old)

    def _temp_pi_reverse(self, edge_index: int, old: int, pos: int):
        current = self.order[edge_index]
        a = self.pi[current].pop()
        b = self.pi[old].pop(pos)
        if a != old or b != current:
            raise AssertionError("Temporary Pi screening failed to restore exact state.")

    @staticmethod
    def _normalized_graph_edge(u, v):
        return frozenset((u, v))

    def _candidate_child_edge_set(self, mod):
        a, b, c, x, d, close_stage = mod
        edges = {self._normalized_graph_edge(u, v) for u, v in self.partial_H.edges}
        edges.discard(self._normalized_graph_edge(a, b))
        edges.update({
            self._normalized_graph_edge(a, x), self._normalized_graph_edge(x, b),
            self._normalized_graph_edge(c, x),
        })
        if close_stage:
            edges.add(self._normalized_graph_edge(x, d))
        return edges

    def _candidate_hits_kuratowski_cache(self, mod) -> bool:
        if not self.use_kuratowski_cache or not self.kuratowski_conflicts:
            return False
        child_edges = self._candidate_child_edge_set(mod)
        for cert in self.kuratowski_conflicts:
            if cert.issubset(child_edges):
                self.stats.kuratowski_cache_hits += 1
                return True
        return False

    def _learn_kuratowski_from_candidate(self, mod) -> None:
        if (not self.use_kuratowski_cache or
                len(self.kuratowski_conflicts) >= self.kuratowski_cache_limit):
            return
        a, b, c, x, d, close_stage = mod
        H = self.partial_H.copy()
        if not H.has_edge(a, b):
            return
        H.remove_edge(a, b)
        H.add_edges_from([(a, x), (x, b), (c, x)])
        if close_stage:
            H.add_edge(x, d)
        t0 = time.perf_counter()
        cert = self.planarity.kuratowski_edges(H)
        self.stats.kuratowski_certificate_seconds += time.perf_counter() - t0
        if cert and cert not in self._kuratowski_conflict_set:
            self._kuratowski_conflict_set.add(cert)
            self.kuratowski_conflicts.append(cert)
            self.stats.kuratowski_certificates_learned += 1
            self.stats.kuratowski_cached_edges_total += len(cert)

    def _screen_state(
        self,
        edge_index: int,
        remaining: Tuple[int, ...],
    ) -> ScreenResult:
        """
        Test every immediate child using the same verified C6 and conservative
        partial-planarity conditions as v0.5.1.  With Boost, v0.8.1 evaluates
        the planarity portion as one compiled batch per state.
        """
        if not self.use_batch_screening:
            return self._screen_state_serial(edge_index, remaining)

        self.stats.screening_states += 1
        parent_size = self._subtree_size(edge_index, remaining)
        total_choices = 0
        pruned_choices = 0
        surviving_weight = 0
        resolved_weight = 0
        pending = []  # (SearchChoice, graph_mod)

        for old, pos, child_remaining, child_subtree, rank in self._choice_candidates(edge_index, remaining):
            total_choices += 1
            self.stats.screening_candidates += 1
            failed = False

            if self.use_c6_restriction and self.six_cycles:
                self._temp_pi_choice(edge_index, old, pos)
                try:
                    if not self._c6_state_consistent():
                        self._mark_resolved(child_subtree, "c6")
                        resolved_weight += child_subtree
                        pruned_choices += 1
                        failed = True
                finally:
                    self._temp_pi_reverse(edge_index, old, pos)

            if not failed:
                mod = self._candidate_graph_modification(edge_index, old, pos)
                if self._candidate_hits_kuratowski_cache(mod):
                    self._mark_resolved(child_subtree, "planarity")
                    resolved_weight += child_subtree
                    pruned_choices += 1
                    failed = True
                else:
                    pending.append((
                        SearchChoice(
                            old=old, pos=pos, child_remaining=child_remaining,
                            child_subtree=child_subtree, base_rank=rank,
                        ),
                        mod,
                    ))

        choices: List[SearchChoice] = []
        if pending:
            mods = [mod for _, mod in pending]
            t0 = time.perf_counter()
            answers = self.planarity.batch_prefix_planarity(self.partial_H, mods, workers=self.planarity_workers)
            dt = time.perf_counter() - t0
            self.stats.batch_planarity_calls += 1
            self.stats.batch_planarity_candidates += len(pending)
            self.stats.batch_planarity_seconds += dt
            self.stats.planarity_seconds += dt
            self.stats.depth_batch_calls[edge_index] = self.stats.depth_batch_calls.get(edge_index, 0) + 1
            self.stats.partial_planarity_tests += len(pending)
            self.stats.depth_planarity_tests[edge_index] = self.stats.depth_planarity_tests.get(edge_index, 0) + len(pending)

            learned_this_batch = False
            for (choice, mod), planar in zip(pending, answers):
                if not planar:
                    if self.use_kuratowski_cache and not learned_this_batch:
                        self._learn_kuratowski_from_candidate(mod)
                        learned_this_batch = True
                    self.stats.partial_nonplanar_prunes += 1
                    self.stats.depth_nonplanar_prunes[edge_index] = self.stats.depth_nonplanar_prunes.get(edge_index, 0) + 1
                    self._mark_resolved(choice.child_subtree, "planarity")
                    resolved_weight += choice.child_subtree
                    pruned_choices += 1
                else:
                    choices.append(choice)
                    surviving_weight += choice.child_subtree
                    self.stats.screening_survivors += 1

        if self.debug and resolved_weight + surviving_weight != parent_size:
            raise AssertionError(
                "Forward-screen partition does not equal parent subtree: "
                f"resolved={resolved_weight}, surviving={surviving_weight}, parent={parent_size}."
            )

        self._check_limits()
        self._maybe_report_progress()
        return ScreenResult(
            choices=choices,
            total_choices=total_choices,
            pruned_choices=pruned_choices,
            surviving_weight=surviving_weight,
        )

    def _screen_state_serial(
        self,
        edge_index: int,
        remaining: Tuple[int, ...],
    ) -> ScreenResult:
        """v0.5.1-compatible serial screening path used for verification/fallback."""
        self.stats.screening_states += 1
        parent_size = self._subtree_size(edge_index, remaining)
        choices: List[SearchChoice] = []
        total_choices = 0
        pruned_choices = 0
        surviving_weight = 0
        resolved_weight = 0

        for old, pos, child_remaining, child_subtree, rank in self._choice_candidates(edge_index, remaining):
            total_choices += 1
            self.stats.screening_candidates += 1
            token = self._apply_choice(edge_index, old, pos)
            failed = False

            if self.use_c6_restriction and self.six_cycles:
                if not self._c6_state_consistent():
                    self._mark_resolved(child_subtree, "c6")
                    resolved_weight += child_subtree
                    failed = True

            if not failed and not self._partial_planar(edge_index):
                self._mark_resolved(child_subtree, "planarity")
                resolved_weight += child_subtree
                failed = True

            if failed:
                pruned_choices += 1
            else:
                choice = SearchChoice(
                    old=old,
                    pos=pos,
                    child_remaining=child_remaining,
                    child_subtree=child_subtree,
                    base_rank=rank,
                )
                choices.append(choice)
                surviving_weight += child_subtree
                self.stats.screening_survivors += 1

            self._reverse_choice(edge_index, old, pos, token)
            if total_choices % 32 == 0:
                self._check_limits(); self._maybe_report_progress()

        if self.debug and resolved_weight + surviving_weight != parent_size:
            raise AssertionError(
                "Forward-screen partition does not equal parent subtree: "
                f"resolved={resolved_weight}, surviving={surviving_weight}, parent={parent_size}."
            )
        return ScreenResult(
            choices=choices,
            total_choices=total_choices,
            pruned_choices=pruned_choices,
            surviving_weight=surviving_weight,
        )

    def _normalize_for_lookahead(
        self,
        edge_index: int,
        remaining: Tuple[int, ...],
    ):
        """
        Temporarily activate empty intermediate stages until the next actual
        crossing decision or a complete leaf is reached.

        Returns (normalized_edge_index, normalized_remaining, activated_indices,
        is_leaf).
        """
        i = edge_index
        rem = remaining
        activated: List[int] = []
        while not rem and i + 1 < len(self.order):
            i += 1
            self._activate_edge(i)
            activated.append(i)
            rem = self.older_required[i]
        is_leaf = (not rem) and (i + 1 == len(self.order))
        return i, rem, activated, is_leaf

    def _score_lookahead_choice(
        self,
        edge_index: int,
        choice: SearchChoice,
    ) -> bool:
        """
        Screen exactly one decision level below a surviving immediate choice.

        Returns True if the choice still has at least one possible continuation
        (or directly reaches a complete leaf). Returns False if lookahead safely
        resolves its entire subtree using the same C6/partial-planarity tests.
        """
        token = self._apply_choice(edge_index, choice.old, choice.pos)
        i, rem, activated, is_leaf = self._normalize_for_lookahead(
            edge_index, choice.child_remaining
        )

        keep = True
        if is_leaf:
            # Do not run the full augmented-graph leaf test during lookahead;
            # recursion handles it in the normal verified success path.
            choice.lookahead_viable_count = 0
            choice.lookahead_surviving_weight = choice.child_subtree
        else:
            self.stats.lookahead_states += 1
            state_key = self._state_key(i, rem)
            screen = self._screen_state(i, rem)
            choice.lookahead_screen = screen
            choice.lookahead_state_key = state_key
            choice.lookahead_viable_count = len(screen.choices)
            choice.lookahead_surviving_weight = screen.surviving_weight
            if not screen.choices:
                self.stats.lookahead_dead_ends += 1
                keep = False
                if self.debug and screen.surviving_weight != 0:
                    raise AssertionError("Dead lookahead state retained positive surviving weight.")

        for idx in reversed(activated):
            self._deactivate_edge(idx)
        self._reverse_choice(edge_index, choice.old, choice.pos, token)
        return keep

    def _order_screened_choices(
        self,
        edge_index: int,
        choices: List[SearchChoice],
    ) -> List[SearchChoice]:
        if not self.use_lookahead or len(choices) <= 1:
            return choices

        survivors = []
        for choice in choices:
            if self._score_lookahead_choice(edge_index, choice):
                survivors.append(choice)
            self._check_limits()
            self._maybe_report_progress()

        # Most constrained first. This is ONLY an ordering rule.
        survivors.sort(
            key=lambda c: (
                c.lookahead_viable_count
                if c.lookahead_viable_count is not None
                else 10**18,
                c.lookahead_surviving_weight
                if c.lookahead_surviving_weight is not None
                else c.child_subtree,
                c.base_rank,
            )
        )
        return survivors

    def _search_edge_v03_style(
        self,
        edge_index: int,
        remaining: Tuple[int, ...],
    ) -> bool:
        """Compatibility path: v0.3-style immediate test then recurse."""
        current = self.order[edge_index]
        ordered = self._ordered_remaining(current, remaining)
        for old in ordered:
            child_remaining = tuple(x for x in remaining if x != old)
            child_subtree = self._subtree_size(edge_index, child_remaining)
            slot_count = self.insertion_slots[(current, old)]
            for pos in range(slot_count):
                token = self._apply_choice(edge_index, old, pos)
                failed = False
                if self.use_c6_restriction and self.six_cycles:
                    if not self._c6_state_consistent():
                        self._mark_resolved(child_subtree, "c6")
                        failed = True
                if not failed and not self._partial_planar(edge_index):
                    self._mark_resolved(child_subtree, "planarity")
                    failed = True
                if not failed:
                    if self._search_edge(edge_index, child_remaining):
                        return True
                self._reverse_choice(edge_index, old, pos, token)
                if self.stats.backtracks % 64 == 0:
                    self._check_limits()
                    self._maybe_report_progress()
        return False

    def _search_edge(
        self,
        edge_index: int,
        remaining: Optional[Tuple[int, ...]] = None,
        *,
        pre_screened: Optional[ScreenResult] = None,
        pre_screen_key: Optional[Tuple] = None,
    ) -> bool:
        self.stats.recursive_calls += 1
        self.current_edge_index = edge_index
        self._check_limits()
        if self.stats.recursive_calls % 128 == 0:
            self._maybe_report_progress()

        if remaining is None:
            remaining = self.older_required[edge_index]

        # Strong safe v0.8 pruning.  The locked-prefix graph is a minor of every
        # completion of the current state.  A nonplanar result therefore resolves
        # the entire subtree represented by this recursive state.
        if self.use_locked_prefix_pruning and self.current_modeled_crossings:
            if not self._locked_prefix_planar(edge_index):
                count = pre_screened.surviving_weight if pre_screened is not None else self._subtree_size(edge_index, remaining)
                self._mark_resolved(count, "planarity")
                return False

        active_count = edge_index + 1
        if active_count > self.stats.max_active_edges:
            self.stats.max_active_edges = active_count
        if self.current_modeled_crossings > self.stats.max_modeled_crossings:
            self.stats.max_modeled_crossings = self.current_modeled_crossings

        if self.use_cache:
            key = self._state_key(edge_index, remaining)
            if key in self.failed_cache:
                self.stats.cache_hits += 1
                self._mark_resolved(
                    self._subtree_size(edge_index, remaining), "cache"
                )
                return False

        self._debug_partition_check(edge_index, remaining)

        if not remaining:
            if edge_index + 1 == len(self.order):
                if pre_screened is not None:
                    raise AssertionError("A complete leaf cannot consume a pre-screened decision state.")
                if self.debug:
                    validate_full_pi(self.G, self.pi)

                planar = self._complete_candidate_planar()
                self._mark_resolved(1, "full")
                if planar:
                    validate_full_pi(self.G, self.pi)
                    H_check = build_augmented_graph(
                        self.G,
                        self.pi,
                        oriented=self.oriented,
                        validate=True,
                        crossing_cache=self.crossing_cache,
                    )
                    if not nx.is_planar(H_check):
                        raise AssertionError(
                            "Witness failed independent final validation."
                        )
                    self.witness = {
                        eid: list(order) for eid, order in self.pi.items()
                    }
                    return True

                if self.use_cache:
                    self.failed_cache.add(self._state_key(edge_index, remaining))
                return False

            next_index = edge_index + 1
            self._activate_edge(next_index)
            succeeded = self._search_edge(
                next_index,
                self.older_required[next_index],
                pre_screened=pre_screened,
                pre_screen_key=pre_screen_key,
            )
            if not succeeded:
                self._deactivate_edge(next_index)
                self.current_edge_index = edge_index
            return succeeded

        if not self.use_screening:
            succeeded = self._search_edge_v03_style(edge_index, remaining)
            if not succeeded and self.use_cache:
                self.failed_cache.add(self._state_key(edge_index, remaining))
            return succeeded

        # Forward screening. A lookahead-generated screen is reused only after
        # verifying the EXACT current state key.
        if pre_screened is not None:
            current_key = self._state_key(edge_index, remaining)
            if current_key != pre_screen_key:
                raise AssertionError(
                    "Lookahead screening result was offered to a different partial state."
                )
            screen = pre_screened
            self.stats.lookahead_reused_screens += 1
        else:
            screen = self._screen_state(edge_index, remaining)

        choices = self._order_screened_choices(edge_index, screen.choices)
        for choice in choices:
            token = self._apply_choice(
                edge_index, choice.old, choice.pos
            )
            succeeded = self._search_edge(
                edge_index,
                choice.child_remaining,
                pre_screened=choice.lookahead_screen,
                pre_screen_key=choice.lookahead_state_key,
            )
            if succeeded:
                return True
            self._reverse_choice(
                edge_index, choice.old, choice.pos, token
            )
            if self.stats.backtracks % 64 == 0:
                self._check_limits()
                self._maybe_report_progress()

        if self.use_cache:
            self.failed_cache.add(self._state_key(edge_index, remaining))
        return False

    def run(self) -> SearchResult:
        self.started = time.perf_counter()
        self.last_progress = self.started
        self.last_report_time = self.started
        self.last_report_resolved = self.stats.resolved_candidates

        try:
            # Display-only: show the initial 0% dashboard before screening can
            # resolve a large fraction of the search space.
            self._maybe_report_progress(force=True)
            found = self._search_edge(0, self.older_required[0])
            self.stats.elapsed_seconds = self._elapsed()
            self._maybe_report_progress(force=True)
            self._close_progress_line()

            if found:
                return SearchResult(
                    status="THRACKLEABLE",
                    witness_pi=self.witness,
                    stats=self.stats,
                    reason=(
                        "Found a complete Pi whose full augmented Fulek–Pach graph is planar."
                    ),
                )

            if self.stats.resolved_candidates != self.total_candidates:
                raise AssertionError(
                    "Search returned NONTHRACKLEABLE without 100% exact coverage: "
                    f"resolved={self.stats.resolved_candidates}, total={self.total_candidates}."
                )

            return SearchResult(
                status="NONTHRACKLEABLE",
                witness_pi=None,
                stats=self.stats,
                reason=(
                    "Exhausted every backtracking branch. Exact resolved search-space "
                    "coverage is 100%."
                ),
            )

        except SearchLimitReached as exc:
            self.stats.elapsed_seconds = self._elapsed()
            self._maybe_report_progress(force=True)
            self._close_progress_line()
            return SearchResult(
                status="INCONCLUSIVE",
                witness_pi=None,
                stats=self.stats,
                reason=str(exc),
            )


def exhaustive_find_witness_v01_style(
    G: ThrackleGraph,
    max_candidates: int = 100000,
):
    total = G.candidate_count()
    if total > max_candidates:
        raise RuntimeError(f"Would require {total:,} complete Pi systems.")

    choices = [
        list(permutations(G.nonincident_edges(e.id)))
        for e in G.edges
    ]
    for checked, candidate in enumerate(product(*choices), start=1):
        pi = {e.id: list(candidate[e.id]) for e in G.edges}
        H = build_augmented_graph(G, pi)
        if nx.is_planar(H):
            return pi, checked, total
    return None, total, total


def _witness_satisfies_c6_rule(G: ThrackleGraph, pi: Pi) -> bool:
    """Independent helper used by the self-test on C6."""
    search = BacktrackingSearch(
        G,
        use_c6_restriction=True,
        branch_order="natural",
        debug=True,
        progress_interval_seconds=None,
    )
    search.pi = {eid: list(L) for eid, L in pi.items()}
    return search._c6_state_consistent()


def _stage_factor_for_order_prefix(G: ThrackleGraph, prefix: Sequence[int], current: int) -> int:
    active = set(prefix)
    older = [e for e in G._nonincident[current] if e in active]
    factor = factorial(len(older))
    for old in older:
        before_count = sum(1 for f in G._nonincident[old] if f in active)
        factor *= before_count + 1
    return factor


def db682_candidate_activation_orders(G: Optional[ThrackleGraph] = None, limit: int = 8) -> List[List[int]]:
    """Return deterministic low-bottleneck orders with the unique C6 first.

    This is execution-order optimization only.  All 6! tail permutations are
    considered; they are ranked lexicographically by their descending stage
    factors, so the worst raw stage is minimized first, then the next worst,
    and so on.
    """
    if G is None:
        G = DB(6, 8, -2)
    p = getattr(G, "source_parameters", {})
    if getattr(G, "source_kind", None) != "dumbbell" or (p.get("c1"), p.get("c2"), p.get("l")) != (6, 8, -2):
        raise ValueError("db682_candidate_activation_orders requires DB(6,8,-2).")
    cycles = G.simple_six_cycles()
    if len(cycles) != 1:
        raise AssertionError(f"Expected exactly one simple C6 in DB(6,8,-2); found {len(cycles)}.")
    prefix = list(cycles[0].edges)
    tail = [e.id for e in G.edges if e.id not in set(prefix)]
    ranked = []
    for perm in permutations(tail):
        order = prefix + list(perm)
        stage = []
        pref = list(prefix)
        for eid in perm:
            stage.append(_stage_factor_for_order_prefix(G, pref, eid))
            pref.append(eid)
        ranked.append((tuple(sorted(stage, reverse=True)), tuple(order), order))
    ranked.sort(key=lambda row: (row[0], row[1]))
    # v0.12 target-specific traversal order.  This was selected only from
    # mathematically equivalent tail permutations after adding the exact
    # completed-restriction superdomain filter.  It is a bijective traversal-only swap of q9/q10 relative to v0.11.
    # The raw tail stage-factor sequence is exactly unchanged, but q10 is now
    # exposed immediately after q7 so the exact q10->q11 endpoint certificate
    # can fire before q9/q8 are generated.
    tuned_tail = [7, 10, 9, 8, 6, 11]
    if set(tuned_tail) != set(tail):
        raise AssertionError("v0.10 tuned DB682 tail does not match the six non-C6 edges.")
    tuned_order = prefix + tuned_tail
    path_order = prefix + sorted(tail)
    result = [tuned_order]
    if path_order != tuned_order and len(result) < max(1, int(limit)):
        result.append(path_order)
    for _, _, order in ranked:
        if order not in result:
            result.append(order)
        if len(result) >= max(1, int(limit)):
            break
    return result


def enumerate_planar_c6_cores(
    G: Optional[ThrackleGraph] = None,
    *,
    activation_order: Optional[Sequence[int]] = None,
    planarity: str = "auto",
) -> Tuple[List[Pi], List[int]]:
    """Enumerate exactly the planar crossing-order systems on DB(6,8,-2)'s C6.

    The 46,656 possibilities are literal complete Pi systems for the six cycle
    edges, considering only their three nonincident cycle partners.  A core is
    kept exactly when the complete Fulek--Pach augmented graph of that C6 is
    planar.  Any planar completion of the whole dumbbell must restrict to one of
    these cores, because this active-C6 augmented graph is a minor of the full
    augmented graph.
    """
    if G is None:
        G = DB(6, 8, -2)
    cycles = G.simple_six_cycles()
    if len(cycles) != 1:
        raise AssertionError(f"Expected exactly one simple C6; found {len(cycles)}.")
    cycle = cycles[0]
    if activation_order is None:
        activation_order = db682_candidate_activation_orders(G, limit=1)[0]
    activation_order = list(activation_order)
    core_edges = activation_order[:6]
    if set(core_edges) != set(cycle.edges):
        raise ValueError("The first six activation edges must be exactly the unique C6.")

    search = BacktrackingSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, debug=False, progress_interval_seconds=None,
        planarity_backend=planarity, activation_order="custom",
        custom_activation_order=activation_order, use_locked_prefix_pruning=False,
    )
    backend = search.planarity
    choices = []
    core_set = set(core_edges)
    for eid in core_edges:
        partners = [f for f in G._nonincident[eid] if f in core_set]
        if len(partners) != 3:
            raise AssertionError(f"C6 edge {eid} should have exactly three nonincident C6 partners.")
        choices.append(list(permutations(partners)))

    cores: List[Pi] = []
    checked = 0
    for candidate in product(*choices):
        checked += 1
        pi: Pi = {e.id: [] for e in G.edges}
        for eid, order_tuple in zip(core_edges, candidate):
            pi[eid] = list(order_tuple)
        H = build_active_augmented_minor(
            G, pi, core_edges, search.oriented,
            validate=True, crossing_cache=search.crossing_cache,
        )
        if backend.is_planar(H):
            cores.append({eid: list(pi[eid]) for eid in core_edges})

    if checked != 46656:
        raise AssertionError(f"Expected 46,656 C6 systems; checked {checked}.")
    if len(cores) != 8:
        raise AssertionError(f"Expected exactly 8 planar C6 cores; found {len(cores)}.")
    return cores, core_edges


# v0.13 exact reflection automorphism of DB(6,8,-2).  It exchanges A and B
# and reverses each of the three internally-disjoint A--B paths.
_DB682_REFLECTION_EDGE = {
    0: 1, 1: 0, 2: 5, 5: 2, 3: 4, 4: 3,
    6: 11, 11: 6, 7: 10, 10: 7, 8: 9, 9: 8,
}

def _db682_reflect_pi(pi: Pi) -> Pi:
    """Relabel one Pi by the target reflection in the program orientations.

    Every stored target edge orientation is reversed by this automorphism, so
    after relabeling crossing edge IDs, each row order is reversed.  This map is
    an involution and induces an isomorphism of Fulek--Pach augmented graphs.
    """
    out: Pi = {}
    for e, row in pi.items():
        f = _DB682_REFLECTION_EDGE[int(e)]
        out[f] = list(reversed([_DB682_REFLECTION_EDGE[int(x)] for x in row]))
    return out

def _db682_core_orbits(cores: Sequence[Pi]) -> Tuple[List[int], Dict[int, Tuple[int, ...]]]:
    """Return exact two-core orbits under the DB(6,8,-2) reflection."""
    def key(pi: Pi):
        return tuple((int(e), tuple(int(x) for x in pi[e])) for e in sorted(pi))
    index = {key(c): i for i, c in enumerate(cores)}
    if len(index) != len(cores):
        raise AssertionError("v0.13 retained C6 cores are not distinct.")
    seen = set()
    reps: List[int] = []
    orbits: Dict[int, Tuple[int, ...]] = {}
    for i, c in enumerate(cores):
        if i in seen:
            continue
        reflected = _db682_reflect_pi(c)
        j = index.get(key(reflected))
        if j is None:
            raise AssertionError("v0.13 reflection did not map a planar C6 core to a retained core.")
        if key(_db682_reflect_pi(reflected)) != key(c):
            raise AssertionError("v0.13 reflection Pi map is not an involution.")
        orb = tuple(sorted({i, j}))
        # On the target's eight planar C6 cores no core is fixed.  Fail loudly
        # if that audited structure ever changes.
        if len(orb) != 2:
            raise AssertionError("v0.13 expected every planar C6 core reflection orbit to have size two.")
        rep = min(orb)
        reps.append(rep)
        orbits[rep] = orb
        seen.update(orb)
    if len(seen) != len(cores) or len(reps) * 2 != len(cores):
        raise AssertionError("v0.13 C6 reflection orbits do not partition the retained cores.")
    return sorted(reps), orbits


def _seed_search_with_core(search: BacktrackingSearch, core_pi: Pi, core_edges: Sequence[int]) -> int:
    """Put ``search`` exactly at the completed six-edge C6 state."""
    core_edges = list(core_edges)
    if search.order[:6] != core_edges:
        raise AssertionError("Core edges must be the first six activation edges in the seeded search.")
    if set(core_pi) != set(core_edges):
        raise ValueError("core_pi must contain exactly the six C6 edge IDs.")

    for eid in core_edges:
        search.pi[eid] = list(core_pi[eid])
    validate_partial_pi(search.G, search.pi, core_edges)
    pairs = modeled_pairs(search.pi, core_edges)
    if len(pairs) != 9:
        raise AssertionError(f"A completed C6 should contain 9 proper crossing pairs; found {len(pairs)}.")

    search.partial_active_index = 5
    search.current_edge_index = 5
    search.current_modeled_crossings = len(pairs)
    search.stats.max_active_edges = max(search.stats.max_active_edges, 6)
    search.stats.max_modeled_crossings = max(search.stats.max_modeled_crossings, len(pairs))
    if search.incremental_partial:
        search.partial_H = build_prefix_planarization(
            search.G, search.pi, core_edges, search.oriented,
            current_eid=core_edges[-1], current_complete=True,
            validate=True, crossing_cache=search.crossing_cache,
        )
        if search.debug:
            search._assert_partial_graph_matches(5)

    core_subtree = search.suffix_after[5]
    search.total_candidates = core_subtree
    search.stats.total_candidates = core_subtree
    search.stats.resolved_candidates = 0
    search.stats.planarity_pruned_candidates = 0
    search.stats.c6_pruned_candidates = 0
    search.stats.full_candidates_resolved = 0
    return core_subtree


def _run_seeded_core_search(search: BacktrackingSearch, core_pi: Pi, core_edges: Sequence[int]) -> SearchResult:
    """Run one exact C6-core extension search with ordinary SearchResult semantics."""
    core_total = _seed_search_with_core(search, core_pi, core_edges)
    search.started = time.perf_counter()
    search.last_progress = search.started
    search.last_report_time = search.started
    search.last_report_resolved = 0
    try:
        search._maybe_report_progress(force=True)
        if len(search.order) == 6:
            planar = search._complete_candidate_planar()
            search._mark_resolved(1, "full")
            found = planar
        else:
            search._activate_edge(6)
            found = search._search_edge(6, search.older_required[6])
        search.stats.elapsed_seconds = search._elapsed()
        search._maybe_report_progress(force=True)
        search._close_progress_line()
        if found:
            return SearchResult(
                "THRACKLEABLE", search.witness, search.stats,
                "Found a complete Pi extending this exact planar C6 core.",
            )
        if search.stats.resolved_candidates != core_total:
            raise AssertionError(
                "Seeded core search returned negative without exact 100% core coverage: "
                f"{search.stats.resolved_candidates}/{core_total}."
            )
        return SearchResult(
            "NONTHRACKLEABLE", None, search.stats,
            "Exhausted every completion of this exact planar C6 core.",
        )
    except SearchLimitReached as exc:
        search.stats.elapsed_seconds = search._elapsed()
        search._maybe_report_progress(force=True)
        search._close_progress_line()
        return SearchResult("INCONCLUSIVE", None, search.stats, str(exc))



def _core_progress_snapshot(search: BacktrackingSearch, core_index: int, status: str = "RUNNING") -> dict:
    """Small picklable snapshot used only by the parent-process terminal dashboard."""
    st = search.stats
    return {
        "core_index": int(core_index),
        "status": status,
        "elapsed_seconds": float(search._elapsed()),
        "resolved_candidates": int(st.resolved_candidates),
        "total_candidates": int(st.total_candidates),
        "recursive_calls": int(st.recursive_calls),
        "partial_planarity_tests": int(st.partial_planarity_tests),
        "full_planarity_tests": int(st.full_planarity_tests),
        "partial_nonplanar_prunes": int(st.partial_nonplanar_prunes),
        "locked_prefix_tests": int(getattr(st, "locked_prefix_tests", 0)),
        "locked_prefix_prunes": int(getattr(st, "locked_prefix_prunes", 0)),
        "superdomain_tests": int(getattr(st, "superdomain_tests", 0)),
        "superdomain_prunes": int(getattr(st, "superdomain_prunes", 0)),
        "superdomain_cache_hits": int(getattr(st, "superdomain_cache_hits", 0)),
        "whole_stage_calls": int(getattr(st, "whole_stage_calls", 0)),
        "whole_stage_cache_hits": int(getattr(st, "whole_stage_cache_hits", 0)),
        "whole_stage_dead_parents": int(getattr(st, "whole_stage_dead_parents", 0)),
        "whole_stage_projection_classes": int(getattr(st, "whole_stage_projection_classes", 0)),
        "whole_stage_candidates_pruned": int(getattr(st, "whole_stage_candidates_pruned", 0)),
        "c8_language_queries": int(getattr(st, "c8_language_queries", 0)),
        "c8_language_prunes": int(getattr(st, "c8_language_prunes", 0)),
        "c8_language_candidates_pruned": int(getattr(st, "c8_language_candidates_pruned", 0)),
        "v014_c8_incremental_refinements": int(getattr(st, "v014_c8_incremental_refinements", 0)),
        "v014_c8_sensitive_slot_bundles": int(getattr(st, "v014_c8_sensitive_slot_bundles", 0)),
        "v014_c8_sensitive_slot_dead": int(getattr(st, "v014_c8_sensitive_slot_dead", 0)),
        "v014_c8_sensitive_candidates_pruned": int(getattr(st, "v014_c8_sensitive_candidates_pruned", 0)),
        "v015_h2_queries": int(getattr(st, "v015_h2_queries", 0)),
        "v015_h2_refinements": int(getattr(st, "v015_h2_refinements", 0)),
        "v015_h2_prunes": int(getattr(st, "v015_h2_prunes", 0)),
        "v015_h2_candidates_pruned": int(getattr(st, "v015_h2_candidates_pruned", 0)),
        "v015_h5_queries": int(getattr(st, "v015_h5_queries", 0)),
        "v015_h5_refinements": int(getattr(st, "v015_h5_refinements", 0)),
        "v015_h5_prunes": int(getattr(st, "v015_h5_prunes", 0)),
        "v015_h5_candidates_pruned": int(getattr(st, "v015_h5_candidates_pruned", 0)),
        "v015_support_prefix_states": int(getattr(st, "v015_support_prefix_states", 0)),
        "v015_support_prefix_dead": int(getattr(st, "v015_support_prefix_dead", 0)),
        "v015_support_prefix_bundles_skipped": int(getattr(st, "v015_support_prefix_bundles_skipped", 0)),
        "v011_kuratowski_hits": int(getattr(st, "v011_kuratowski_hits", 0)),
        "v011_kuratowski_learned": int(getattr(st, "v011_kuratowski_learned", 0)),
        "v011_batch_calls": int(getattr(st, "v011_batch_calls", 0)),
        "v011_batch_graphs": int(getattr(st, "v011_batch_graphs", 0)),
        "domain_pruned_stage_assignments": int(getattr(st, "domain_pruned_stage_assignments", 0)),
        "domain_signatures_considered": int(getattr(st, "domain_signatures_considered", 0)),
        "local_domain_signatures": int(getattr(st, "local_domain_signatures", 0)),
        "c6_prunes": int(st.c6_prunes),
        "backtracks": int(st.backtracks),
        "screening_states": int(getattr(st, "screening_states", 0)),
        "current_modeled_crossings": int(search.current_modeled_crossings),
        "max_modeled_crossings": int(st.max_modeled_crossings),
        "current_edge_index": int(search.current_edge_index),
        "total_edges": int(len(search.order)),
        "total_required_crossings": int(search.total_required_crossings),
        "planarity_backend": str(st.planarity_backend),
    }


def _db682_parallel_dashboard(
    snapshots: dict,
    selected_indices: Sequence[int],
    *,
    started: float,
    excluded_candidates: int,
    full_total: int,
    core_subtree: int,
    last_retained_resolved: int,
    last_time: float,
    orbit_sizes: Optional[Dict[int, int]] = None,
) -> Tuple[str, int, float]:
    """Render a v0.6.1.1-style dashboard for the eight independent core jobs."""
    now = time.perf_counter()
    elapsed = max(0.0, now - started)
    selected = list(selected_indices)
    orbit_sizes = dict(orbit_sizes or {i: 1 for i in selected})
    retained_total = core_subtree * sum(int(orbit_sizes.get(i, 1)) for i in selected)
    retained_resolved = 0
    calls = tests = prunes = locked_prunes = super_tests = super_prunes = super_hits = c6_prunes = backtracks = screened = 0
    whole_calls = whole_hits = whole_dead = whole_classes = kur_hits = kur_learned = batch_calls = batch_graphs = 0
    c8_queries = c8_prunes = c8_candidates = 0
    v14_refines = v14_bundles = v14_bundle_dead = v14_bundle_candidates = 0
    h2_queries = h2_refines = h2_prunes = h2_candidates = 0
    h5_queries = h5_refines = h5_prunes = h5_candidates = 0
    v15_prefix = v15_prefix_dead = v15_prefix_skipped = 0
    deepest = 0
    running = completed = 0
    backend_names = set()

    for i in selected:
        snap = snapshots.get(i) or {}
        r = int(snap.get("resolved_candidates", 0))
        retained_resolved += int(orbit_sizes.get(i, 1)) * min(max(r, 0), core_subtree)
        calls += int(snap.get("recursive_calls", 0))
        tests += int(snap.get("partial_planarity_tests", 0)) + int(snap.get("full_planarity_tests", 0))
        prunes += int(snap.get("partial_nonplanar_prunes", 0))
        locked_prunes += int(snap.get("locked_prefix_prunes", 0))
        super_tests += int(snap.get("superdomain_tests", 0))
        super_prunes += int(snap.get("superdomain_prunes", 0))
        super_hits += int(snap.get("superdomain_cache_hits", 0))
        whole_calls += int(snap.get("whole_stage_calls", 0))
        whole_hits += int(snap.get("whole_stage_cache_hits", 0))
        whole_dead += int(snap.get("whole_stage_dead_parents", 0))
        whole_classes += int(snap.get("whole_stage_projection_classes", 0))
        c8_queries += int(snap.get("c8_language_queries", 0))
        c8_prunes += int(snap.get("c8_language_prunes", 0))
        c8_candidates += int(snap.get("c8_language_candidates_pruned", 0))
        v14_refines += int(snap.get("v014_c8_incremental_refinements", 0))
        v14_bundles += int(snap.get("v014_c8_sensitive_slot_bundles", 0))
        v14_bundle_dead += int(snap.get("v014_c8_sensitive_slot_dead", 0))
        v14_bundle_candidates += int(snap.get("v014_c8_sensitive_candidates_pruned", 0))
        h2_queries += int(snap.get("v015_h2_queries", 0))
        h2_refines += int(snap.get("v015_h2_refinements", 0))
        h2_prunes += int(snap.get("v015_h2_prunes", 0))
        h2_candidates += int(snap.get("v015_h2_candidates_pruned", 0))
        h5_queries += int(snap.get("v015_h5_queries", 0))
        h5_refines += int(snap.get("v015_h5_refinements", 0))
        h5_prunes += int(snap.get("v015_h5_prunes", 0))
        h5_candidates += int(snap.get("v015_h5_candidates_pruned", 0))
        v15_prefix += int(snap.get("v015_support_prefix_states", 0))
        v15_prefix_dead += int(snap.get("v015_support_prefix_dead", 0))
        v15_prefix_skipped += int(snap.get("v015_support_prefix_bundles_skipped", 0))
        kur_hits += int(snap.get("v011_kuratowski_hits", 0))
        kur_learned += int(snap.get("v011_kuratowski_learned", 0))
        batch_calls += int(snap.get("v011_batch_calls", 0))
        batch_graphs += int(snap.get("v011_batch_graphs", 0))
        c6_prunes += int(snap.get("c6_prunes", 0))
        backtracks += int(snap.get("backtracks", 0))
        screened += int(snap.get("screening_states", 0))
        deepest = max(deepest, int(snap.get("max_modeled_crossings", 0)))
        status = str(snap.get("status", "WAITING"))
        if status == "RUNNING":
            running += 1
        elif status not in {"WAITING", "STARTING"}:
            completed += 1
        b = snap.get("planarity_backend")
        if b:
            backend_names.add(str(b))

    dt = max(now - last_time, 1e-12)
    delta = max(0, retained_resolved - last_retained_resolved)
    delta_rate = delta / dt
    test_rate = tests / elapsed if elapsed > 0 else 0.0
    global_resolved = excluded_candidates + retained_resolved
    retained_pct = coverage_percent_string(retained_resolved, retained_total or 1, precision=18)
    global_pct = coverage_percent_string(global_resolved, full_total, precision=18)
    backend = ",".join(sorted(backend_names)) if backend_names else "starting"

    with localcontext() as ctx:
        ctx.prec = 30
        pp = (Decimal(delta) * Decimal(100) / Decimal(retained_total)) if retained_total else Decimal(0)
        delta_pp = f"+{pp:.3E} pp"

    lines = [
        "Graph:                     DB(6,8,-2) — exact C6-core/orbit search",
        f"Runtime:                   {BacktrackingSearch._format_duration(elapsed)} ({elapsed:,.2f} s)",
        f"Search coverage:           {retained_pct}  (retained C6 cores)",
        f"Global exact coverage:     {global_pct}  (includes 46,648 excluded C6 cores)",
        f"Resolved complete Pi:      {_format_big_int(retained_resolved, 8)} / {_format_big_int(retained_total, 8)}",
        f"Newly resolved since last: +{_format_big_int(delta, 7)} ({delta_pp})",
        f"Resolved Pi/sec (window):  {_format_big_int(int(delta_rate), 6)}",
        "",
        f"Recursive calls:           {calls:,}",
        f"Planarity tests:           {tests:,}",
        f"Tests/sec:                 {test_rate:,.1f}",
        f"Partial nonplanar prunes:  {prunes:,}",
        f"Locked-prefix prunes:      {locked_prunes:,}",
        f"Superdomain tests/prunes:  {super_tests:,} / {super_prunes:,}",
        f"Superdomain cache hits:    {super_hits:,}",
        f"Whole-stage calls/dead:    {whole_calls:,} / {whole_dead:,}",
        f"Whole-stage cache hits:    {whole_hits:,}",
        f"Whole-stage proj classes:  {whole_classes:,}",
        f"C8-language queries/prunes:{c8_queries:,} / {c8_prunes:,}",
        f"C8 candidates pruned:      {_format_big_int(c8_candidates, 6)}",
        f"v0.14 C8 refinements:      {v14_refines:,}",
        f"v0.14 slot bundles/dead:   {v14_bundles:,} / {v14_bundle_dead:,}",
        f"v0.14 bundled candidates:  {_format_big_int(v14_bundle_candidates, 6)}",
        f"v0.15 H2 queries/refines:  {h2_queries:,} / {h2_refines:,}",
        f"v0.15 H2 prunes/candidates:{h2_prunes:,} / {_format_big_int(h2_candidates, 6)}",
        f"v0.15 H5 queries/refines:  {h5_queries:,} / {h5_refines:,}",
        f"v0.15 H5 prunes/candidates:{h5_prunes:,} / {_format_big_int(h5_candidates, 6)}",
        f"v0.15 support prefixes:    {v15_prefix:,} (dead {v15_prefix_dead:,}, skipped bundles {v15_prefix_skipped:,})",
        f"Kuratowski hits/learned:   {kur_hits:,} / {kur_learned:,}",
        f"v0.11 batch calls/graphs:  {batch_calls:,} / {batch_graphs:,}",
        f"C6 prunes inside cores:    {c6_prunes:,}",
        f"Backtracks:                {backtracks:,}",
        f"Screened states:           {screened:,}",
        "",
        f"Running cores:             {running} / {len(selected)}",
        f"Completed cores:           {completed} / {len(selected)}",
        f"Deepest crossings:         {deepest} / 51",
        f"Planarity backend:         {backend}",
        "",
        "Per-core progress:",
    ]
    for i in selected:
        snap = snapshots.get(i) or {}
        status = str(snap.get("status", "WAITING"))
        r = int(snap.get("resolved_candidates", 0))
        pct = coverage_percent_string(r, core_subtree, precision=9)
        c = int(snap.get("recursive_calls", 0))
        t = int(snap.get("partial_planarity_tests", 0)) + int(snap.get("full_planarity_tests", 0))
        p = int(snap.get("partial_nonplanar_prunes", 0))
        lp = int(snap.get("locked_prefix_prunes", 0))
        d = int(snap.get("max_modeled_crossings", 0))
        mult = int(orbit_sizes.get(i, 1))
        label = f"Core {i}" if mult == 1 else f"Core {i} (x{mult})"
        lines.append(
            f"  {label}: {status:<16} cov {pct:>13} | calls {c:>9,} | "
            f"tests {t:>10,} | P {p:>10,} | LP {lp:>8,} | depth {d:>2}/51"
        )
    return "\n".join(lines), retained_resolved, now


def _print_db682_dashboard(text: str, mode: str) -> None:
    if mode == "auto":
        mode = "single" if sys.stdout.isatty() else "line"
    if mode in {"single", "dashboard"}:
        print("\033[2J\033[H" + text, end="", flush=True)
    else:
        print(text + "\n", flush=True)




# ---------------------------------------------------------------------------
# v0.9 target-specific exact C6-projection domains and factorized q-stage search
# ---------------------------------------------------------------------------

@dataclass(frozen=True, order=True)
class DB682LocalSignature:
    """Complete projection of one q-path edge onto the fixed C6 core.

    ``core_order`` is the order of the C6 edges crossed by q along q's fixed
    orientation. ``core_gaps`` gives, in ``core_partners`` order, how many of
    the three C6-vs-C6 crossings on that host C6 edge occur before q.

    For the local graph C6 + q these data determine the complete Pi exactly.
    In a full dumbbell Pi, deleting all other q-path edges preserves this
    signature. Therefore a full planar augmented graph can use only signatures
    whose C6+q augmented graph is planar.
    """
    core_order: Tuple[int, ...]
    core_gaps: Tuple[int, ...]


def _db682_core_partners(G: ThrackleGraph, core_edges: Sequence[int], q: int) -> Tuple[int, ...]:
    core_set = set(core_edges)
    return tuple(e for e in core_edges if e in core_set and e in G._nonincident[q])


def _db682_local_signature_from_pi(
    pi: Pi,
    q: int,
    core_edges: Sequence[int],
    core_partners: Sequence[int],
) -> DB682LocalSignature:
    core_set = set(core_edges)
    order = tuple(e for e in pi[q] if e in core_set)
    gaps = []
    for e in core_partners:
        if q not in pi[e]:
            raise AssertionError("Complete local signature requested before both sides were modeled.")
        j = pi[e].index(q)
        gaps.append(sum(1 for x in pi[e][:j] if x in core_set))
    return DB682LocalSignature(order, tuple(gaps))


def _generate_db682_local_domain(
    search: BacktrackingSearch,
    core_pi: Pi,
    core_edges: Sequence[int],
    q: int,
) -> Tuple[Tuple[DB682LocalSignature, ...], dict]:
    """Generate exactly all planar C6+q complete projection signatures.

    This precomputation is itself exhaustive.  It explores the local stage by
    the safe locked-prefix minor.  A local branch is dropped only when that
    minor is nonplanar; at a complete local signature the same builder is the
    full augmented graph of C6+q.  Thus no globally planar Pi can lose its
    projection here.
    """
    G = search.G
    core_edges = tuple(core_edges)
    core_set = set(core_edges)
    partners = _db682_core_partners(G, core_edges, q)
    active = core_edges + (q,)
    pi: Pi = {e.id: [] for e in G.edges}
    for e in core_edges:
        pi[e] = list(core_pi[e])

    signatures = set()
    tests = 0
    prunes = 0
    nodes = 0
    started = time.perf_counter()

    def rec(remaining: Tuple[int, ...]):
        nonlocal tests, prunes, nodes
        nodes += 1
        if not remaining:
            signatures.add(_db682_local_signature_from_pi(pi, q, core_edges, partners))
            return
        for old in remaining:
            child = tuple(x for x in remaining if x != old)
            for pos in range(len(pi[old]) + 1):
                pi[old].insert(pos, q)
                pi[q].append(old)
                H = build_locked_prefix_minor(
                    G, pi, active, search.oriented,
                    current_eid=q, current_complete=(not child),
                    validate=False, crossing_cache=search.crossing_cache,
                )
                tests += 1
                if search.planarity.is_planar(H):
                    rec(child)
                else:
                    prunes += 1
                got_q = pi[q].pop()
                got_old = pi[old].pop(pos)
                if got_q != old or got_old != q:
                    raise AssertionError("Local-domain DFS failed to restore Pi.")

    rec(partners)
    elapsed = time.perf_counter() - started
    out = tuple(sorted(signatures))
    if not out:
        raise AssertionError(f"C6+edge {q} local domain unexpectedly empty.")
    return out, {
        "q": q,
        "partners": list(partners),
        "signatures": len(out),
        "nodes": nodes,
        "planarity_tests": tests,
        "planarity_prunes": prunes,
        "seconds": elapsed,
    }


def _db682_build_local_domains(
    search: BacktrackingSearch,
    core_pi: Pi,
    core_edges: Sequence[int],
) -> Tuple[Dict[int, Tuple[DB682LocalSignature, ...]], List[dict]]:
    """Build the v0.9 exact local domains for q6,...,q11.

    Edges 7,8,9,10 have identical local incidence with the fixed C6: in the
    abstract subgraph C6+q they are an isolated K2 whose two endpoints are not
    C6 vertices, and q is nonincident to every C6 edge.  Relabeling that K2
    while fixing the C6 is an isomorphism, and the signature records only C6
    edge IDs.  Hence their domains are exactly the same.  We compute edge 7
    once and reuse it for 8,9,10.  Edges 6 and 11 are computed separately
    because they attach to different C6 vertices.
    """
    domains: Dict[int, Tuple[DB682LocalSignature, ...]] = {}
    reports: List[dict] = []
    for q in (6, 7, 11):
        dom, rep = _generate_db682_local_domain(search, core_pi, core_edges, q)
        domains[q] = dom
        reports.append(rep)
        search.stats.local_domain_planarity_tests += int(rep["planarity_tests"])
        search.stats.local_domain_planarity_prunes += int(rep["planarity_prunes"])
        search.stats.local_domain_signatures += len(dom)
        search.stats.local_domain_seconds += float(rep["seconds"])
    for q in (8, 9, 10):
        # Exact relabeling reuse described above; no search cases are omitted.
        domains[q] = domains[7]
    return domains, reports


class DB682FactorizedSearch(BacktrackingSearch):
    """v0.9 exact extension search for one retained DB(6,8,-2) C6 core.

    The first six edges are fixed by ``core_pi``.  Every later stage is
    reparameterized by its exact C6 projection plus the remaining q-vs-q
    interleavings.  The reparameterization is bijective:

    * a complete stage assignment has one unique C6 projection signature;
    * after fixing that projection, prior q-edge crossings are inserted in a
      fixed edge order; removing them in reverse order recovers the unique
      insertion history;
    * on each C6 host edge, every exact slot consistent with the signature's
      C6 gap is enumerated.

    Planarity pruning inside this factorized search is deliberately restricted
    to stage-complete active-subgraph augmented graphs.

    Therefore the factorized search covers exactly the same complete Pi systems
    as the ordinary activation-stage search.  The only omitted projection
    signatures are those whose complete C6+q augmented graph is nonplanar.
    """

    def __init__(self, *args, core_edges: Sequence[int], local_domains=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.db682_core_edges = tuple(core_edges)
        self.db682_core_set = set(core_edges)
        self.db682_local_domains = dict(local_domains or {})
        self.db682_local_domain_reports: List[dict] = []
        # v0.11 safety rule: caches contain only exact mathematical facts.
        # Compact bytes keys are a bijective serialization of selected edge IDs
        # and their exact projected Pi lists; there is no hash-only inference.
        self.db682_superdomain_cache: OrderedDict[bytes, bool] = OrderedDict()
        self.db682_superdomain_cache_limit = 200000
        self.db682_whole_stage_cache: OrderedDict[bytes, bool] = OrderedDict()
        self.db682_whole_stage_cache_limit = 100000
        self.db682_kuratowski_by_selected = defaultdict(list)
        self.db682_kuratowski_limit_per_selected = 48
        self.db682_iso_cache = defaultdict(list)
        self.db682_iso_cache_limit_per_bucket = 8
        self.use_exact_superdomain_pruning = True
        self.use_exact_whole_stage_pruning = True
        self.use_v012_endpoint_hoisting = True
        self.use_v012_direct_pi_encoder = True
        self.db682_endpoint_cache: OrderedDict[bytes, bool] = OrderedDict()
        self.db682_endpoint_cache_limit = 100000
        # Kuratowski learning remains available but is OFF in the v0.12 target
        # configuration because the direct exact encoder is substantially faster.
        self.use_v011_kuratowski_learning = False
        # Exact graph-isomorphism reuse is logically safe but can be slower on
        # some machines. It is implemented and blast-tested, but remains opt-in.
        self.use_v011_exact_iso_cache = False

        # v0.13 exact C8-language support.  The language contains EVERY complete
        # labeled/oriented C8 crossing-order system generated by the published
        # face-routing traversal.  A partial DB state is kept iff at least one
        # language member contains each already-modeled C8 row as a subsequence.
        # No incomplete graph is planarity-tested here.
        self.use_v013_c8_language = True
        self._v013_c8_language = _db682_c8_language()
        self._v013_c8_row_index = {e: i for i, e in enumerate(_DB682_C8_EDGE_ORDER)}
        self._v013_c8_all_mask = (1 << len(self._v013_c8_language)) - 1
        self._v013_c8_row_mask_cache: Dict[Tuple[int, Tuple[int, ...]], int] = {}
        self.use_v014_precomputed_c8_rows = True
        self._v014_c8_row_mask_tables = _db682_c8_row_mask_tables()

        # v0.14 keeps the same exact C8 theorem but propagates the support mask
        # incrementally.  A child only adds order relations on rows that were
        # actually changed, hence child_support = parent_support AND the exact
        # complete-language masks of those stronger rows.  This is a pure
        # implementation optimization: disabling it restores the v0.13 global
        # support recomputation path.
        self.use_v014_incremental_c8 = True
        # At a q-stage only C6 hosts 0 and 1 lie on the target C8.  v0.14
        # enumerates those C8-sensitive insertion slots first; if their exact
        # support is empty, every combination of the four C8-insensitive C6
        # host slots is killed in one cardinality-certified bundle.
        self.use_v014_c8_sensitive_slots = True

        # v0.15 strengthens the exact cycle support with two 9-edge selected
        # subgraphs: H2=C8+edge2 and its exact target reflection H5=C8+edge5.
        # These are complete selected-edge restrictions, so zero support is a
        # sound minor obstruction.  H5 reuses the same frozen H2 data through
        # the exact DB reflection; no second independently trusted language is
        # required.
        # Disabled in the bare class so all inherited v0.14 direct regressions
        # retain their historical behavior.  The production DB682 worker enables
        # these explicitly from run_db682_cores (default True there).
        self.use_v015_h2_language = False
        self.use_v015_h5_language = False
        self.use_v015_support_driven_slots = False
        self._v015_h2_records = _db682_h2_records() if _DB682_H2_LANGUAGE_COUNT else ()
        self._v015_h2_all_mask = (1 << len(self._v015_h2_records)) - 1 if self._v015_h2_records else 0
        self._v015_h2_full_row_groups = _db682_h2_full_row_groups() if self._v015_h2_records else {}
        # Immutable exact tables are built once (and before fork in production)
        # so worker support lookups are direct dictionary reads rather than
        # repeated scans over complete-row groups.
        self._v015_h2_row_mask_tables = _db682_h2_row_mask_tables() if self._v015_h2_records else {}

    @staticmethod
    def _is_subsequence_tuple(needle: Tuple[int, ...], haystack: Tuple[int, ...]) -> bool:
        if not needle:
            return True
        j = 0
        for x in haystack:
            if x == needle[j]:
                j += 1
                if j == len(needle):
                    return True
        return False

    def _v013_c8_row_mask(self, edge: int, subseq: Tuple[int, ...]) -> int:
        key = (int(edge), tuple(int(x) for x in subseq))
        if getattr(self, "use_v014_precomputed_c8_rows", False):
            # Exact table lookup; a missing key means this ordered tuple is not
            # a subsequence of any complete language row and therefore has zero
            # support.
            return int(self._v014_c8_row_mask_tables[int(edge)].get(key[1], 0))
        cached = self._v013_c8_row_mask_cache.get(key)
        if cached is not None:
            self.stats.c8_language_row_cache_hits += 1
            return int(cached)
        self.stats.c8_language_row_cache_misses += 1
        row_index = self._v013_c8_row_index[edge]
        mask = 0
        bit = 1
        for system in self._v013_c8_language:
            if self._is_subsequence_tuple(key[1], system[row_index]):
                mask |= bit
            bit <<= 1
        self._v013_c8_row_mask_cache[key] = mask
        return mask

    def _v013_c8_support_mask(self) -> int:
        """Return exact C8-language support for the current partial Pi.

        SAFETY THEOREM.  Any full planar DB Pi restricts to one member L of the
        exhaustive complete C8 language.  Future UPDATEs can insert new C8
        crossings but never change the relative order of crossings already
        present in a projected row.  Hence every currently modeled projected
        row must be a subsequence of L's corresponding row.  If no L satisfies
        all row subsequence constraints, no full planar completion exists.

        This test deliberately ignores missing crossings; they may be inserted
        later in arbitrary gaps.  Therefore it cannot reproduce the old
        incomplete-placeholder monotonicity bug.
        """
        if not self.use_v013_c8_language:
            return self._v013_c8_all_mask
        self.stats.c8_language_queries += 1
        t0 = time.perf_counter()
        mask = self._v013_c8_all_mask
        for e in _DB682_C8_EDGE_ORDER:
            subseq = tuple(x for x in self.pi[e] if x in _DB682_C8_EDGE_SET)
            if not subseq:
                continue
            mask &= self._v013_c8_row_mask(e, subseq)
            if not mask:
                break
        self.stats.c8_language_seconds += time.perf_counter() - t0
        return mask

    def _v013_c8_supported(self) -> bool:
        return bool(self._v013_c8_support_mask())

    def _v014_c8_refine_mask(self, parent_mask: int, changed_edges: Sequence[int]) -> int:
        """Exact incremental refinement of the v0.13 C8 support set.

        ``parent_mask`` already encodes every C8 row constraint of the parent
        state.  The child state is obtained only by inserting crossings, so an
        unchanged row has exactly the same constraint and a changed row has a
        stronger projected sequence containing its parent sequence as a
        subsequence.  Intersecting the parent support with the complete-language
        mask of each changed row therefore gives *exactly* the child support.

        No graph is constructed and no incomplete state is planarity-tested.
        """
        if not self.use_v013_c8_language:
            return self._v013_c8_all_mask
        self.stats.v014_c8_incremental_refinements += 1
        mask = int(parent_mask)
        seen = set()
        for e0 in changed_edges:
            e = int(e0)
            if e in seen or e not in _DB682_C8_EDGE_SET:
                continue
            seen.add(e)
            subseq = tuple(x for x in self.pi[e] if x in _DB682_C8_EDGE_SET)
            mask &= self._v013_c8_row_mask(e, subseq)
            if not mask:
                break
        return mask

    def _v014_c8_child_mask(self, parent_mask: Optional[int], changed_edges: Sequence[int]) -> int:
        """Use incremental support when enabled; otherwise reproduce v0.13."""
        if not self.use_v013_c8_language:
            return self._v013_c8_all_mask
        if self.use_v014_incremental_c8:
            if parent_mask is None:
                parent_mask = self._v013_c8_support_mask()
            return self._v014_c8_refine_mask(int(parent_mask), changed_edges)
        return self._v013_c8_support_mask()

    def _v015_h2_row_mask(self, edge: int, subseq: Tuple[int, ...]) -> int:
        """Exact H2 support mask for one ordered partial selected row."""
        if not self._v015_h2_records:
            return 0
        e = int(edge)
        seq = tuple(int(x) for x in subseq)
        return int(self._v015_h2_row_mask_tables[e].get(seq, 0))

    def _v015_h5_row_mask(self, edge: int, subseq: Tuple[int, ...]) -> int:
        """Exact H5 mask by pulling a row back through the DB reflection.

        H5 is the reflection of H2.  The program orientation of every target
        edge reverses under that automorphism, so a target H5 row is pulled
        back by reflecting IDs and reversing the row order.  Bit i therefore
        represents the reflection of H2 member i, giving a literal bijection.
        """
        e = int(edge)
        src = int(_DB682_REFLECTION_EDGE[e])
        pulled = tuple(
            int(_DB682_REFLECTION_EDGE[int(x)]) for x in reversed(tuple(subseq))
        )
        return self._v015_h2_row_mask(src, pulled)

    def _v015_selected_support_mask(self, which: int) -> int:
        """Recompute exact H2/H5 support from every currently fixed row."""
        if which == 2:
            if not self.use_v015_h2_language:
                return self._v015_h2_all_mask
            selected = _DB682_H2_SELECTED_SET
            rows = _DB682_H2_SELECTED
            row_mask = self._v015_h2_row_mask
            self.stats.v015_h2_queries += 1
        elif which == 5:
            if not self.use_v015_h5_language:
                return self._v015_h2_all_mask
            selected = _DB682_H5_SELECTED_SET
            rows = tuple(_DB682_REFLECTION_EDGE[e] for e in _DB682_H2_SELECTED)
            row_mask = self._v015_h5_row_mask
            self.stats.v015_h5_queries += 1
        else:
            raise ValueError("v0.15 selected support requires which=2 or 5.")
        mask = self._v015_h2_all_mask
        for e in rows:
            seq = tuple(x for x in self.pi[int(e)] if x in selected)
            if not seq:
                continue
            mask &= int(row_mask(int(e), seq))
            if not mask:
                break
        return int(mask)

    def _v015_refine_selected_mask(
        self, parent_mask: int, changed_edges: Sequence[int], which: int
    ) -> int:
        """Exact incremental H2/H5 support refinement after insertions only."""
        if which == 2:
            if not self.use_v015_h2_language:
                return self._v015_h2_all_mask
            selected = _DB682_H2_SELECTED_SET
            row_mask = self._v015_h2_row_mask
            self.stats.v015_h2_refinements += 1
        elif which == 5:
            if not self.use_v015_h5_language:
                return self._v015_h2_all_mask
            selected = _DB682_H5_SELECTED_SET
            row_mask = self._v015_h5_row_mask
            self.stats.v015_h5_refinements += 1
        else:
            raise ValueError("v0.15 selected support requires which=2 or 5.")
        mask = int(parent_mask)
        seen = set()
        for e0 in changed_edges:
            e = int(e0)
            if e in seen or e not in selected:
                continue
            seen.add(e)
            seq = tuple(x for x in self.pi[e] if x in selected)
            mask &= int(row_mask(e, seq))
            if not mask:
                break
        return int(mask)

    def _v015_child_selected_mask(
        self, parent_mask: Optional[int], changed_edges: Sequence[int], which: int
    ) -> int:
        if which == 2 and not self.use_v015_h2_language:
            return self._v015_h2_all_mask
        if which == 5 and not self.use_v015_h5_language:
            return self._v015_h2_all_mask
        if parent_mask is None:
            parent_mask = self._v015_selected_support_mask(which)
        return self._v015_refine_selected_mask(int(parent_mask), changed_edges, which)

    def _v015_supports_dead(self, c8_mask: int, h2_mask: int, h5_mask: int) -> bool:
        if self.use_v013_c8_language and not int(c8_mask):
            return True
        if self.use_v015_h2_language and not int(h2_mask):
            return True
        if self.use_v015_h5_language and not int(h5_mask):
            return True
        return False

    def _v015_mark_support_prune(
        self, killed: int, c8_mask: int, h2_mask: int, h5_mask: int
    ) -> None:
        """Credit one exact zero-support subtree once, with deterministic attribution."""
        killed = int(killed)
        if self.use_v013_c8_language and not int(c8_mask):
            self.stats.c8_language_prunes += 1
            self.stats.c8_language_candidates_pruned += killed
        elif self.use_v015_h2_language and not int(h2_mask):
            self.stats.v015_h2_prunes += 1
            self.stats.v015_h2_candidates_pruned += killed
        elif self.use_v015_h5_language and not int(h5_mask):
            self.stats.v015_h5_prunes += 1
            self.stats.v015_h5_candidates_pruned += killed
        else:
            raise AssertionError("v0.15 support-prune accounting called on a supported state.")
        self._mark_resolved(killed, "planarity")

    @staticmethod
    def _compact_pi_key(selected: Sequence[int], projected: Pi, *, marker: int = 255) -> bytes:
        """Bijectively serialize one exact projected Pi state for DB(6,8,-2).

        Edge IDs are 0..11, so one-byte fields are exact.  The marker separates
        cache namespaces.  Equality of these bytes is exact state equality; no
        probabilistic digest is used to authorize pruning.
        """
        selected = tuple(int(e) for e in selected)
        if len(selected) >= 255 or any(e < 0 or e >= 255 for e in selected):
            raise AssertionError("Compact DB682 cache key edge range violated.")
        out = bytearray((marker & 255, len(selected)))
        out.extend(selected)
        for e in selected:
            seq = tuple(int(x) for x in projected[e])
            if len(seq) >= 255 or any(x < 0 or x >= 255 for x in seq):
                raise AssertionError("Compact DB682 cache key Pi range violated.")
            out.extend((e, len(seq)))
            out.extend(seq)
        return bytes(out)

    @staticmethod
    def _lru_get(cache: OrderedDict, key):
        try:
            value = cache.pop(key)
        except KeyError:
            return None, False
        cache[key] = value
        return value, True

    @staticmethod
    def _lru_put(cache: OrderedDict, key, value, limit: int) -> None:
        if key in cache:
            cache.pop(key)
        cache[key] = value
        while len(cache) > max(1, int(limit)):
            cache.popitem(last=False)

    @staticmethod
    def _literal_edge_set(H: nx.Graph) -> FrozenSet[FrozenSet[Hashable]]:
        return frozenset(frozenset((u, v)) for u, v in H.edges)

    def _core_gap_positions(self, host: int, current: int, gap: int) -> Tuple[int, ...]:
        """All exact slots on host giving ``gap`` preceding C6 crossings."""
        seq = self.pi[host]
        positions = []
        for pos in range(len(seq) + 1):
            before = sum(1 for x in seq[:pos] if x in self.db682_core_set)
            if before == gap:
                positions.append(pos)
        if not positions:
            raise AssertionError(
                f"No exact insertion slot realizes C6 gap {gap} on edge {host}."
            )
        return tuple(positions)

    def _remaining_extra_factor(self, extras: Sequence[int], start: int, current_len: int) -> int:
        """Exact number of completions of uninserted q-vs-q crossings.

        Extras are inserted in one fixed deterministic order. At each insertion,
        choosing a slot on the current edge and a slot on the older edge is
        bijective with the resulting final pair of Pi orders.  Removing extras
        in reverse fixed order recovers the choices uniquely.
        """
        factor = 1
        length = current_len
        for old in extras[start:]:
            factor *= (length + 1) * (len(self.pi[old]) + 1)
            length += 1
        return factor

    def _stage_allowed_weight(
        self,
        edge_index: int,
        domain: Sequence[DB682LocalSignature],
        partners: Sequence[int],
        extras: Sequence[int],
    ) -> Tuple[int, List[Tuple[DB682LocalSignature, Tuple[Tuple[int, ...], ...], int]]]:
        """Return exact stage assignments whose C6 projection is locally planar."""
        current = self.order[edge_index]
        k = len(partners)
        extra_factor = self._remaining_extra_factor(extras, 0, k)
        prepared = []
        allowed = 0
        for sig in domain:
            if set(sig.core_order) != set(partners) or len(sig.core_order) != k:
                raise AssertionError("Local-domain signature partner set mismatch.")
            if len(sig.core_gaps) != k:
                raise AssertionError("Local-domain gap vector length mismatch.")
            slot_lists = tuple(
                self._core_gap_positions(host, current, gap)
                for host, gap in zip(partners, sig.core_gaps)
            )
            slot_count = prod(len(x) for x in slot_lists)
            w = slot_count * extra_factor
            allowed += w
            prepared.append((sig, slot_lists, w))
        return allowed, prepared

    def _selected_restriction_state(
        self,
        edge_index: int,
        included_extra_count: int,
        extras: Tuple[int, ...],
    ) -> Tuple[Tuple[int, ...], Pi, bytes]:
        """Return one COMPLETE selected-edge restriction and its exact key.

        Pending nonincident q-edges are deleted entirely; no incomplete
        arbitrary-gap graph is ever returned from this routine.
        """
        current = self.order[edge_index]
        expected_extras = tuple(
            e for e in self.older_required[edge_index] if e not in self.db682_core_set
        )
        if tuple(extras) != expected_extras:
            raise AssertionError(
                "v0.11 superdomain safety guard: extras do not equal the exact "
                f"non-core older requirements; got={tuple(extras)}, expected={expected_extras}."
            )
        if not (0 <= int(included_extra_count) <= len(extras)):
            raise AssertionError("v0.11 superdomain safety guard: included-extra count out of range.")

        for j, old in enumerate(extras):
            in_current = old in self.pi[current]
            in_old = current in self.pi[old]
            if j < included_extra_count:
                if not (in_current and in_old):
                    raise AssertionError(
                        "v0.11 superdomain safety guard: an included extra crossing "
                        f"is not present symmetrically for current={current}, old={old}."
                    )
            else:
                if in_current or in_old:
                    raise AssertionError(
                        "v0.11 superdomain safety guard: a pending extra crossing "
                        f"was already present for current={current}, old={old}."
                    )

        older_q = tuple(self.order[6:edge_index])
        pending = set(extras[included_extra_count:])
        selected_older_q = tuple(q for q in older_q if q not in pending)
        selected = tuple(self.db682_core_edges) + selected_older_q + (current,)
        if len(selected) != len(set(selected)):
            raise AssertionError("v0.11 selected restriction contains a duplicate original edge.")
        selected_set = set(selected)

        projected: Pi = {e.id: [] for e in self.G.edges}
        for e in selected:
            seq = [x for x in self.pi[e] if x in selected_set]
            if len(seq) != len(set(seq)):
                raise AssertionError(
                    f"v0.11 selected restriction has a duplicate crossing on edge {e}."
                )
            projected[e] = seq

        for e in selected:
            expected = {f for f in self.G._nonincident[e] if f in selected_set}
            if set(projected[e]) != expected or len(projected[e]) != len(expected):
                raise AssertionError(
                    "v0.11 superdomain safety guard: selected restriction is incomplete "
                    f"on edge {e}; got={projected[e]}, expected={sorted(expected)}."
                )
        modeled_pairs(projected, selected)
        key = self._compact_pi_key(selected, projected, marker=161)
        return selected, projected, key

    def _cache_completed_answer(self, key: bytes, planar: bool) -> None:
        self._lru_put(
            self.db682_superdomain_cache,
            key,
            bool(planar),
            self.db682_superdomain_cache_limit,
        )
        self.stats.superdomain_cache_entries = len(self.db682_superdomain_cache)

    def _certificate_or_iso_answer(
        self,
        selected: Tuple[int, ...],
        H: nx.Graph,
    ) -> Optional[bool]:
        """Try only exact reusable certificates; return None if unresolved."""
        edge_set = None
        if self.use_v011_kuratowski_learning:
            certs = self.db682_kuratowski_by_selected[tuple(selected)]
            if certs:
                edge_set = self._literal_edge_set(H)
                for cert in certs:
                    self.stats.v011_kuratowski_checks += 1
                    if cert.issubset(edge_set):
                        self.stats.v011_kuratowski_hits += 1
                        return False

        if self.use_v011_exact_iso_cache:
            wl = nx.weisfeiler_lehman_graph_hash(H)
            bucket_key = (tuple(selected), H.number_of_nodes(), H.number_of_edges(), wl)
            for representative, answer in self.db682_iso_cache[bucket_key]:
                self.stats.v011_iso_checks += 1
                if nx.is_isomorphic(H, representative):
                    self.stats.v011_iso_hits += 1
                    return bool(answer)
        return None

    def _learn_completed_graph_fact(
        self,
        selected: Tuple[int, ...],
        H: nx.Graph,
        planar: bool,
    ) -> None:
        """Learn only facts whose reuse has an exact proof."""
        if self.use_v011_kuratowski_learning and not planar and hasattr(self.planarity, "kuratowski_edges"):
            certs = self.db682_kuratowski_by_selected[tuple(selected)]
            if len(certs) < self.db682_kuratowski_limit_per_selected:
                t0 = time.perf_counter()
                cert = self.planarity.kuratowski_edges(H)
                self.stats.kuratowski_certificate_seconds += time.perf_counter() - t0
                if cert:
                    edge_set = self._literal_edge_set(H)
                    if not cert.issubset(edge_set):
                        raise AssertionError("Boost Kuratowski certificate is not a literal subgraph.")
                    if self.debug:
                        K = nx.Graph()
                        K.add_edges_from(tuple(e) for e in cert)
                        if nx.is_planar(K):
                            raise AssertionError("v0.11 learned Kuratowski certificate is planar.")
                    if cert not in certs:
                        certs.append(cert)
                        self.stats.v011_kuratowski_learned += 1
                        self.stats.kuratowski_certificates_learned += 1

        if self.use_v011_exact_iso_cache:
            wl = nx.weisfeiler_lehman_graph_hash(H)
            bucket_key = (tuple(selected), H.number_of_nodes(), H.number_of_edges(), wl)
            bucket = self.db682_iso_cache[bucket_key]
            already = False
            for representative, answer in bucket:
                self.stats.v011_iso_checks += 1
                if nx.is_isomorphic(H, representative):
                    if bool(answer) != bool(planar):
                        raise AssertionError("Exact-isomorphism cache has inconsistent planarity answers.")
                    already = True
                    break
            if not already and len(bucket) < self.db682_iso_cache_limit_per_bucket:
                bucket.append((H.copy(), bool(planar)))

    def _classify_completed_graph_batch(
        self,
        items: Sequence[Tuple[bytes, Tuple[int, ...], nx.Graph]],
    ) -> List[bool]:
        """Classify complete restrictions using exact cache/certificates/batching."""
        answers: List[Optional[bool]] = [None] * len(items)
        unresolved_indices: List[int] = []
        unresolved_graphs: List[nx.Graph] = []

        for i, (key, selected, H) in enumerate(items):
            cached, hit = self._lru_get(self.db682_superdomain_cache, key)
            if hit:
                self.stats.superdomain_cache_hits += 1
                answers[i] = bool(cached)
                continue
            reusable = self._certificate_or_iso_answer(selected, H)
            if reusable is not None:
                answers[i] = bool(reusable)
                self._cache_completed_answer(key, bool(reusable))
                continue
            unresolved_indices.append(i)
            unresolved_graphs.append(H)

        if unresolved_graphs:
            t0 = time.perf_counter()
            if hasattr(self.planarity, "batch_graph_planarity") and len(unresolved_graphs) > 1:
                raw = self.planarity.batch_graph_planarity(
                    unresolved_graphs, workers=max(1, int(self.stats.planarity_workers))
                )
                elapsed = time.perf_counter() - t0
                self.stats.v011_batch_calls += 1
                self.stats.v011_batch_graphs += len(unresolved_graphs)
                self.stats.v011_batch_seconds += elapsed
            else:
                raw = [self.planarity.is_planar(H) for H in unresolved_graphs]
                elapsed = time.perf_counter() - t0
            self.stats.superdomain_seconds += elapsed
            self.stats.superdomain_tests += len(unresolved_graphs)

            for idx, planar in zip(unresolved_indices, raw):
                key, selected, H = items[idx]
                planar = bool(planar)
                if self.debug:
                    nx_answer = nx.is_planar(H)
                    if planar != nx_answer:
                        raise AssertionError(
                            "v0.11 Boost/NetworkX mismatch on an exact completed restriction."
                        )
                answers[idx] = planar
                self._learn_completed_graph_fact(selected, H, planar)
                self._cache_completed_answer(key, planar)

        if any(a is None for a in answers):
            raise AssertionError("v0.11 completed-graph batch left an unresolved answer.")
        return [bool(a) for a in answers]

    def _classify_completed_pi_batch(
        self,
        selected: Tuple[int, ...],
        items: Sequence[Tuple[bytes, Pi]],
    ) -> List[bool]:
        """v0.12 classify COMPLETE selected restrictions, preferably direct in C++.

        Cache equality is exact byte-for-byte Pi equality.  The direct route is
        used only as an implementation accelerator for the same completed
        augmented graph.  If direct encoding is unavailable, or if optional
        graph-level learning is requested, this falls back to the independently
        verified v0.11 NetworkX construction path.
        """
        items = list(items)
        answers: List[Optional[bool]] = [None] * len(items)
        unresolved_indices: List[int] = []
        unresolved_pis: List[Pi] = []
        for i, (key, projected) in enumerate(items):
            cached, hit = self._lru_get(self.db682_superdomain_cache, key)
            if hit:
                self.stats.superdomain_cache_hits += 1
                answers[i] = bool(cached)
            else:
                unresolved_indices.append(i)
                unresolved_pis.append(projected)

        if unresolved_pis:
            can_direct = (
                self.use_v012_direct_pi_encoder
                and hasattr(self.planarity, "batch_complete_pi_planarity")
                and not self.use_v011_kuratowski_learning
                and not self.use_v011_exact_iso_cache
            )
            if can_direct:
                t0 = time.perf_counter()
                raw = self.planarity.batch_complete_pi_planarity(
                    self.G, selected, unresolved_pis,
                    oriented=self.oriented,
                    workers=max(1, int(self.stats.planarity_workers)),
                )
                elapsed = time.perf_counter() - t0
                self.stats.direct_pi_batch_calls += 1
                self.stats.direct_pi_batch_graphs += len(unresolved_pis)
                self.stats.direct_pi_batch_seconds += elapsed
                self.stats.superdomain_seconds += elapsed
                self.stats.superdomain_tests += len(unresolved_pis)
                for local_i, planar in enumerate(raw):
                    idx = unresolved_indices[local_i]
                    key, projected = items[idx]
                    planar = bool(planar)
                    if self.debug:
                        H = build_active_augmented_minor(
                            self.G, projected, selected, self.oriented,
                            validate=True, crossing_cache=self.crossing_cache,
                        )
                        if planar != nx.is_planar(H):
                            raise AssertionError(
                                "v0.12 direct completed-Pi encoder disagrees with NetworkX."
                            )
                    answers[idx] = planar
                    self._cache_completed_answer(key, planar)
            else:
                graph_items = []
                for idx in unresolved_indices:
                    key, projected = items[idx]
                    H = build_active_augmented_minor(
                        self.G, projected, selected, self.oriented,
                        validate=True, crossing_cache=self.crossing_cache,
                    )
                    graph_items.append((key, selected, H))
                vals = self._classify_completed_graph_batch(graph_items)
                for idx, planar in zip(unresolved_indices, vals):
                    answers[idx] = bool(planar)

        if any(a is None for a in answers):
            raise AssertionError("v0.12 completed-Pi batch left an unresolved answer.")
        return [bool(a) for a in answers]


    def _completed_selected_restriction_planar(
        self,
        edge_index: int,
        included_extra_count: int,
        extras: Tuple[int, ...],
    ) -> bool:
        """Exact v0.11 complete selected-restriction planarity certificate."""
        selected, projected, key = self._selected_restriction_state(
            edge_index, included_extra_count, extras
        )
        cached, hit = self._lru_get(self.db682_superdomain_cache, key)
        if hit:
            self.stats.superdomain_cache_hits += 1
            return bool(cached)

        return self._classify_completed_pi_batch(
            selected, [(key, projected)]
        )[0]

    def _whole_stage_parent_key(
        self,
        edge_index: int,
        extras: Tuple[int, ...],
    ) -> Tuple[bytes, Tuple[int, ...], Pi]:
        """Exact selected-parent key for the q6/q11 zero-extra theorem."""
        current = self.order[edge_index]
        older_q = tuple(self.order[6:edge_index])
        pending = set(extras)
        selected_base = tuple(self.db682_core_edges) + tuple(q for q in older_q if q not in pending)
        selected_set = set(selected_base)
        projected: Pi = {e.id: [] for e in self.G.edges}
        for e in selected_base:
            projected[e] = [x for x in self.pi[e] if x in selected_set]
            expected = {f for f in self.G._nonincident[e] if f in selected_set}
            if set(projected[e]) != expected or len(projected[e]) != len(expected):
                raise AssertionError(
                    "v0.11 whole-stage parent is not a complete selected restriction."
                )
        modeled_pairs(projected, selected_base)
        key = self._compact_pi_key(selected_base, projected, marker=200 + int(current))
        return key, selected_base, projected

    def _whole_stage_dead_certificate(
        self,
        edge_index: int,
        domain: Sequence[DB682LocalSignature],
        partners: Tuple[int, ...],
        extras: Tuple[int, ...],
    ) -> bool:
        """Exact bulk DEAD certificate for the observed q6/q11 bottlenecks.

        For the exact selected parent, enumerate every DISTINCT complete
        zero-extra restriction obtained by adding ``current`` with any locally
        allowed C6 signature and any projected C6-host slot. Pending q-edges are
        deleted entirely. Every exact full stage assignment projects to one of
        these complete restrictions. If all are nonplanar, no completed stage
        extension can be planar. If one is planar, return False (UNKNOWN for
        this theorem) and fall back to the frozen v0.10 recursion.
        """
        current = self.order[edge_index]
        if current not in (6, 11) or not extras:
            return False
        self.stats.whole_stage_calls += 1
        t_started = time.perf_counter()

        parent_key, selected_base, projected_base = self._whole_stage_parent_key(
            edge_index, extras
        )
        cached, hit = self._lru_get(self.db682_whole_stage_cache, parent_key)
        if hit:
            self.stats.whole_stage_cache_hits += 1
            self.stats.whole_stage_seconds += time.perf_counter() - t_started
            return bool(cached)

        selected = tuple(selected_base) + (current,)
        selected_set = set(selected)
        base_set = set(selected_base)
        items_by_key: OrderedDict[bytes, Tuple[bytes, Pi]] = OrderedDict()

        for sig in domain:
            self._check_limits()
            if set(sig.core_order) != set(partners) or len(sig.core_gaps) != len(partners):
                raise AssertionError("v0.11 whole-stage local-domain signature mismatch.")
            projected_slot_lists: List[Tuple[int, ...]] = []
            for host, gap in zip(partners, sig.core_gaps):
                seq = projected_base[host]
                projected_positions = tuple(
                    pos for pos in range(len(seq) + 1)
                    if sum(1 for x in seq[:pos] if x in self.db682_core_set) == gap
                )
                if not projected_positions:
                    raise AssertionError("v0.11 whole-stage projection has no legal host slot.")

                full_positions = self._core_gap_positions(host, current, gap)
                mapped = {
                    sum(1 for x in self.pi[host][:pos] if x in base_set)
                    for pos in full_positions
                }
                if mapped != set(projected_positions):
                    raise AssertionError(
                        "v0.11 whole-stage quotient failed exact slot-cover guard: "
                        f"host={host}, gap={gap}, mapped={sorted(mapped)}, "
                        f"projected={list(projected_positions)}."
                    )
                projected_slot_lists.append(projected_positions)

            for proj_combo in product(*projected_slot_lists):
                projected: Pi = {e.id: [] for e in self.G.edges}
                for e in selected_base:
                    projected[e] = list(projected_base[e])
                projected[current] = list(sig.core_order)
                for host, pos in zip(partners, proj_combo):
                    projected[host].insert(pos, current)

                for e in selected:
                    seq = projected[e]
                    if len(seq) != len(set(seq)):
                        raise AssertionError("v0.11 whole-stage projected Pi has a duplicate.")
                    expected = {f for f in self.G._nonincident[e] if f in selected_set}
                    if set(seq) != expected or len(seq) != len(expected):
                        raise AssertionError(
                            "v0.11 whole-stage projected restriction is incomplete "
                            f"on edge {e}: got={seq}, expected={sorted(expected)}."
                        )
                modeled_pairs(projected, selected)
                key = self._compact_pi_key(selected, projected, marker=161)
                if key in items_by_key:
                    continue
                items_by_key[key] = (key, projected)

        if not items_by_key:
            raise AssertionError("v0.11 whole-stage theorem enumerated zero projection classes.")
        self.stats.whole_stage_projection_classes += len(items_by_key)
        answers = self._classify_completed_pi_batch(
            selected, list(items_by_key.values())
        )
        dead = not any(answers)

        self._lru_put(
            self.db682_whole_stage_cache,
            parent_key,
            bool(dead),
            self.db682_whole_stage_cache_limit,
        )
        if dead:
            self.stats.whole_stage_dead_parents += 1
        self.stats.whole_stage_seconds += time.perf_counter() - t_started
        return bool(dead)

    def _endpoint_signature_dead(
        self,
        edge_index: int,
        sig: DB682LocalSignature,
        partners: Tuple[int, ...],
        slot_lists: Tuple[Tuple[int, ...], ...],
    ) -> bool:
        """v0.12 hoist the already-proved q6/q11 certificate to q7/q10.

        q7 is rejected only if EVERY complete C6+q7+q6 restriction extending
        its exact C6 projection is nonplanar.  q10 is treated symmetrically via
        C6+q10+q11.  The intermediate q edges are deleted, so this test depends
        only on the exact C6 core plus the current local signature.

        A True result is therefore a necessary-condition failure for every full
        completion.  A False result means UNKNOWN and ordinary exact recursion
        continues.  No incomplete arbitrary-gap graph is tested here.
        """
        if not self.use_v012_endpoint_hoisting:
            return False
        current = self.order[edge_index]
        child = 6 if current == 7 else 11 if current == 10 else None
        if child is None:
            return False
        if child not in self.order[edge_index + 1:]:
            raise AssertionError("v0.12 endpoint child must occur later in the activation order.")

        # Exact signature cache is per worker/core.  core_order has fixed length
        # and gaps are one-byte C6 gap indices, so this serialization is bijective.
        skey = bytes((current, len(sig.core_order), *sig.core_order, *sig.core_gaps))
        self.stats.endpoint_queries += 1
        cached, hit = self._lru_get(self.db682_endpoint_cache, skey)
        if hit:
            self.stats.endpoint_cache_hits += 1
            return bool(cached)

        child_index = self.order.index(child)
        child_older = tuple(self.older_required[child_index])
        child_partners = tuple(e for e in self.db682_core_edges if e in child_older)
        child_extras = tuple(e for e in child_older if e not in self.db682_core_set)
        child_domain = self.db682_local_domains[child]
        if not child_extras:
            raise AssertionError("v0.12 endpoint theorem expected deleted pending q edges.")

        # Make the current C6 projection symmetric using one canonical exact host
        # slot from each gap class.  Any older non-core q edges occupying those
        # host lists are deliberately projected away by the child theorem.  The
        # exact-cover guard inside _whole_stage_dead_certificate verifies that
        # every full host slot maps to the projected classes it enumerates.
        inserted = []
        t0 = time.perf_counter()
        try:
            for host, positions in zip(partners, slot_lists):
                if not positions:
                    raise AssertionError("v0.12 endpoint signature has no canonical host slot.")
                pos = positions[0]
                self.pi[host].insert(pos, current)
                inserted.append((host, pos))
            before_hits = self.stats.whole_stage_cache_hits
            dead = self._whole_stage_dead_certificate(
                child_index, child_domain, child_partners, child_extras
            )
            if self.stats.whole_stage_cache_hits > before_hits:
                # Normally the signature cache catches repeats first, but this
                # records exact-parent reuse reached through another path.
                self.stats.endpoint_cache_hits += 1
        finally:
            for host, pos in reversed(inserted):
                got = self.pi[host].pop(pos)
                if got != current:
                    raise AssertionError("v0.12 endpoint canonical insertion failed to restore Pi.")
            self.stats.endpoint_seconds += time.perf_counter() - t0

        self._lru_put(
            self.db682_endpoint_cache, skey, bool(dead), self.db682_endpoint_cache_limit
        )
        return bool(dead)


    def _factorized_locked_planar(self, edge_index: int) -> bool:
        """Stage-complete planarity checkpoint for factorized search.

        SAFETY GUARD (v0.9.1-safe): factorized enumeration may insert future
        q-vs-q crossings into arbitrary gaps, so an incomplete factorized state
        is *not* a chronological prefix and must never be used for planarity
        pruning.  This routine therefore refuses to run unless every crossing
        required at the current activation stage has already been modeled.

        At stage completion, ``_locked_prefix_planar`` specializes to the full
        augmented graph of the completed active-edge subgraph, which is a true
        restriction/minor of every full completion.  Nonplanarity is therefore
        safely hereditary.
        """
        current = self.order[edge_index]
        if len(self.pi[current]) != len(self.older_required[edge_index]):
            raise AssertionError(
                "v0.9.1 safety guard: attempted planarity pruning on an "
                "incomplete arbitrary-gap factorized stage."
            )
        return self._locked_prefix_planar(edge_index)

    def _search_factorized_extras(
        self,
        edge_index: int,
        extras: Tuple[int, ...],
        extra_index: int,
        c8_support_mask: Optional[int] = None,
        h2_support_mask: Optional[int] = None,
        h5_support_mask: Optional[int] = None,
    ) -> bool:
        current = self.order[edge_index]
        suffix = self.suffix_after[edge_index]
        if extra_index == len(extras):
            # The stage is complete. The preceding locked-prefix call (or the
            # no-extra call in the caller) used the complete active augmented
            # graph. Recurse to the next exact stage, or independently validate
            # a possible full witness.
            if edge_index + 1 == len(self.order):
                self.stats.full_planarity_tests += 1
                H = build_augmented_graph(
                    self.G, self.pi, oriented=self.oriented,
                    validate=True, crossing_cache=self.crossing_cache,
                )
                t0 = time.perf_counter()
                planar = self.planarity.is_planar(H)
                self.stats.planarity_seconds += time.perf_counter() - t0
                self._mark_resolved(1, "full")
                if planar:
                    if not nx.is_planar(H):
                        raise AssertionError("v0.9 witness failed independent NetworkX validation.")
                    self.witness = {eid: list(v) for eid, v in self.pi.items()}
                    return True
                return False
            return self._search_factorized_stage(
                edge_index + 1, c8_support_mask, h2_support_mask, h5_support_mask
            )

        old = extras[extra_index]
        current_slots = range(len(self.pi[current]) + 1)
        old_slots = range(len(self.pi[old]) + 1)
        for pos_cur in current_slots:
            for pos_old in old_slots:
                self.stats.factorized_extra_choices += 1
                self.stats.recursive_calls += 1
                self._check_limits()
                self.pi[current].insert(pos_cur, old)
                self.pi[old].insert(pos_old, current)
                self.current_modeled_crossings += 1
                self.stats.max_modeled_crossings = max(
                    self.stats.max_modeled_crossings, self.current_modeled_crossings
                )

                # v0.15 exact support propagation.  C8, H2=C8+e2, and
                # H5=C8+e5 are all COMPLETE selected-edge restriction languages.
                # Future insertions can only strengthen the already-fixed row
                # subsequences, so zero support in any enabled language is a
                # hereditary impossibility certificate.  No incomplete graph is
                # planarity-tested here.
                child_c8_mask = (
                    self._v014_c8_child_mask(c8_support_mask, (current, old))
                    if self.use_v013_c8_language else self._v013_c8_all_mask
                )
                child_h2_mask = (
                    self._v015_child_selected_mask(h2_support_mask, (current, old), 2)
                    if self.use_v015_h2_language else self._v015_h2_all_mask
                )
                child_h5_mask = (
                    self._v015_child_selected_mask(h5_support_mask, (current, old), 5)
                    if self.use_v015_h5_language else self._v015_h2_all_mask
                )
                support_dead = self._v015_supports_dead(
                    child_c8_mask, child_h2_mask, child_h5_mask
                )
                if support_dead:
                    remaining = self._remaining_extra_factor(
                        extras, extra_index + 1, len(self.pi[current])
                    )
                    killed = remaining * suffix
                    self._v015_mark_support_prune(
                        killed, child_c8_mask, child_h2_mask, child_h5_mask
                    )
                # v0.10: never planarity-test the incomplete arbitrary-gap
                # active graph.  Instead, delete every still-pending nonincident
                # q edge and test the COMPLETE selected-edge restriction.
                # Nonplanarity of that literal subgraph safely kills every way
                # of inserting the pending extras and every later stage.
                elif self.use_exact_superdomain_pruning:
                    planar_restriction = self._completed_selected_restriction_planar(
                        edge_index, extra_index + 1, extras
                    )
                    if not planar_restriction:
                        remaining = self._remaining_extra_factor(
                            extras, extra_index + 1, len(self.pi[current])
                        )
                        killed = remaining * suffix
                        self.stats.superdomain_prunes += 1
                        self.stats.superdomain_candidates_pruned += killed
                        self._mark_resolved(killed, "planarity")
                    elif extra_index + 1 == len(extras):
                        # At the final extra the selected restriction is exactly
                        # the complete active stage, so its planar answer replaces
                        # the duplicate stage-complete checkpoint.
                        if self._search_factorized_extras(
                            edge_index, extras, extra_index + 1,
                            child_c8_mask, child_h2_mask, child_h5_mask
                        ):
                            return True
                    else:
                        if self._search_factorized_extras(
                            edge_index, extras, extra_index + 1,
                            child_c8_mask, child_h2_mask, child_h5_mask
                        ):
                            return True
                else:
                    # Frozen v0.9.1 reference behavior.
                    if extra_index + 1 == len(extras):
                        planar = self._factorized_locked_planar(edge_index)
                        if not planar:
                            self._mark_resolved(suffix, "planarity")
                        else:
                            if self._search_factorized_extras(
                                edge_index, extras, extra_index + 1,
                                child_c8_mask, child_h2_mask, child_h5_mask
                            ):
                                return True
                    else:
                        if self._search_factorized_extras(
                            edge_index, extras, extra_index + 1,
                            child_c8_mask, child_h2_mask, child_h5_mask
                        ):
                            return True

                got_old = self.pi[old].pop(pos_old)
                got_cur = self.pi[current].pop(pos_cur)
                self.current_modeled_crossings -= 1
                self.stats.backtracks += 1
                if got_old != current or got_cur != old:
                    raise AssertionError("Factorized extra crossing failed to restore Pi.")
                if self.stats.backtracks % 64 == 0:
                    self._maybe_report_progress()
        return False

    def _v015_process_core_slots(
        self,
        edge_index: int,
        current: int,
        partners: Tuple[int, ...],
        slot_lists: Tuple[Tuple[int, ...], ...],
        extras: Tuple[int, ...],
        sig_weight: int,
        sig_c8_mask: int,
        sig_h2_mask: int,
        sig_h5_mask: int,
    ) -> bool:
        """Enumerate exactly the support-relevant C6-host slots first.

        SAFETY. A host is called insensitive only when inserting ``current`` on
        that host changes none of the enabled selected restrictions C8, H2, H5.
        Therefore all exact support predicates are constant over its slot
        choices.  With support-driven mode enabled, sensitive hosts are handled
        one at a time.  If a prefix already has zero exact support, every choice
        of the remaining distinct-host slots has the same impossible prefix;
        their exact product multiplicity is credited and no child is generated.
        This is a reordering/factoring of the same Cartesian product, not a new
        topological inference.
        """
        suffix = self.suffix_after[edge_index]

        def host_sensitive(host: int) -> bool:
            h = int(host)
            return bool(
                (self.use_v013_c8_language and h in _DB682_C8_EDGE_SET)
                or (self.use_v015_h2_language and h in _DB682_H2_SELECTED_SET)
                or (self.use_v015_h5_language and h in _DB682_H5_SELECTED_SET)
            )

        sensitive_idx = tuple(j for j, host in enumerate(partners) if host_sensitive(host))
        insensitive_idx = tuple(j for j in range(len(partners)) if j not in sensitive_idx)
        sensitive_hosts = tuple(partners[j] for j in sensitive_idx)
        sensitive_lists = tuple(slot_lists[j] for j in sensitive_idx)
        insensitive_hosts = tuple(partners[j] for j in insensitive_idx)
        insensitive_lists = tuple(slot_lists[j] for j in insensitive_idx)
        insensitive_count = prod(len(x) for x in insensitive_lists) if insensitive_lists else 1
        extra_factor = self._remaining_extra_factor(extras, 0, len(self.pi[current]))
        sensitive_count = prod(len(x) for x in sensitive_lists) if sensitive_lists else 1
        if sensitive_count * insensitive_count * extra_factor != sig_weight:
            raise AssertionError(
                "v0.15 support-sensitive slot factorization changed exact signature weight."
            )

        def refine_one(c8m: int, h2m: int, h5m: int, host: int):
            if self.use_v013_c8_language and host in _DB682_C8_EDGE_SET:
                c8m = self._v014_c8_child_mask(c8m, (host,))
            if self.use_v015_h2_language and host in _DB682_H2_SELECTED_SET:
                h2m = self._v015_child_selected_mask(h2m, (host,), 2)
            if self.use_v015_h5_language and host in _DB682_H5_SELECTED_SET:
                h5m = self._v015_child_selected_mask(h5m, (host,), 5)
            return int(c8m), int(h2m), int(h5m)

        def enumerate_insensitive(c8m: int, h2m: int, h5m: int) -> bool:
            iterator = product(*insensitive_lists) if insensitive_lists else [()]
            for insensitive_combo in iterator:
                self.stats.factorized_core_slot_states += 1
                self.stats.recursive_calls += 1
                self._check_limits()
                for host, pos in zip(insensitive_hosts, insensitive_combo):
                    self.pi[host].insert(pos, current)
                if self._v014_continue_after_core_slots(
                    edge_index, extras, c8m, h2m, h5m
                ):
                    return True
                for host, pos in reversed(tuple(zip(insensitive_hosts, insensitive_combo))):
                    got = self.pi[host].pop(pos)
                    if got != current:
                        raise AssertionError(
                            "v0.15 insensitive C6-host insertion failed to restore Pi."
                        )
                self.stats.backtracks += 1
                if self.stats.backtracks % 64 == 0:
                    self._maybe_report_progress()
            return False

        if self.use_v015_support_driven_slots:
            remaining_counts = [1] * (len(sensitive_lists) + 1)
            for j in range(len(sensitive_lists) - 1, -1, -1):
                remaining_counts[j] = remaining_counts[j + 1] * len(sensitive_lists[j])

            def rec_sensitive(j: int, c8m: int, h2m: int, h5m: int) -> bool:
                if j == len(sensitive_hosts):
                    self.stats.v014_c8_sensitive_slot_bundles += 1
                    return enumerate_insensitive(c8m, h2m, h5m)
                host = sensitive_hosts[j]
                for pos in sensitive_lists[j]:
                    self.stats.v015_support_prefix_states += 1
                    self._check_limits()
                    self.pi[host].insert(pos, current)
                    nc8, nh2, nh5 = refine_one(c8m, h2m, h5m, host)
                    if self._v015_supports_dead(nc8, nh2, nh5):
                        logical_bundles = remaining_counts[j + 1]
                        killed = logical_bundles * insensitive_count * extra_factor * suffix
                        self.stats.v015_support_prefix_dead += 1
                        self.stats.v015_support_prefix_bundles_skipped += logical_bundles
                        self._v015_mark_support_prune(killed, nc8, nh2, nh5)
                    else:
                        if rec_sensitive(j + 1, nc8, nh2, nh5):
                            return True
                    got = self.pi[host].pop(pos)
                    if got != current:
                        raise AssertionError(
                            "v0.15 support-driven sensitive insertion failed to restore Pi."
                        )
                return False

            return rec_sensitive(0, sig_c8_mask, sig_h2_mask, sig_h5_mask)

        # Verification/reference traversal: enumerate each full sensitive tuple
        # before applying the same exact selected-language predicates.
        for sensitive_combo in product(*sensitive_lists) if sensitive_lists else [()]:
            self.stats.v014_c8_sensitive_slot_bundles += 1
            self._check_limits()
            for host, pos in zip(sensitive_hosts, sensitive_combo):
                self.pi[host].insert(pos, current)
            bc8, bh2, bh5 = sig_c8_mask, sig_h2_mask, sig_h5_mask
            for host in sensitive_hosts:
                bc8, bh2, bh5 = refine_one(bc8, bh2, bh5, host)
            if self._v015_supports_dead(bc8, bh2, bh5):
                killed = insensitive_count * extra_factor * suffix
                self._v015_mark_support_prune(killed, bc8, bh2, bh5)
            else:
                if enumerate_insensitive(bc8, bh2, bh5):
                    return True
            for host, pos in reversed(tuple(zip(sensitive_hosts, sensitive_combo))):
                got = self.pi[host].pop(pos)
                if got != current:
                    raise AssertionError("v0.15 sensitive C6-host insertion failed to restore Pi.")
        return False

    def _v014_continue_after_core_slots(
        self,
        edge_index: int,
        extras: Tuple[int, ...],
        c8_support_mask: Optional[int],
        h2_support_mask: Optional[int],
        h5_support_mask: Optional[int],
    ) -> bool:
        """Continue one exact stage after every C6-host slot is fixed.

        This routine contains no new pruning theorem.  It is the v0.13
        post-C8-support continuation factored into one place so the v0.14
        sensitive-slot bundling path and the reference path execute identical
        superdomain / stage-complete logic.
        """
        current = self.order[edge_index]
        suffix = self.suffix_after[edge_index]
        if extras and self.use_exact_superdomain_pruning:
            planar_restriction = self._completed_selected_restriction_planar(
                edge_index, 0, extras
            )
            if not planar_restriction:
                remaining = self._remaining_extra_factor(extras, 0, len(self.pi[current]))
                killed = remaining * suffix
                self.stats.superdomain_prunes += 1
                self.stats.superdomain_candidates_pruned += killed
                self._mark_resolved(killed, "planarity")
                return False
            return self._search_factorized_extras(
                edge_index, extras, 0, c8_support_mask, h2_support_mask, h5_support_mask
            )
        if not extras:
            planar = self._factorized_locked_planar(edge_index)
            if not planar:
                self._mark_resolved(suffix, "planarity")
                return False
            return self._search_factorized_extras(
                edge_index, extras, 0, c8_support_mask, h2_support_mask, h5_support_mask
            )
        return self._search_factorized_extras(
            edge_index, extras, 0, c8_support_mask, h2_support_mask, h5_support_mask
        )

    def _search_factorized_stage(
        self, edge_index: int, c8_support_mask: Optional[int] = None,
        h2_support_mask: Optional[int] = None, h5_support_mask: Optional[int] = None
    ) -> bool:
        self.current_edge_index = edge_index
        self.partial_active_index = edge_index
        self.stats.recursive_calls += 1
        self.stats.domain_stage_states += 1
        self._check_limits()
        self._maybe_report_progress()

        current = self.order[edge_index]
        if self.pi[current]:
            raise AssertionError("Factorized stage must begin with an empty current-edge Pi list.")
        if current not in self.db682_local_domains:
            raise AssertionError(f"No v0.9 local domain for target edge {current}.")

        older = tuple(self.older_required[edge_index])
        partners = tuple(e for e in self.db682_core_edges if e in older)
        extras = tuple(e for e in older if e not in self.db682_core_set)
        domain = self.db682_local_domains[current]
        suffix = self.suffix_after[edge_index]

        # v0.15 carries three exact selected-language supports.  The initial
        # seeded C6 state computes them once; every recursive child subsequently
        # passes strictly refined masks.
        if self.use_v013_c8_language and c8_support_mask is None:
            c8_support_mask = self._v013_c8_support_mask()
        elif c8_support_mask is None:
            c8_support_mask = self._v013_c8_all_mask
        if self.use_v015_h2_language and h2_support_mask is None:
            h2_support_mask = self._v015_selected_support_mask(2)
        elif h2_support_mask is None:
            h2_support_mask = self._v015_h2_all_mask
        if self.use_v015_h5_language and h5_support_mask is None:
            h5_support_mask = self._v015_selected_support_mask(5)
        elif h5_support_mask is None:
            h5_support_mask = self._v015_h2_all_mask

        # A zero support at the parent kills the entire unexpanded stage exactly.
        if self._v015_supports_dead(c8_support_mask, h2_support_mask, h5_support_mask):
            killed = self.stage_factor[edge_index] * suffix
            self._v015_mark_support_prune(killed, c8_support_mask, h2_support_mask, h5_support_mask)
            return False

        allowed_stage, prepared = self._stage_allowed_weight(
            edge_index, domain, partners, extras
        )
        stage_total = self.stage_factor[edge_index]
        if allowed_stage > stage_total:
            raise AssertionError(
                f"Allowed local-domain weight exceeds exact stage factor: {allowed_stage}>{stage_total}."
            )
        local_pruned = stage_total - allowed_stage
        if local_pruned:
            resolved = local_pruned * suffix
            self.stats.domain_pruned_stage_assignments += local_pruned
            self._mark_resolved(resolved, "planarity")

        # Strong exact accounting assertion for the reparameterization.  The raw
        # local signatures are k! choices of C6 order times one of four C6 gaps
        # on each host edge. Summing exact slots over all gaps gives len(pi[e])+1.
        k = len(partners)
        raw_by_factorization = factorial(k)
        for host in partners:
            raw_by_factorization *= len(self.pi[host]) + 1
        raw_by_factorization *= self._remaining_extra_factor(extras, 0, k)
        if raw_by_factorization != stage_total:
            raise AssertionError(
                "v0.9 stage-factor bijection failed: "
                f"factorized={raw_by_factorization}, original={stage_total}."
            )

        # v0.11 exact whole-stage DEAD theorem for q6/q11.  This runs only
        # after the local-domain and factorization cardinalities have been
        # checked.  If it succeeds, *every* locally allowed exact stage
        # assignment has a nonplanar complete zero-extra restriction, so all
        # allowed assignments (and every later suffix completion) are resolved
        # in one exact step.  A False result is only UNKNOWN and falls back to
        # the frozen v0.10 recursion below.
        if (
            extras
            and self.use_exact_whole_stage_pruning
            and current in (6, 11)
            and self._whole_stage_dead_certificate(edge_index, domain, partners, extras)
        ):
            killed = allowed_stage * suffix
            self.stats.whole_stage_candidates_pruned += killed
            self._mark_resolved(killed, "planarity")
            return False

        for sig, slot_lists, sig_weight in prepared:
            self.stats.domain_signatures_considered += 1
            self._check_limits()
            # The domain signature fixes the relative order of the C6 crossings
            # on current. Prior q crossings are deliberately not yet modeled and
            # may later be inserted in any gap.
            self.pi[current] = list(sig.core_order)
            self.current_modeled_crossings += k
            self.stats.max_modeled_crossings = max(
                self.stats.max_modeled_crossings, self.current_modeled_crossings
            )

            # Refine every enabled exact selected language on the newly fixed
            # current-edge C6 projection.
            sig_c8_mask = (
                self._v014_c8_child_mask(c8_support_mask, (current,))
                if self.use_v013_c8_language else self._v013_c8_all_mask
            )
            sig_h2_mask = (
                self._v015_child_selected_mask(h2_support_mask, (current,), 2)
                if self.use_v015_h2_language else self._v015_h2_all_mask
            )
            sig_h5_mask = (
                self._v015_child_selected_mask(h5_support_mask, (current,), 5)
                if self.use_v015_h5_language else self._v015_h2_all_mask
            )
            if self._v015_supports_dead(sig_c8_mask, sig_h2_mask, sig_h5_mask):
                killed = sig_weight * suffix
                self._v015_mark_support_prune(killed, sig_c8_mask, sig_h2_mask, sig_h5_mask)
                self.current_modeled_crossings -= k
                self.pi[current] = []
                continue

            # v0.12 endpoint certificate is unchanged and still runs before any
            # host-slot enumeration.
            if (
                current in (7, 10)
                and self.use_v012_endpoint_hoisting
                and self._endpoint_signature_dead(edge_index, sig, partners, slot_lists)
            ):
                killed = sig_weight * suffix
                self.stats.endpoint_dead_signatures += 1
                self.stats.endpoint_candidates_pruned += killed
                self._mark_resolved(killed, "planarity")
                self.current_modeled_crossings -= k
                self.pi[current] = []
                continue

            # v0.15 support-driven host-slot factoring.  The old v0.14
            # C8-sensitive switch remains the master OFF switch for this
            # reparameterization so disabling new features can reproduce the
            # frozen reference traversal exactly.
            if self.use_v014_c8_sensitive_slots and (
                self.use_v013_c8_language
                or self.use_v015_h2_language
                or self.use_v015_h5_language
            ):
                if self._v015_process_core_slots(
                    edge_index, current, partners, slot_lists, extras, sig_weight,
                    sig_c8_mask, sig_h2_mask, sig_h5_mask,
                ):
                    return True
            else:
                # Literal reference traversal over every C6-host slot tuple.
                for slot_combo in product(*slot_lists):
                    self.stats.factorized_core_slot_states += 1
                    self.stats.recursive_calls += 1
                    self._check_limits()
                    for host, pos in zip(partners, slot_combo):
                        self.pi[host].insert(pos, current)

                    slot_c8_mask = (
                        self._v014_c8_child_mask(sig_c8_mask, partners)
                        if self.use_v013_c8_language else self._v013_c8_all_mask
                    )
                    slot_h2_mask = (
                        self._v015_child_selected_mask(sig_h2_mask, partners, 2)
                        if self.use_v015_h2_language else self._v015_h2_all_mask
                    )
                    slot_h5_mask = (
                        self._v015_child_selected_mask(sig_h5_mask, partners, 5)
                        if self.use_v015_h5_language else self._v015_h2_all_mask
                    )
                    if self._v015_supports_dead(slot_c8_mask, slot_h2_mask, slot_h5_mask):
                        remaining = self._remaining_extra_factor(
                            extras, 0, len(self.pi[current])
                        )
                        killed = remaining * suffix
                        self._v015_mark_support_prune(
                            killed, slot_c8_mask, slot_h2_mask, slot_h5_mask
                        )
                    else:
                        if self._v014_continue_after_core_slots(
                            edge_index, extras, slot_c8_mask, slot_h2_mask, slot_h5_mask
                        ):
                            return True

                    for host, pos in reversed(tuple(zip(partners, slot_combo))):
                        got = self.pi[host].pop(pos)
                        if got != current:
                            raise AssertionError(
                                "Factorized C6-host insertion failed to restore Pi."
                            )
                    self.stats.backtracks += 1
                    if self.stats.backtracks % 64 == 0:
                        self._maybe_report_progress()

            self.current_modeled_crossings -= k
            self.pi[current] = []

        return False

    def run_seeded_factorized(self, core_pi: Pi, core_edges: Sequence[int]) -> SearchResult:
        core_total = _seed_search_with_core(self, core_pi, core_edges)
        self.started = time.perf_counter()
        self.last_progress = self.started
        self.last_report_time = self.started
        self.last_report_resolved = 0
        try:
            self._maybe_report_progress(force=True)
            found = self._search_factorized_stage(6)
            self.stats.elapsed_seconds = self._elapsed()
            self._maybe_report_progress(force=True)
            self._close_progress_line()
            if found:
                return SearchResult(
                    "THRACKLEABLE", self.witness, self.stats,
                    "Found a complete Pi extending this exact planar C6 core (v0.10 exact factorized/superdomain search).",
                )
            if self.stats.resolved_candidates != core_total:
                raise AssertionError(
                    "v0.10 factorized core search returned negative without exact 100% coverage: "
                    f"{self.stats.resolved_candidates}/{core_total}."
                )
            return SearchResult(
                "NONTHRACKLEABLE", None, self.stats,
                "Exhausted every completion of this exact planar C6 core with exact v0.10 domain factorization and completed-restriction superdomains.",
            )
        except SearchLimitReached as exc:
            self.stats.elapsed_seconds = self._elapsed()
            self._maybe_report_progress(force=True)
            self._close_progress_line()
            return SearchResult("INCONCLUSIVE", None, self.stats, str(exc))


def _db682_factorization_self_check(search: DB682FactorizedSearch) -> None:
    """Cheap invariant checks that do not prune or mutate the search space."""
    if tuple(search.order[:6]) != tuple(search.db682_core_edges):
        raise AssertionError("v0.10 factorized search requires the C6 as the first six edges.")
    tail = tuple(search.order[6:])
    if set(tail) != {6, 7, 8, 9, 10, 11} or len(tail) != 6:
        raise AssertionError(
            "v0.10 DB682 factorization requires the six non-C6 edges exactly once."
        )
    # Internal q edges 7..10 really do have the exact same local incidence to C6.
    base = tuple(e for e in search.db682_core_edges if e in search.G._nonincident[7])
    if len(base) != 6:
        raise AssertionError("Expected q7 to be nonincident to all six C6 edges.")
    core_vertices = set()
    for e in search.db682_core_edges:
        edge = search.G.edge_by_id[e]
        core_vertices.update((edge.u, edge.v))
    for q in (7, 8, 9, 10):
        partners = tuple(e for e in search.db682_core_edges if e in search.G._nonincident[q])
        edge = search.G.edge_by_id[q]
        if partners != base or edge.u in core_vertices or edge.v in core_vertices:
            raise AssertionError("Internal q-edge local-domain isomorphism precondition failed.")


def _db682_core_worker(payload: dict) -> dict:
    """Top-level multiprocessing worker for one disjoint C6-core extension space."""
    try:
        G = DB(6, 8, -2)
        order = list(payload["order"])
        core_edges = list(payload["core_edges"])
        core_pi = {int(k): list(v) for k, v in payload["core_pi"].items()}
        search = DB682FactorizedSearch(
            G,
            max_recursive_calls=payload.get("max_calls"),
            time_limit_seconds=payload.get("time_limit"),
            use_c6_restriction=False,
            branch_order="constrained",
            use_screening=False,
            use_lookahead=False,
            incremental_partial=False,
            debug=bool(payload.get("debug", False)),
            use_cache=False,
            progress_interval_seconds=None,
            graph_label=f"DB(6,8,-2) core {payload['core_index']}",
            planarity_backend=payload.get("planarity", "auto"),
            use_batch_screening=False,
            planarity_workers=int(payload.get("planarity_workers", 1)),
            use_kuratowski_cache=False,
            activation_order="custom",
            custom_activation_order=order,
            use_locked_prefix_pruning=True,
            core_edges=core_edges,
        )
        _db682_factorization_self_check(search)
        search.use_exact_superdomain_pruning = bool(payload.get("use_superdomain", True))
        search.use_exact_whole_stage_pruning = bool(payload.get("use_whole_stage", True))
        search.use_v012_endpoint_hoisting = bool(payload.get("use_endpoint_hoisting", True))
        search.use_v012_direct_pi_encoder = bool(payload.get("use_direct_pi_encoder", True))
        search.use_v013_c8_language = bool(payload.get("use_c8_language", True))
        search.use_v014_precomputed_c8_rows = bool(payload.get("use_v014_precomputed_c8_rows", True))
        search.use_v014_incremental_c8 = bool(payload.get("use_v014_incremental_c8", True))
        search.use_v014_c8_sensitive_slots = bool(payload.get("use_v014_c8_sensitive_slots", True))
        search.use_v015_h2_language = bool(payload.get("use_v015_h2_language", True))
        search.use_v015_h5_language = bool(payload.get("use_v015_h5_language", True))
        search.use_v015_support_driven_slots = bool(payload.get("use_v015_support_driven_slots", True))
        search.use_v011_kuratowski_learning = bool(payload.get("use_kuratowski_learning", False))
        search.use_v011_exact_iso_cache = bool(payload.get("use_exact_iso_cache", False))
        domains, domain_reports = _db682_build_local_domains(search, core_pi, core_edges)
        search.db682_local_domains = domains
        search.db682_local_domain_reports = domain_reports

        progress_proxy = payload.get("progress_proxy")
        progress_interval = float(payload.get("progress_interval") or 0.0)
        if progress_proxy is not None and progress_interval > 0:
            core_index = int(payload["core_index"])
            heartbeat = {"last": 0.0}

            def publish(force: bool = False):
                now = time.perf_counter()
                if not force and now - heartbeat["last"] < progress_interval:
                    return
                progress_proxy[core_index] = _core_progress_snapshot(search, core_index, "RUNNING")
                heartbeat["last"] = now

            search._maybe_report_progress = publish
            search._close_progress_line = lambda: None
            publish(force=True)

        result = search.run_seeded_factorized(core_pi, core_edges)
        if progress_proxy is not None and progress_interval > 0:
            final_snap = _core_progress_snapshot(search, int(payload["core_index"]), result.status)
            progress_proxy[int(payload["core_index"])] = final_snap
        return {
            "core_index": int(payload["core_index"]),
            "represented_cores": list(payload.get("represented_cores", [int(payload["core_index"])])),
            "status": result.status,
            "reason": result.reason,
            "witness_pi": result.witness_pi,
            "stats": asdict(result.stats),
            "order": order,
            "error": None,
        }
    except Exception:
        return {
            "core_index": int(payload.get("core_index", -1)),
            "represented_cores": list(payload.get("represented_cores", [int(payload.get("core_index", -1))])),
            "status": "ERROR",
            "reason": "Worker raised an exception.",
            "witness_pi": None,
            "stats": None,
            "order": payload.get("order"),
            "error": traceback.format_exc(),
        }


def run_db682_cores(
    *,
    processes: Optional[int] = None,
    time_limit_per_core: Optional[float] = None,
    max_calls_per_core: Optional[int] = None,
    planarity: str = "auto",
    planarity_workers_per_process: Optional[int] = None,
    use_superdomain: bool = True,
    use_whole_stage: bool = True,
    use_endpoint_hoisting: bool = True,
    use_direct_pi_encoder: bool = True,
    use_c8_language: bool = True,
    use_v014_precomputed_c8_rows: bool = True,
    use_v014_incremental_c8: bool = True,
    use_v014_c8_sensitive_slots: bool = True,
    use_v015_h2_language: bool = True,
    use_v015_h5_language: bool = True,
    use_v015_support_driven_slots: bool = True,
    use_automorphism_quotient: bool = True,
    use_kuratowski_learning: bool = False,
    use_exact_iso_cache: bool = False,
    report: Optional[str] = None,
    verbose: bool = True,
    core_indices: Optional[Sequence[int]] = None,
    progress: Optional[float] = 2.0,
    progress_mode: str = "auto",
) -> DB682CoreResult:
    """Safely search DB(6,8,-2) by exact C6-core orbits and local projection domains.

    The 46,648 nonplanar C6 core systems are eliminated before the large search.
    The eight remaining extension spaces are disjoint and may be searched in
    parallel.  A negative global conclusion is returned only if every one of the
    eight exact core searches finishes negative.
    """
    started = time.perf_counter()
    G = DB(6, 8, -2)
    if use_v015_h2_language or use_v015_h5_language:
        if _DB682_H2_LANGUAGE_COUNT <= 0:
            raise AssertionError("v0.15 selected-language pruning requested without frozen H2 data.")
        # Build the immutable complete-row support tables before forking so
        # Linux/WSL workers share the large integer masks copy-on-write.
        _db682_h2_row_mask_tables()
    orders = db682_candidate_activation_orders(G, limit=1)
    order = orders[0]
    cores, core_edges = enumerate_planar_c6_cores(G, activation_order=order, planarity=planarity)

    template = BacktrackingSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=False,
    )
    core_pattern_count = prod(template.stage_factor[:6])
    if core_pattern_count != 46656:
        raise AssertionError(f"C6-first search should have 46,656 core patterns; got {core_pattern_count}.")
    core_subtree = template.suffix_after[5]
    full_total = G.candidate_count()
    if core_pattern_count * core_subtree != full_total:
        raise AssertionError("C6-core factorization does not equal the full complete-Pi count.")
    excluded_patterns = core_pattern_count - len(cores)
    excluded_candidates = excluded_patterns * core_subtree

    cpu = max(1, os.cpu_count() or 1)
    if processes is None:
        processes = min(8, cpu)
    processes = max(1, min(int(processes), 8))
    if planarity_workers_per_process is None:
        planarity_workers_per_process = 1 if processes > 1 else min(4, cpu)
    planarity_workers_per_process = max(1, int(planarity_workers_per_process))

    if verbose:
        print("v0.15.0 exact H2/H5-supported factorized search for DB(6,8,-2)")
        print(f"  full complete-Pi count: {full_total}")
        print(f"  C6 systems checked exactly: {core_pattern_count:,}")
        print(f"  planar C6 cores retained: {len(cores)}")
        print(f"  nonplanar C6 cores safely eliminated: {excluded_patterns:,}")
        print(f"  extension candidates per retained core: {core_subtree}")
        print(f"  worker processes: {processes}")
        print(f"  activation order: {order}")
        print(f"  exact completed-restriction superdomains: {bool(use_superdomain)}")
        print(f"  exact q6/q11 whole-stage DEAD certificates: {bool(use_whole_stage)}")
        print(f"  v0.12 early q7/q10 endpoint certificates: {bool(use_endpoint_hoisting)}")
        print(f"  v0.12 direct complete-Pi encoder: {bool(use_direct_pi_encoder)}")
        print(f"  v0.13 exact C8-language support: {bool(use_c8_language)}")
        print(f"  v0.14 precomputed exact C8 row masks: {bool(use_v014_precomputed_c8_rows)}")
        print(f"  v0.14 incremental C8 support propagation: {bool(use_v014_incremental_c8)}")
        print(f"  v0.14 C8-sensitive early slot bundling: {bool(use_v014_c8_sensitive_slots)}")
        print(f"  v0.15 exact H2=C8+e2 support: {bool(use_v015_h2_language)}")
        print(f"  v0.15 exact H5=C8+e5 reflected support: {bool(use_v015_h5_language)}")
        print(f"  v0.15 support-driven sensitive-slot generation: {bool(use_v015_support_driven_slots)}")
        print(f"  v0.13 exact C6-core automorphism quotient: {bool(use_automorphism_quotient)}")
        print(f"  literal Kuratowski learning: {bool(use_kuratowski_learning)}")
        print(f"  exact-isomorphism planarity cache: {bool(use_exact_iso_cache)}")

    full_target_run = core_indices is None
    effective_quotient = bool(use_automorphism_quotient and full_target_run)
    if effective_quotient:
        selected_indices, orbit_map = _db682_core_orbits(cores)
    elif core_indices is None:
        selected_indices = list(range(len(cores)))
        orbit_map = {i: (i,) for i in selected_indices}
    else:
        selected_indices = sorted(set(int(i) for i in core_indices))
        if not selected_indices or any(i < 0 or i >= len(cores) for i in selected_indices):
            raise ValueError("core_indices must contain values from 0 through 7.")
        # Explicit core requests are diagnostic partial searches, so no unasked
        # symmetry copies are credited to their coverage.
        orbit_map = {i: (i,) for i in selected_indices}

    # Never launch more worker processes than exact representative jobs.
    processes = max(1, min(int(processes), len(selected_indices)))

    if verbose and effective_quotient:
        print(f"  exact reflection core orbits: {orbit_map}")
        print(f"  searched C6-core representatives: {selected_indices}")

    orbit_sizes = {i: len(orbit_map[i]) for i in selected_indices}

    payloads = []
    for i in selected_indices:
        core = cores[i]
        payloads.append({
            "core_index": i,
            "represented_cores": list(orbit_map[i]),
            "core_pi": core,
            "core_edges": core_edges,
            "order": order,
            "max_calls": max_calls_per_core,
            "time_limit": time_limit_per_core,
            "planarity": planarity,
            "planarity_workers": planarity_workers_per_process,
            "use_superdomain": bool(use_superdomain),
            "use_whole_stage": bool(use_whole_stage),
            "use_endpoint_hoisting": bool(use_endpoint_hoisting),
            "use_direct_pi_encoder": bool(use_direct_pi_encoder),
            "use_c8_language": bool(use_c8_language),
            "use_v014_precomputed_c8_rows": bool(use_v014_precomputed_c8_rows),
            "use_v014_incremental_c8": bool(use_v014_incremental_c8),
            "use_v014_c8_sensitive_slots": bool(use_v014_c8_sensitive_slots),
            "use_v015_h2_language": bool(use_v015_h2_language),
            "use_v015_h5_language": bool(use_v015_h5_language),
            "use_v015_support_driven_slots": bool(use_v015_support_driven_slots),
            "use_kuratowski_learning": bool(use_kuratowski_learning),
            "use_exact_iso_cache": bool(use_exact_iso_cache),
            "debug": False,
            "progress_interval": None,
            "progress_proxy": None,
        })

    core_results: List[dict] = []
    progress_interval = None if progress in (None, 0) else max(0.1, float(progress))
    if progress_mode not in {"auto", "single", "line", "dashboard"}:
        raise ValueError("progress_mode must be auto, single, line, or dashboard.")

    # For the live dashboard, workers publish lightweight snapshots through a
    # Manager dictionary while the parent alone owns terminal output.  This is
    # display-only plumbing: it does not change search order, pruning, or counts.
    use_live_dashboard = bool(verbose and progress_interval is not None)
    methods = mp.get_all_start_methods()
    ctx = mp.get_context("fork" if "fork" in methods else "spawn")
    manager = None
    progress_proxy = None
    if use_live_dashboard:
        manager = ctx.Manager()
        progress_proxy = manager.dict()
        for i in selected_indices:
            progress_proxy[i] = {
                "core_index": i, "status": "WAITING", "resolved_candidates": 0,
                "total_candidates": core_subtree,
            }
        # Workers publish more frequently than the screen refresh so the parent
        # always has a fresh snapshot when it redraws.
        worker_heartbeat = min(1.0, progress_interval)
        for payload in payloads:
            payload["progress_proxy"] = progress_proxy
            payload["progress_interval"] = worker_heartbeat

    if use_live_dashboard:
        last_draw = 0.0
        last_resolved = 0
        last_measure = started
        pending = {}
        terminate_for_witness = False
        try:
            with ctx.Pool(processes=processes) as pool:
                for payload in payloads:
                    pending[int(payload["core_index"])] = pool.apply_async(_db682_core_worker, (payload,))

                while pending:
                    now = time.perf_counter()
                    for idx_core, async_result in list(pending.items()):
                        if async_result.ready():
                            r = async_result.get()
                            core_results.append(r)
                            pending.pop(idx_core)
                            if progress_proxy is not None:
                                st = r.get("stats") or {}
                                snap = dict(progress_proxy.get(idx_core, {}))
                                snap.update({
                                    "core_index": idx_core,
                                    "status": r["status"],
                                    "resolved_candidates": st.get("resolved_candidates", snap.get("resolved_candidates", 0)),
                                    "total_candidates": st.get("total_candidates", core_subtree),
                                    "recursive_calls": st.get("recursive_calls", snap.get("recursive_calls", 0)),
                                    "partial_planarity_tests": st.get("partial_planarity_tests", snap.get("partial_planarity_tests", 0)),
                                    "full_planarity_tests": st.get("full_planarity_tests", snap.get("full_planarity_tests", 0)),
                                    "partial_nonplanar_prunes": st.get("partial_nonplanar_prunes", snap.get("partial_nonplanar_prunes", 0)),
                                    "locked_prefix_prunes": st.get("locked_prefix_prunes", snap.get("locked_prefix_prunes", 0)),
                                    "superdomain_tests": st.get("superdomain_tests", snap.get("superdomain_tests", 0)),
                                    "superdomain_prunes": st.get("superdomain_prunes", snap.get("superdomain_prunes", 0)),
                                    "superdomain_cache_hits": st.get("superdomain_cache_hits", snap.get("superdomain_cache_hits", 0)),
                                    "c8_language_queries": st.get("c8_language_queries", snap.get("c8_language_queries", 0)),
                                    "c8_language_prunes": st.get("c8_language_prunes", snap.get("c8_language_prunes", 0)),
                                    "c8_language_candidates_pruned": st.get("c8_language_candidates_pruned", snap.get("c8_language_candidates_pruned", 0)),
                                    "v014_c8_incremental_refinements": st.get("v014_c8_incremental_refinements", snap.get("v014_c8_incremental_refinements", 0)),
                                    "v014_c8_sensitive_slot_bundles": st.get("v014_c8_sensitive_slot_bundles", snap.get("v014_c8_sensitive_slot_bundles", 0)),
                                    "v014_c8_sensitive_slot_dead": st.get("v014_c8_sensitive_slot_dead", snap.get("v014_c8_sensitive_slot_dead", 0)),
                                    "v014_c8_sensitive_candidates_pruned": st.get("v014_c8_sensitive_candidates_pruned", snap.get("v014_c8_sensitive_candidates_pruned", 0)),
                                    "v015_h2_queries": st.get("v015_h2_queries", snap.get("v015_h2_queries", 0)),
                                    "v015_h2_refinements": st.get("v015_h2_refinements", snap.get("v015_h2_refinements", 0)),
                                    "v015_h2_prunes": st.get("v015_h2_prunes", snap.get("v015_h2_prunes", 0)),
                                    "v015_h2_candidates_pruned": st.get("v015_h2_candidates_pruned", snap.get("v015_h2_candidates_pruned", 0)),
                                    "v015_h5_queries": st.get("v015_h5_queries", snap.get("v015_h5_queries", 0)),
                                    "v015_h5_refinements": st.get("v015_h5_refinements", snap.get("v015_h5_refinements", 0)),
                                    "v015_h5_prunes": st.get("v015_h5_prunes", snap.get("v015_h5_prunes", 0)),
                                    "v015_h5_candidates_pruned": st.get("v015_h5_candidates_pruned", snap.get("v015_h5_candidates_pruned", 0)),
                                    "v015_support_prefix_states": st.get("v015_support_prefix_states", snap.get("v015_support_prefix_states", 0)),
                                    "v015_support_prefix_dead": st.get("v015_support_prefix_dead", snap.get("v015_support_prefix_dead", 0)),
                                    "v015_support_prefix_bundles_skipped": st.get("v015_support_prefix_bundles_skipped", snap.get("v015_support_prefix_bundles_skipped", 0)),
                                    "c6_prunes": st.get("c6_prunes", snap.get("c6_prunes", 0)),
                                    "backtracks": st.get("backtracks", snap.get("backtracks", 0)),
                                    "screening_states": st.get("screening_states", snap.get("screening_states", 0)),
                                    "max_modeled_crossings": st.get("max_modeled_crossings", snap.get("max_modeled_crossings", 0)),
                                    "planarity_backend": st.get("planarity_backend", snap.get("planarity_backend", "")),
                                })
                                progress_proxy[idx_core] = snap
                            if r["status"] == "THRACKLEABLE":
                                terminate_for_witness = True
                                break
                    if terminate_for_witness:
                        pool.terminate()
                        break

                    now = time.perf_counter()
                    if now - last_draw >= progress_interval:
                        snapshots = dict(progress_proxy) if progress_proxy is not None else {}
                        text, last_resolved, last_measure = _db682_parallel_dashboard(
                            snapshots, selected_indices, started=started,
                            excluded_candidates=excluded_candidates, full_total=full_total,
                            core_subtree=core_subtree, last_retained_resolved=last_resolved,
                            last_time=last_measure, orbit_sizes=orbit_sizes,
                        )
                        _print_db682_dashboard(text, progress_mode)
                        last_draw = now
                    time.sleep(min(0.10, progress_interval / 10.0))

                if not terminate_for_witness:
                    pool.close()
                    pool.join()

            # One final dashboard with final worker states.
            snapshots = dict(progress_proxy) if progress_proxy is not None else {}
            text, last_resolved, last_measure = _db682_parallel_dashboard(
                snapshots, selected_indices, started=started,
                excluded_candidates=excluded_candidates, full_total=full_total,
                core_subtree=core_subtree, last_retained_resolved=last_resolved,
                last_time=last_measure, orbit_sizes=orbit_sizes,
            )
            _print_db682_dashboard(text, progress_mode)
            if progress_mode in {"auto", "single", "dashboard"} and sys.stdout.isatty():
                print()
        finally:
            if manager is not None:
                manager.shutdown()
    elif processes == 1:
        for payload in payloads:
            r = _db682_core_worker(payload)
            core_results.append(r)
            if verbose:
                st = r.get("stats") or {}
                print(
                    f"  core {r['core_index']}: {r['status']} | "
                    f"coverage={coverage_percent_string(st.get('resolved_candidates',0), st.get('total_candidates',1), 12)}"
                )
            if r["status"] == "THRACKLEABLE":
                break
    else:
        with ctx.Pool(processes=processes) as pool:
            for r in pool.imap_unordered(_db682_core_worker, payloads):
                core_results.append(r)
                if verbose:
                    st = r.get("stats") or {}
                    print(
                        f"  core {r['core_index']}: {r['status']} | "
                        f"coverage={coverage_percent_string(st.get('resolved_candidates',0), st.get('total_candidates',1), 12)}"
                    )
                if r["status"] == "THRACKLEABLE":
                    pool.terminate()
                    break

    core_results.sort(key=lambda r: r["core_index"])
    witness = next((r.get("witness_pi") for r in core_results if r["status"] == "THRACKLEABLE"), None)
    errors = [r for r in core_results if r["status"] == "ERROR"]
    represented_resolved = 0
    for r in core_results:
        st = r.get("stats") or {}
        multiplicity = len(r.get("represented_cores") or [r.get("core_index")])
        represented_resolved += multiplicity * int(st.get("resolved_candidates", 0))
    resolved = excluded_candidates + represented_resolved
    elapsed = time.perf_counter() - started

    if witness is not None:
        status = "THRACKLEABLE"
        reason = "A retained planar C6 core has a complete planar extension."
    elif errors:
        status = "INCONCLUSIVE"
        reason = f"{len(errors)} core worker(s) failed; no mathematical conclusion."
    elif (
        full_target_run
        and len(core_results) == len(selected_indices)
        and all(r["status"] == "NONTHRACKLEABLE" for r in core_results)
    ):
        if resolved != full_total:
            raise AssertionError(
                "All required C6 core representatives finished negative but global exact "
                f"coverage is {resolved}/{full_total}."
            )
        status = "NONTHRACKLEABLE"
        if effective_quotient:
            reason = (
                "All 46,648 nonplanar C6 cores were safely excluded and one exact "
                "representative of each of the four reflection orbits of planar C6 "
                "cores was exhaustively eliminated; symmetry covers all eight cores."
            )
        else:
            reason = (
                "All 46,648 nonplanar C6 cores were safely excluded and all eight "
                "planar C6-core extension spaces were exhaustively eliminated."
            )
    else:
        status = "INCONCLUSIVE"
        reason = "At least one required retained C6-core extension search is incomplete."

    result = DB682CoreResult(
        status=status,
        witness_pi=witness,
        total_candidates=full_total,
        resolved_candidates=resolved,
        exact_core_count=len(cores),
        excluded_core_patterns=excluded_patterns,
        core_results=core_results,
        elapsed_seconds=elapsed,
        reason=reason,
    )
    if report:
        Path(report).write_text(json.dumps(asdict(result), indent=2, default=str), encoding="utf-8")
    if verbose:
        print(f"GLOBAL STATUS: {result.status}")
        print(f"GLOBAL COVERAGE: {coverage_percent_string(result.resolved_candidates, result.total_candidates, 18)}")
        print(f"Elapsed: {result.elapsed_seconds:.3f}s")
        print(result.reason)
    return result



def _v091_safety_regressions() -> None:
    """Permanent regressions for the v0.6.1.1/v0.9.0 monotonicity failures.

    The first check reproduces the known non-chronological C6 state that is
    nonplanar despite having a planar completion.  The second check verifies
    that the target-specific factorized checkpoint refuses to test any
    incomplete arbitrary-gap stage.  These tests are deliberately assertions,
    not pruning rules.
    """
    G = Cycle(6)
    search = BacktrackingSearch(
        G,
        use_c6_restriction=False,
        use_screening=False,
        use_lookahead=False,
        incremental_partial=False,
        use_cache=False,
        progress_interval_seconds=None,
        planarity_backend="networkx",
    )
    full = {
        0: [2, 4, 3],
        1: [3, 5, 4],
        2: [4, 0, 5],
        3: [5, 1, 0],
        4: [0, 2, 1],
        5: [1, 3, 2],
    }

    def partial_for_current(modeled):
        current = 0
        modeled = set(modeled)
        pi = {e.id: [] for e in G.edges}
        for e in range(6):
            for f in full[e]:
                if e == current:
                    if f in modeled:
                        pi[e].append(f)
                elif f == current:
                    if e in modeled:
                        pi[e].append(f)
                else:
                    pi[e].append(f)
        return pi

    Hfull = build_augmented_graph(
        G, full, oriented=search.oriented, validate=True,
        crossing_cache=search.crossing_cache,
    )
    Hchron = build_locked_prefix_minor(
        G, partial_for_current([2]), list(range(6)), search.oriented,
        current_eid=0, current_complete=False, validate=True,
        crossing_cache=search.crossing_cache,
    )
    Hnonprefix = build_locked_prefix_minor(
        G, partial_for_current([4]), list(range(6)), search.oriented,
        current_eid=0, current_complete=False, validate=True,
        crossing_cache=search.crossing_cache,
    )
    if not nx.is_planar(Hfull) or not nx.is_planar(Hchron) or nx.is_planar(Hnonprefix):
        raise AssertionError("Known non-chronological prefix counterexample did not reproduce.")

    # Hard guard: factorized target planarity may be called only stage-complete.
    T = DB(6, 8, -2)
    order = db682_candidate_activation_orders(T, limit=1)[0]
    fs = DB682FactorizedSearch(
        T,
        use_c6_restriction=False,
        use_screening=False,
        use_lookahead=False,
        incremental_partial=False,
        use_cache=False,
        progress_interval_seconds=None,
        planarity_backend="networkx",
        activation_order="custom",
        custom_activation_order=order,
        use_locked_prefix_pruning=True,
        core_edges=order[:6],
    )
    try:
        fs._factorized_locked_planar(6)
    except AssertionError as exc:
        if "safety guard" not in str(exc):
            raise
    else:
        raise AssertionError("Factorized safety guard allowed an incomplete stage planarity test.")

    # v0.10 hard guard: an exact-superdomain test must itself be a COMPLETE
    # selected-edge restriction. Calling it before the fixed C6/current
    # projection has been modeled must fail loudly rather than prune.
    try:
        fs._completed_selected_restriction_planar(7, 0, (7,))
    except AssertionError as exc:
        if "superdomain safety guard" not in str(exc):
            raise
    else:
        raise AssertionError("v0.10 superdomain guard accepted an incomplete restriction.")

    # Tail reordering must remain a permutation of the same six edges and the
    # exact complete-Pi count is constructor-level invariant.
    if tuple(order[6:]) != (7, 10, 9, 8, 6, 11):
        raise AssertionError(f"Unexpected v0.12 tuned tail order: {order[6:]}")
    if fs.total_candidates != T.candidate_count():
        raise AssertionError("v0.10 tuned order changed the exact complete-Pi count.")


def _v011_safety_regressions() -> None:
    """Targeted regressions for every new v0.11 negative-inference path."""
    # 1. New generic compiled batch must be exactly the ordinary predicate.
    try:
        boost = _BoostPlanarityBackend()
    except Exception:
        boost = None
    if boost is not None:
        graphs = [nx.cycle_graph(5), nx.complete_graph(5), nx.complete_bipartite_graph(3, 3), nx.path_graph(7)]
        expected = [nx.is_planar(H) for H in graphs]
        if boost.batch_graph_planarity(graphs, workers=1) != expected:
            raise AssertionError("v0.11 generic graph batch disagrees with NetworkX (serial).")
        if boost.batch_graph_planarity(graphs, workers=min(4, max(1, os.cpu_count() or 1))) != expected:
            raise AssertionError("v0.11 generic graph batch disagrees with NetworkX (parallel).")

    # 2. Hash-only reuse is permanently forbidden: these atlas graphs collide
    # under WL but have different planarity. Exact isomorphism must reject reuse.
    atlas = nx.graph_atlas_g()
    A, B = atlas[174], atlas[175]
    if nx.weisfeiler_lehman_graph_hash(A) != nx.weisfeiler_lehman_graph_hash(B):
        raise AssertionError("Expected permanent WL-collision regression did not reproduce.")
    if nx.is_planar(A) == nx.is_planar(B) or nx.is_isomorphic(A, B):
        raise AssertionError("WL-collision regression no longer separates exact graph semantics.")

    # 3. Literal Kuratowski containment is hereditary.
    if boost is not None:
        K33 = nx.complete_bipartite_graph(3, 3)
        cert = boost.kuratowski_edges(K33)
        if not cert:
            raise AssertionError("v0.11 Kuratowski regression failed to extract K3,3 certificate.")
        cert_graph = nx.Graph(); cert_graph.add_edges_from(tuple(e) for e in cert)
        if nx.is_planar(cert_graph):
            raise AssertionError("v0.11 Kuratowski regression extracted a planar certificate.")
        S = cert_graph.copy(); S.add_edge("extra-a", "extra-b")
        if nx.is_planar(S):
            raise AssertionError("Literal supergraph of Kuratowski certificate became planar.")

    # 4. Whole-stage q6/q11 quotient is compared against literal enumeration of
    # every exact core-host slot on deterministic synthetic exact parents.
    T = DB(6, 8, -2)
    order = db682_candidate_activation_orders(T, limit=1)[0]
    planarity_name = "boost" if boost is not None else "networkx"
    # Use one explicitly mapped planar C6 system instead of re-enumerating all
    # 46,656 cores inside the routine self-test. The production core enumerator
    # is tested separately by the release audit.
    known_c6 = {
        0: [2, 4, 3], 1: [3, 5, 4], 2: [4, 0, 5],
        3: [5, 1, 0], 4: [0, 2, 1], 5: [1, 3, 2],
    }
    cyc_edges = tuple(T.simple_six_cycles()[0].edges)
    edge_map = {i: cyc_edges[i] for i in range(6)}
    core_edges = list(cyc_edges)
    core_pi = {edge_map[i]: [edge_map[j] for j in known_c6[i]] for i in range(6)}
    core_check = {e.id: [] for e in T.edges}
    for e in core_edges:
        core_check[e] = list(core_pi[e])
    orient = BacktrackingSearch(
        T, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=False,
    ).oriented
    if not nx.is_planar(build_active_augmented_minor(T, core_check, core_edges, orient, validate=True)):
        raise AssertionError("Mapped v0.11 self-test C6 core is not planar.")
    fs = DB682FactorizedSearch(
        T,
        use_c6_restriction=False,
        use_screening=False,
        use_lookahead=False,
        incremental_partial=False,
        use_cache=False,
        progress_interval_seconds=None,
        planarity_backend=planarity_name,
        planarity_workers=1,
        activation_order="custom",
        custom_activation_order=order,
        use_locked_prefix_pruning=True,
        core_edges=core_edges,
        debug=True,
    )
    d6, _ = _generate_db682_local_domain(fs, core_pi, core_edges, 6)
    d11, _ = _generate_db682_local_domain(fs, core_pi, core_edges, 11)
    core_set = set(core_edges)
    rng = random.Random(11020260901)

    def make_parent(last_index: int, seed_offset: int) -> Pi:
        rr = random.Random(11020260901 + seed_offset)
        pi: Pi = {e.id: [] for e in T.edges}
        for e in core_edges:
            pi[e] = list(core_pi[e])
        active = list(core_edges)
        for idx in range(6, last_index + 1):
            current = order[idx]
            older = [e for e in T._nonincident[current] if e in set(active)]
            rr.shuffle(older)
            pi[current] = list(older)
            for old in older:
                pos = rr.randrange(len(pi[old]) + 1)
                pi[old].insert(pos, current)
            active.append(current)
        validate_partial_pi(T, pi, active)
        return pi

    def literal_zero_extra_dead(edge_index: int, domain) -> bool:
        current = order[edge_index]
        older = tuple(fs.older_required[edge_index])
        partners = tuple(e for e in core_edges if e in older)
        extras = tuple(e for e in older if e not in core_set)
        _, prepared = fs._stage_allowed_weight(edge_index, domain, partners, extras)
        older_q = tuple(order[6:edge_index])
        selected_older = tuple(q for q in older_q if q not in set(extras))
        selected = tuple(core_edges) + selected_older + (current,)
        selected_set = set(selected)
        any_planar = False
        for sig, slot_lists, _ in prepared:
            fs.pi[current] = list(sig.core_order)
            for combo in product(*slot_lists):
                for host, pos in zip(partners, combo):
                    fs.pi[host].insert(pos, current)
                projected: Pi = {e.id: [] for e in T.edges}
                for e in selected:
                    projected[e] = [x for x in fs.pi[e] if x in selected_set]
                for e in selected:
                    expected = {f for f in T._nonincident[e] if f in selected_set}
                    if set(projected[e]) != expected or len(projected[e]) != len(expected):
                        raise AssertionError("Literal v0.11 regression constructed incomplete restriction.")
                H = build_active_augmented_minor(
                    T, projected, selected, fs.oriented,
                    validate=True, crossing_cache=fs.crossing_cache,
                )
                if nx.is_planar(H):
                    any_planar = True
                for host, pos in reversed(tuple(zip(partners, combo))):
                    if fs.pi[host].pop(pos) != current:
                        raise AssertionError("Literal q-stage regression failed restoration.")
            fs.pi[current] = []
        return not any_planar

    for j in range(12):
        fs.pi = {e: list(L) for e, L in make_parent(9, j).items()}
        fs.started = time.perf_counter()
        fs.db682_whole_stage_cache.clear()
        expected_dead = literal_zero_extra_dead(10, d6)
        older = tuple(fs.older_required[10])
        partners = tuple(e for e in core_edges if e in older)
        extras = tuple(e for e in older if e not in core_set)
        got_dead = fs._whole_stage_dead_certificate(10, d6, partners, extras)
        if got_dead != expected_dead:
            raise AssertionError(
                f"v0.11 q6 whole-stage quotient mismatch on synthetic parent {j}: "
                f"bulk={got_dead}, literal={expected_dead}."
            )

    for j in range(6):
        fs.pi = {e: list(L) for e, L in make_parent(10, 100 + j).items()}
        fs.started = time.perf_counter()
        fs.db682_whole_stage_cache.clear()
        expected_dead = literal_zero_extra_dead(11, d11)
        older = tuple(fs.older_required[11])
        partners = tuple(e for e in core_edges if e in older)
        extras = tuple(e for e in older if e not in core_set)
        got_dead = fs._whole_stage_dead_certificate(11, d11, partners, extras)
        if got_dead != expected_dead:
            raise AssertionError(
                f"v0.11 q11 whole-stage quotient mismatch on synthetic parent {j}: "
                f"bulk={got_dead}, literal={expected_dead}."
            )

    # 5. Hidden pending q-edge placements must not change the exact selected
    # parent key used by the q6 theorem. Build two parents with identical C6+q7
    # restriction and different q9/q10/q8 placements.
    p1 = make_parent(6, 500)
    selected_q7 = tuple(core_edges) + (order[6],)
    selected_q7_set = set(selected_q7)
    fixed = {e: [x for x in p1[e] if x in selected_q7_set] for e in selected_q7}

    def extend_fixed_q7(seed: int) -> Pi:
        rr = random.Random(seed)
        pi: Pi = {e.id: [] for e in T.edges}
        for e in selected_q7:
            pi[e] = list(fixed[e])
        active = list(selected_q7)
        for idx in range(7, 10):
            current = order[idx]
            older = [e for e in T._nonincident[current] if e in set(active)]
            rr.shuffle(older)
            pi[current] = list(older)
            for old in older:
                pi[old].insert(rr.randrange(len(pi[old]) + 1), current)
            active.append(current)
        validate_partial_pi(T, pi, active)
        return pi

    fs.pi = extend_fixed_q7(901)
    key1, _, _ = fs._whole_stage_parent_key(10, (8, 9, 10))
    fs.pi = extend_fixed_q7(902)
    key2, _, _ = fs._whole_stage_parent_key(10, (8, 9, 10))
    if key1 != key2:
        raise AssertionError("v0.11 q6 selected-parent key incorrectly depends on pending hidden edges.")

    # 6. Interruption must not create a DEAD cache fact.
    fs.db682_whole_stage_cache.clear()
    fs.pi = extend_fixed_q7(903)
    parent_key, _, _ = fs._whole_stage_parent_key(10, (8, 9, 10))
    old_check = fs._check_limits
    fs._check_limits = lambda: (_ for _ in ()).throw(SearchLimitReached("intentional v0.11 test"))
    try:
        try:
            fs._whole_stage_dead_certificate(10, d6, (1, 5, 4, 3), (8, 9, 10))
        except SearchLimitReached:
            pass
        else:
            raise AssertionError("v0.11 intentional interruption failed to interrupt whole-stage theorem.")
    finally:
        fs._check_limits = old_check
    if parent_key in fs.db682_whole_stage_cache:
        raise AssertionError("v0.11 interruption incorrectly cached a whole-stage result.")


def _v012_safety_regressions() -> None:
    """Targeted blast regressions for every new v0.12 inference/encoder path."""
    T = DB(6, 8, -2)
    order = db682_candidate_activation_orders(T, limit=1)[0]
    if tuple(order[6:]) != (7, 10, 9, 8, 6, 11):
        raise AssertionError(f"v0.12 traversal regression: {order[6:]}")

    try:
        boost = _BoostPlanarityBackend()
    except Exception:
        boost = None
    if boost is None:
        raise AssertionError("v0.12 target blast test requires the compiled Boost backend.")

    # 1. Direct complete-Pi encoder vs independent Python augmented-graph
    # construction + NetworkX + the older generic Boost graph-batch path.
    ref = BacktrackingSearch(
        T, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="boost", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=False,
    )
    rng = random.Random(12020260901)
    checked = 0
    for _batch in range(2):
        keep = set(rng.sample(order, rng.randrange(2, len(order) + 1)))
        selected = tuple(e for e in order if e in keep)
        selected_set = set(selected)
        pis = []
        graphs = []
        for _ in range(50):
            pi: Pi = {e.id: [] for e in T.edges}
            for e in selected:
                req = [f for f in T._nonincident[e] if f in selected_set]
                rng.shuffle(req)
                pi[e] = req
            modeled_pairs(pi, selected)
            pis.append(pi)
            graphs.append(build_active_augmented_minor(
                T, pi, selected, ref.oriented, validate=True,
                crossing_cache=ref.crossing_cache,
            ))
        direct = boost.batch_complete_pi_planarity(
            T, selected, pis, oriented=ref.oriented,
            workers=min(4, max(1, os.cpu_count() or 1)),
        )
        nx_answers = [nx.is_planar(H) for H in graphs]
        if direct != nx_answers:
            raise AssertionError("v0.12 direct complete-Pi encoder differential mismatch.")
        checked += len(pis)
    if checked != 100:
        raise AssertionError("v0.12 direct encoder blast case count drifted.")

    # Release-audit note: malformed-packing failure is tested separately in a
    # fresh process so it cannot perturb the long target regression's allocator state.
    import gc as _gc
    del graphs, pis, boost, ref
    _gc.collect()

    # 2. One explicit planar C6 core, identical to the independent v0.11
    # regression core.  Generate exact local domains, then exercise hoisting.
    known_c6 = {
        0: [2, 4, 3], 1: [3, 5, 4], 2: [4, 0, 5],
        3: [5, 1, 0], 4: [0, 2, 1], 5: [1, 3, 2],
    }
    core_edges = tuple(order[:6])
    edge_map = {i: core_edges[i] for i in range(6)}
    core_pi = {edge_map[i]: [edge_map[j] for j in known_c6[i]] for i in range(6)}
    fs = DB682FactorizedSearch(
        T, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="boost", planarity_workers=min(4, max(1, os.cpu_count() or 1)),
        activation_order="custom", custom_activation_order=order,
        use_locked_prefix_pruning=True, core_edges=core_edges, debug=False,
    )
    fs.use_v011_kuratowski_learning = False
    fs.use_v011_exact_iso_cache = False
    fs.use_v012_direct_pi_encoder = True
    d6, _ = _generate_db682_local_domain(fs, core_pi, core_edges, 6)
    d7, _ = _generate_db682_local_domain(fs, core_pi, core_edges, 7)
    d11, _ = _generate_db682_local_domain(fs, core_pi, core_edges, 11)
    fs.db682_local_domains = {6: d6, 7: d7, 8: d7, 9: d7, 10: d7, 11: d11}
    _seed_search_with_core(fs, core_pi, core_edges)
    fs.started = time.perf_counter()
    core_set = set(core_edges)

    def install_signature(q: int, sig: DB682LocalSignature) -> Tuple[Tuple[int, ...], Tuple[Tuple[int, ...], ...]]:
        fs.pi[q] = list(sig.core_order)
        partners = tuple(e for e in core_edges if e in T._nonincident[q])
        slots = tuple(fs._core_gap_positions(h, q, g) for h, g in zip(partners, sig.core_gaps))
        return partners, slots

    def uninstall_signature(q: int) -> None:
        fs.pi[q] = []

    # On this audited core the exact endpoint theorem has a permanent regression
    # target: 966 locally planar q7 signatures -> 133 endpoint-viable signatures.
    q7_index = order.index(7)
    q7_dead = 0
    q7_results = []
    for sig in d7:
        partners, slots = install_signature(7, sig)
        dead = fs._endpoint_signature_dead(q7_index, sig, partners, slots)
        q7_results.append(dead)
        q7_dead += int(dead)
        uninstall_signature(7)
    if (len(d7), q7_dead, len(d7)-q7_dead) != (966, 833, 133):
        raise AssertionError(
            f"v0.12 q7 endpoint regression changed: domain={len(d7)}, dead={q7_dead}."
        )

    # 3. Independent literal NetworkX check on a mix of endpoint-DEAD and
    # endpoint-surviving q7 signatures.  Enumerate every complete C6+q7+q6
    # restriction represented by the q6 local domain.
    q6_index = order.index(6)
    q6_older = tuple(fs.older_required[q6_index])
    q6_partners = tuple(e for e in core_edges if e in q6_older)
    q6_extras = tuple(e for e in q6_older if e not in core_set)
    chosen = list(range(12))
    survivors = [i for i, dead in enumerate(q7_results) if not dead][:6]
    chosen.extend(survivors)

    def literal_q6_dead_for_installed_q7() -> bool:
        # Pending q10/q9/q8 are deleted; selected restriction is exactly C6+q7+q6.
        selected_base = tuple(core_edges) + (7,)
        base_set = set(selected_base)
        projected_base: Pi = {e.id: [] for e in T.edges}
        for e in selected_base:
            projected_base[e] = [x for x in fs.pi[e] if x in base_set]
        selected = selected_base + (6,)
        selected_set = set(selected)
        any_planar = False
        for child_sig in d6:
            projected_slots = []
            for host, gap in zip(q6_partners, child_sig.core_gaps):
                seq = projected_base[host]
                positions = tuple(
                    pos for pos in range(len(seq)+1)
                    if sum(1 for x in seq[:pos] if x in core_set) == gap
                )
                projected_slots.append(positions)
            for combo in product(*projected_slots):
                pi: Pi = {e.id: [] for e in T.edges}
                for e in selected_base:
                    pi[e] = list(projected_base[e])
                pi[6] = list(child_sig.core_order)
                for host, pos in zip(q6_partners, combo):
                    pi[host].insert(pos, 6)
                for e in selected:
                    expected = {f for f in T._nonincident[e] if f in selected_set}
                    if set(pi[e]) != expected or len(pi[e]) != len(expected):
                        raise AssertionError("v0.12 literal endpoint regression built incomplete Pi.")
                H = build_active_augmented_minor(
                    T, pi, selected, fs.oriented, validate=True,
                    crossing_cache=fs.crossing_cache,
                )
                if nx.is_planar(H):
                    any_planar = True
        return not any_planar

    for idx in chosen:
        sig = d7[idx]
        partners, slots = install_signature(7, sig)
        # Make the q7 crossing lists symmetric exactly as the search does.
        inserted=[]
        try:
            for h, positions in zip(partners, slots):
                pos=positions[0]; fs.pi[h].insert(pos,7); inserted.append((h,pos))
            literal = literal_q6_dead_for_installed_q7()
        finally:
            for h,pos in reversed(inserted):
                if fs.pi[h].pop(pos) != 7:
                    raise AssertionError("v0.12 literal q7 restore failed.")
            uninstall_signature(7)
        if literal != q7_results[idx]:
            raise AssertionError(
                f"v0.12 endpoint hoist differs from literal completed restrictions at q7 signature {idx}."
            )

    # 4. q10 endpoint result must be invariant under hidden q7 placement and the
    # exact signature cache must reuse it.  Install two different q7 signatures.
    q10_index = order.index(10)
    q10_sig = d7[0]
    endpoint_vals=[]
    hits_before=fs.stats.endpoint_cache_hits
    for q7_sig in (d7[0], d7[1]):
        p7, sl7 = install_signature(7, q7_sig)
        inserted7=[]
        try:
            for h, positions in zip(p7, sl7):
                pos=positions[-1]; fs.pi[h].insert(pos,7); inserted7.append((h,pos))
            p10, sl10 = install_signature(10, q10_sig)
            endpoint_vals.append(fs._endpoint_signature_dead(q10_index, q10_sig, p10, sl10))
            uninstall_signature(10)
        finally:
            for h,pos in reversed(inserted7):
                if fs.pi[h].pop(pos) != 7:
                    raise AssertionError("v0.12 q10 hidden-parent restore failed.")
            uninstall_signature(7)
    if endpoint_vals[0] != endpoint_vals[1]:
        raise AssertionError("v0.12 q10 endpoint result depends on deleted q7 information.")
    if fs.stats.endpoint_cache_hits <= hits_before:
        raise AssertionError("v0.12 q10 endpoint exact signature cache did not reuse the result.")

    # 5. Interrupted endpoint work is fail-open: neither endpoint cache nor a
    # whole-stage DEAD fact may be written after the intentional interruption.
    fs.db682_endpoint_cache.clear()
    fs.db682_whole_stage_cache.clear()
    sig = d7[0]
    partners, slots = install_signature(7, sig)
    old_check = fs._check_limits
    fs._check_limits = lambda: (_ for _ in ()).throw(SearchLimitReached("intentional v0.12 endpoint test"))
    try:
        try:
            fs._endpoint_signature_dead(q7_index, sig, partners, slots)
        except SearchLimitReached:
            pass
        else:
            raise AssertionError("v0.12 intentional endpoint interruption failed to interrupt.")
    finally:
        fs._check_limits = old_check
        uninstall_signature(7)
    if fs.db682_endpoint_cache or fs.db682_whole_stage_cache:
        raise AssertionError("v0.12 interruption incorrectly cached a DEAD/endpoint result.")

def self_test():
    """
    v0.8.1 verification ladder.

    1. v0.1-style exhaustive baseline agrees with known C4/C5/C6 statuses.
    2. v0.8.1 with screening/lookahead OFF and legacy rebuilds reproduces the
       v0.3 search path/result on those small cycles.
    3. The incremental conservative partial graph reproduces the legacy graph
       exactly in debug mode at every tested UPDATE/REVERSE_UPDATE.
    4. Forward screening only agrees with the baseline.
    5. Screening + one-level lookahead agrees with the baseline.
    6. Optimized C6 mode agrees with the baseline and keeps the published C6
       witness compatible.
    7. Every completed negative run finishes at exact 100% coverage.
    8. Small dumbbell negatives exercise stage transitions and exact accounting.
    9. The streamlined DB/Cycle/Edges/run interface agrees with the engine.
    """
    _v091_safety_regressions()

    expected = {4: False, 5: True, 6: True}
    rows = []

    for n in (4, 5, 6):
        G = cycle_graph(n)
        baseline_pi, baseline_checked, baseline_total = exhaustive_find_witness_v01_style(
            G, max_candidates=100000
        )
        baseline_found = baseline_pi is not None
        if baseline_found != expected[n]:
            raise AssertionError(f"C{n} exhaustive baseline disagrees with known status.")

        modes = {
            "v03_compat": dict(
                use_c6_restriction=False,
                branch_order="natural",
                use_screening=False,
                use_lookahead=False,
                incremental_partial=False,
                debug=True,
            ),
            "incremental": dict(
                use_c6_restriction=False,
                branch_order="natural",
                use_screening=False,
                use_lookahead=False,
                incremental_partial=True,
                debug=True,
            ),
            "screening": dict(
                use_c6_restriction=False,
                branch_order="constrained",
                use_screening=True,
                use_lookahead=False,
                incremental_partial=True,
                debug=True,
            ),
            "lookahead": dict(
                use_c6_restriction=False,
                branch_order="constrained",
                use_screening=True,
                use_lookahead=True,
                incremental_partial=True,
                debug=True,
            ),
            "optimized": dict(
                use_c6_restriction=True,
                branch_order="constrained",
                use_screening=True,
                use_lookahead=True,
                incremental_partial=True,
                debug=False,
            ),
        }

        results = {}
        for label, settings in modes.items():
            result = BacktrackingSearch(
                G,
                max_recursive_calls=2000000,
                time_limit_seconds=120,
                use_cache=False,
                progress_interval_seconds=None,
                **settings,
            ).run()
            results[label] = result
            if result.status == "INCONCLUSIVE":
                raise AssertionError(f"C{n} {label} unexpectedly hit a search limit.")
            found = result.status == "THRACKLEABLE"
            if found != baseline_found:
                raise AssertionError(
                    f"C{n} {label} disagrees with exhaustive baseline."
                )
            if result.status == "NONTHRACKLEABLE":
                if result.stats.resolved_candidates != result.stats.total_candidates:
                    raise AssertionError(
                        f"C{n} {label} negative coverage is not exactly 100%."
                    )

        # With every search optimization disabled except incremental graph
        # maintenance, the exact search path/test counts should match the
        # legacy v0.3-style path. This is a strong implementation check.
        a = results["v03_compat"].stats
        b = results["incremental"].stats
        for field in (
            "recursive_calls",
            "partial_planarity_tests",
            "partial_nonplanar_prunes",
            "full_planarity_tests",
            "resolved_candidates",
        ):
            if getattr(a, field) != getattr(b, field):
                raise AssertionError(
                    f"C{n} incremental/legacy mismatch in {field}: "
                    f"{getattr(a, field)} != {getattr(b, field)}."
                )

        if n == 6:
            if baseline_pi is None or not _witness_satisfies_c6_rule(G, baseline_pi):
                raise AssertionError(
                    "The exhaustive C6 witness does not satisfy the implemented published C6 rule."
                )

        opt = results["optimized"]
        rows.append(
            {
                "graph": f"C{n}",
                "baseline_found": baseline_found,
                "baseline_checked": baseline_checked,
                "baseline_total": baseline_total,
                "v03_compat_status": results["v03_compat"].status,
                "v03_compat_calls": results["v03_compat"].stats.recursive_calls,
                "v03_compat_tests": (
                    results["v03_compat"].stats.partial_planarity_tests
                    + results["v03_compat"].stats.full_planarity_tests
                ),
                "screening_status": results["screening"].status,
                "lookahead_status": results["lookahead"].status,
                "optimized_status": opt.status,
                "optimized_calls": opt.stats.recursive_calls,
                "optimized_tests": (
                    opt.stats.partial_planarity_tests + opt.stats.full_planarity_tests
                ),
                "optimized_c6_prunes": opt.stats.c6_prunes,
                "optimized_time": opt.stats.elapsed_seconds,
            }
        )

    dumbbell_results = []
    for pars in ((3, 3, -1), (3, 3, 0), (4, 4, -1)):
        Gdb = dumbbell(*pars)
        result = BacktrackingSearch(
            Gdb,
            max_recursive_calls=2000000,
            time_limit_seconds=120,
            use_c6_restriction=True,
            branch_order="constrained",
            use_screening=True,
            use_lookahead=True,
            incremental_partial=True,
            debug=True,
            use_cache=False,
            progress_interval_seconds=None,
        ).run()
        if result.status != "NONTHRACKLEABLE":
            raise AssertionError(
                f"DB{pars} expected negative in verification suite, got {result.status}."
            )
        if result.stats.resolved_candidates != result.stats.total_candidates:
            raise AssertionError(f"DB{pars} did not finish at exact 100% coverage.")
        dumbbell_results.append((pars, result))

    # v0.8.1 public-interface checks. These do not introduce a second search
    # implementation; they verify that the friendly constructors/wrapper feed
    # the same engine correctly.
    if single != "single" or line != "line":
        raise AssertionError("Display constants are not exposed as requested.")
    if DB(3, 3, 0).label != "DB(3,3,0)" or Cycle(5).label != "C5":
        raise AssertionError("Friendly graph constructor labels are incorrect.")
    custom_c5 = Edges(
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)],
        label="custom C5",
    )
    public_result = run(
        custom_c5,
        time_limit=120,
        max_calls=1000000,
        progress=0,
        display=single,
        show_start=False,
        show_result=False,
    )
    if public_result.status != "THRACKLEABLE":
        raise AssertionError("Public Edges(...)/run(...) interface failed on custom C5.")

    return rows, dumbbell_results


def print_result(result: SearchResult):
    print(f"STATUS: {result.status}")
    print(f"Reason: {result.reason}")
    print(
        "Coverage:",
        coverage_percent_string(
            result.stats.resolved_candidates,
            result.stats.total_candidates,
            precision=18,
        ),
    )
    print(
        "Resolved complete Pi:",
        f"{result.stats.resolved_candidates:,} / {result.stats.total_candidates:,}",
    )
    print("Stats:")
    for k, v in asdict(result.stats).items():
        if isinstance(v, float):
            print(f"  {k}: {v:.6f}")
        elif isinstance(v, int):
            print(f"  {k}: {v:,}")
        else:
            print(f"  {k}: {v}")

    if result.witness_pi is not None:
        print("Witness Pi:")
        for eid in sorted(result.witness_pi):
            print(f"  pi[{eid}] = {result.witness_pi[eid]}")


def write_json_report(
    path: str,
    graph_label: str,
    G: ThrackleGraph,
    search: BacktrackingSearch,
    result: SearchResult,
):
    payload = {
        "program": "fulek_pach_thrackle_v0100.py",
        "version": "0.10.0",
        "graph_label": graph_label,
        "vertices": list(G.graph.nodes),
        "edges": [{"id": e.id, "u": e.u, "v": e.v} for e in G.edges],
        "euler_edge_order": search.order,
        "oriented_edges": {
            str(eid): [u, v] for eid, (u, v) in search.oriented.items()
        },
        "settings": {
            "use_c6_restriction": search.use_c6_restriction,
            "detected_c6_cycles": [
                {
                    "id": c.id,
                    "vertices": list(c.vertices),
                    "edges": list(c.edges),
                }
                for c in search.six_cycles
            ],
            "branch_order": search.branch_order,
            "use_screening": search.use_screening,
            "use_lookahead": search.use_lookahead,
            "incremental_partial": search.incremental_partial,
            "debug": search.debug,
            "use_cache": search.use_cache,
            "planarity_backend": search.planarity.name,
            "use_batch_screening": search.use_batch_screening,
            "planarity_workers": search.planarity_workers,
            "openmp_enabled": bool(getattr(search.planarity, "openmp_enabled", False)),
            "planarity_parallel_threshold": int(getattr(search.planarity, "parallel_threshold", 4)),
            "use_kuratowski_cache": search.use_kuratowski_cache,
            "kuratowski_cache_limit": search.kuratowski_cache_limit,
            "activation_order": search.activation_order_mode,
            "edge_order": list(search.order),
            "max_recursive_calls": search.max_recursive_calls,
            "time_limit_seconds": search.time_limit_seconds,
        },
        "status": result.status,
        "reason": result.reason,
        "coverage_percent": coverage_percent_string(
            result.stats.resolved_candidates,
            result.stats.total_candidates,
            precision=18,
        ),
        "stats": asdict(result.stats),
        "witness_pi": result.witness_pi,
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, default=str)



def _graph_label(G: ThrackleGraph) -> str:
    return getattr(G, "label", None) or "Custom graph"


def _odd_degree_vertices(G: ThrackleGraph) -> List[Vertex]:
    return [v for v, d in G.graph.degree if d % 2 == 1]


def _theta_dumbbell_info(G: ThrackleGraph):
    """Return the three u-v path lengths for a negative-l dumbbell, if applicable."""
    if getattr(G, "source_kind", None) != "dumbbell":
        return None
    p = getattr(G, "source_parameters", {})
    c1, c2, ell = p.get("c1"), p.get("c2"), p.get("l")
    if c1 is None or c2 is None or ell is None or ell >= 0:
        return None
    shared = -ell
    lengths = (shared, c1 - shared, c2 - shared)
    odd_count = sum(x % 2 for x in lengths)
    return {
        "path_lengths": lengths,
        "lps_converter_required": odd_count <= 1,
        "odd_path_count": odd_count,
        "pruning_active": False,
    }


def inspect(G: ThrackleGraph, *, show_edges: bool = True) -> dict:
    """
    Inspect any graph accepted by the v0.8.1 interface.

    This is intentionally safe to call before run(). If the graph is not
    Euler-compatible with the current activation strategy, inspect() explains
    why rather than constructing a BacktrackingSearch and failing cryptically.
    """
    if not isinstance(G, ThrackleGraph):
        raise TypeError("inspect(graph) expects a graph made by DB(...), Cycle(...), or Edges(...).")

    odd = _odd_degree_vertices(G)
    compatible = len(odd) in (0, 2)
    info = {
        "label": _graph_label(G),
        "vertices": G.graph.number_of_nodes(),
        "edges": len(G.edges),
        "odd_degree_vertices": list(odd),
        "euler_compatible": compatible,
        "required_crossings": G.total_required_crossings(),
        "candidate_count": G.candidate_count(),
        "detected_c6_cycles": None,
        "euler_edge_order": None,
        "oriented_edges": None,
        "theta": _theta_dumbbell_info(G),
    }

    print(f"Graph: {info['label']}")
    print(f"Vertices: {info['vertices']}")
    print(f"Edges: {info['edges']}")
    print(f"Odd-degree vertices: {len(odd)}" + (f" {list(odd)}" if odd else ""))
    print(f"Euler-compatible with v0.8.1 search: {'YES' if compatible else 'NO'}")
    print(f"Required proper crossings: {info['required_crossings']}")
    print(f"Naive complete-Pi systems: {info['candidate_count']:,}")
    if info["theta"] is not None:
        ti = info["theta"]
        print(f"Theta path lengths: {ti['path_lengths']}")
        if ti["lps_converter_required"]:
            print("LPS Lemma 2.3: any thrackle drawing of this theta graph must be a converter.")
        print("Theta/converter pruning: NOT active in v0.8.1 (reported for research guidance only).")

    if not compatible:
        print(
            "Reason: the current search activates edges along one Euler trail/circuit, "
            "so it requires exactly 0 or 2 odd-degree vertices. This is a program "
            "restriction, not a general restriction on thrackles."
        )
    else:
        search = BacktrackingSearch(
            G,
            use_c6_restriction=True,
            progress_interval_seconds=None,
            graph_label=_graph_label(G),
            planarity_backend="networkx",
        )
        info["detected_c6_cycles"] = len(search.six_cycles)
        info["euler_edge_order"] = list(search.order)
        info["oriented_edges"] = dict(search.oriented)
        opt_search = BacktrackingSearch(
            G, use_c6_restriction=True, progress_interval_seconds=None,
            graph_label=_graph_label(G), planarity_backend="networkx",
            activation_order="optimized",
        )
        info["optimized_edge_order"] = list(opt_search.order)
        print(f"Detected simple C6 cycles: {len(search.six_cycles)}")
        print(f"Euler edge order: {search.order}")
        print(f"v0.8.1 optimized order: {opt_search.order}")
        print("Fixed orientations (from Euler traversal):")
        for eid in search.order:
            u, v = search.oriented[eid]
            print(f"  {eid}: {u} -> {v}")

    if show_edges:
        print("Edges:")
        for e in G.edges:
            print(f"  {e.id}: {e.u} -- {e.v}")

    return info


def run(
    G: ThrackleGraph,
    *,
    time_limit: Optional[float] = 600,
    max_calls: Optional[int] = 10000000,
    progress: Optional[float] = 2,
    display=single,
    c6: bool = True,
    screening: bool = True,
    lookahead: bool = False,
    incremental: bool = True,
    debug: bool = False,
    cache: bool = False,
    branch_order: str = "constrained",
    planarity: str = "auto",
    batch: bool = True,
    workers: Optional[int] = None,
    conflicts: bool = False,
    conflict_limit: int = 128,
    activation_order: str = "optimized",
    custom_activation_order: Optional[Sequence[int]] = None,
    locked_prefix: bool = True,
    report: Optional[str] = None,
    show_start: bool = True,
    show_result: bool = True,
) -> SearchResult:
    """
    Run the generic safe search on any graph made by DB, Cycle, or Edges.

    With Boost and batch=True (default), forward screening is evaluated in
    compiled batches without changing which candidates pass or fail.

    Normal notebook use:

        graph = DB(6, 6, 0)
        run(graph)

    or, with explicit common settings:

        run(
            graph,
            time_limit=600,
            max_calls=10000000,
            progress=2,
            display=single,
        )

    Set time_limit=None and/or max_calls=None to remove that limit.
    Set progress=0 or None to disable progress output.
    """
    if not isinstance(G, ThrackleGraph):
        raise TypeError("run(graph) expects a graph made by DB(...), Cycle(...), or Edges(...).")

    odd = _odd_degree_vertices(G)
    if len(odd) not in (0, 2):
        raise ValueError(
            f"{_graph_label(G)} has {len(odd)} odd-degree vertices {odd}. "
            "v0.8.1 currently needs 0 or 2 odd-degree vertices because its "
            "activation order uses one Euler trail/circuit. Call inspect(graph) "
            "for a full compatibility report."
        )

    if display not in {single, line, dashboard, auto}:
        raise ValueError("display must be single, line, dashboard, or auto.")
    if progress is not None and progress < 0:
        raise ValueError("progress must be 0, None, or a positive number of seconds.")
    if time_limit is not None and time_limit <= 0:
        raise ValueError("time_limit must be None or a positive number of seconds.")
    if max_calls is not None and max_calls <= 0:
        raise ValueError("max_calls must be None or a positive integer.")

    progress_interval = None if progress in (None, 0) else float(progress)
    label = _graph_label(G)

    search = BacktrackingSearch(
        G,
        max_recursive_calls=max_calls,
        time_limit_seconds=time_limit,
        use_c6_restriction=c6,
        branch_order=branch_order,
        use_screening=screening,
        use_lookahead=lookahead and screening,
        incremental_partial=incremental,
        debug=debug,
        use_cache=cache,
        progress_interval_seconds=progress_interval,
        progress_mode=display,
        graph_label=label,
        planarity_backend=planarity,
        use_batch_screening=batch,
        planarity_workers=workers,
        use_kuratowski_cache=conflicts,
        kuratowski_cache_limit=conflict_limit,
        activation_order=activation_order,
        custom_activation_order=custom_activation_order,
        use_locked_prefix_pruning=locked_prefix,
    )

    if show_start:
        print(
            f"Starting {label}: {G.graph.number_of_nodes()} vertices, "
            f"{len(G.edges)} edges, {search.total_required_crossings} required crossings, "
            f"{search.total_candidates:,} complete Pi systems, "
            f"C6 cycles active={len(search.six_cycles)}, "
            f"activation={search.activation_order_mode}, "
            f"screening={search.use_screening}, lookahead={search.use_lookahead}, "
            f"incremental-partial={search.incremental_partial}, locked-prefix={search.use_locked_prefix_pruning}, "
            f"planarity={search.planarity.name}, batch={search.use_batch_screening}, "
            f"workers={search.planarity_workers}, exact-conflicts={search.use_kuratowski_cache}."
        )

    result = search.run()

    if show_result:
        print_result(result)

    if report:
        write_json_report(report, label, G, search, result)
        print(f"Wrote report: {report}")

    return result


def _v013_safety_regressions() -> None:
    """Permanent safety regressions for every new v0.13 negative inference.

    These tests separate the two proof obligations:
    (1) the frozen C8 language is exact data with complete rows whose augmented
        graphs are planar; and
    (2) the support predicate is literal subsequence extension into that data.
    The completeness of the language generation itself is audited separately by
    the face-routing generator: on C6 it reproduces the literal 46,656-system
    Fulek--Pach enumeration exactly (8 planar Pi), then the same traversal is run
    on C8.
    """
    G = DB(6, 8, -2)
    language = _db682_c8_language()
    if len(language) != 2544:
        raise AssertionError(f"v0.13 C8 language count changed: {len(language)}")
    selected = tuple(_DB682_C8_EDGE_ORDER)
    selected_set = set(selected)

    # 1. Every frozen row is a COMPLETE selected C8 row.
    complete_pis = []
    for rows in language:
        pi: Pi = {e.id: [] for e in G.edges}
        for e, row in zip(selected, rows):
            expected = {f for f in G._nonincident[e] if f in selected_set}
            if set(row) != expected or len(row) != len(expected):
                raise AssertionError("v0.13 C8 language row is not complete.")
            pi[e] = list(row)
        modeled_pairs(pi, selected)
        complete_pis.append(pi)

    # 2. Independent Fulek--Pach planarity: every generated C8 system must
    # really be a positive complete selected restriction.  Prefer the direct
    # compiled encoder, then cross-check a deterministic subset with NetworkX.
    try:
        boost = _BoostPlanarityBackend()
    except Exception:
        boost = None
    oriented = {e.id: (e.u, e.v) for e in G.edges}
    if boost is not None:
        answers = boost.batch_complete_pi_planarity(
            G, selected, complete_pis, oriented=oriented,
            workers=min(4, max(1, os.cpu_count() or 1)),
        )
        if not all(bool(x) for x in answers):
            bad = next(i for i, x in enumerate(answers) if not x)
            raise AssertionError(f"v0.13 frozen C8 language contains nonplanar system {bad}.")
    for i in range(0, len(complete_pis), max(1, len(complete_pis) // 64)):
        H = build_active_augmented_minor(
            G, complete_pis[i], selected, oriented, validate=True
        )
        if not nx.is_planar(H):
            raise AssertionError(f"v0.13 C8 system {i} failed independent NetworkX planarity.")

    # 3. The support implementation accepts complete language members and all
    # tested subsequences of them.  This directly checks the future-insertion
    # semantics used on arbitrary-gap factorized states.
    order = db682_candidate_activation_orders(G, limit=1)[0]
    dummy = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=order[:6],
    )
    for i in range(0, len(language), max(1, len(language) // 32)):
        rows = language[i]
        dummy.pi = {e.id: [] for e in G.edges}
        for e, row in zip(selected, rows):
            # Keep a deterministic proper subsequence when possible.
            dummy.pi[e] = list(row[::2])
        if not dummy._v013_c8_supported():
            raise AssertionError("v0.13 C8 support rejected a subsequence of a known language member.")

    # 4. At full C8 completion, subsequence support becomes exact language
    # membership.  Construct a deterministic row-swap perturbation not in the
    # frozen language and ensure support is zero.
    lang_keys = {tuple(rows) for rows in language}
    invalid = None
    for base in language[:64]:
        rows = [list(r) for r in base]
        rows[0][0], rows[0][1] = rows[0][1], rows[0][0]
        key = tuple(tuple(r) for r in rows)
        if key not in lang_keys:
            invalid = key
            break
    if invalid is None:
        raise AssertionError("v0.13 could not construct an invalid full C8 regression state.")
    dummy.pi = {e.id: [] for e in G.edges}
    for e, row in zip(selected, invalid):
        dummy.pi[e] = list(row)
    if dummy._v013_c8_supported():
        raise AssertionError("v0.13 C8 support accepted a full C8 Pi outside the exhaustive language.")

    # 5. Exact reflection quotient.  The eight planar C6 cores must form four
    # size-two orbits, and relabeling must preserve the augmented graph up to
    # isomorphism.
    cores, core_edges = enumerate_planar_c6_cores(
        G, activation_order=order, planarity="boost" if boost is not None else "networkx"
    )
    reps, orbits = _db682_core_orbits(cores)
    expected_orbits = {(0, 2), (1, 4), (3, 6), (5, 7)}
    if set(orbits.values()) != expected_orbits or len(reps) != 4:
        raise AssertionError(f"v0.13 unexpected C6 reflection orbits: {orbits}")
    def core_key(pi: Pi):
        return tuple((e, tuple(pi[e])) for e in sorted(pi))
    core_index = {core_key(c): i for i, c in enumerate(cores)}
    for i, c in enumerate(cores):
        rc = _db682_reflect_pi(c)
        j = core_index.get(core_key(rc))
        if j is None:
            raise AssertionError("v0.13 reflected C6 core is missing.")
        H1 = build_active_augmented_minor(G, c, core_edges, oriented, validate=True)
        H2 = build_active_augmented_minor(G, rc, core_edges, oriented, validate=True)
        if not nx.is_isomorphic(H1, H2):
            raise AssertionError(f"v0.13 reflected augmented C6 graphs {i},{j} are not isomorphic.")



def _v014_pair_root_extension_count(G: ThrackleGraph, c6_edges: Sequence[int]) -> int:
    """Exact number of full DB Pi systems extending one fixed C6+C8 root pair.

    On an edge belonging only to C6 (respectively only to C8), the cycle root
    fixes the relative order of the same-cycle nonincident partners and leaves
    all other partners freely permuted/interleaved.  On the two shared R-path
    edges, C6 and C8 fix two disjoint partner lists, so the full row is an
    arbitrary shuffle preserving each list internally.  Multiplying these exact
    row counts gives the root size; no planarity assumption enters the count.
    """
    c6 = set(int(e) for e in c6_edges)
    c8 = set(int(e) for e in _DB682_C8_EDGE_ORDER)
    if c6 | c8 != {e.id for e in G.edges}:
        raise AssertionError("v0.14 C6+C8 roots do not cover all DB original edges.")
    total = 1
    for e in G.edges:
        eid = e.id
        allp = set(G._nonincident[eid])
        a = allp & c6 if eid in c6 else set()
        b = allp & c8 if eid in c8 else set()
        if eid in c6 and eid in c8:
            if a & b:
                raise AssertionError("v0.14 shared C6/C8 row constraints unexpectedly overlap.")
            if a | b != allp:
                raise AssertionError("v0.14 shared C6/C8 row constraints miss partners.")
            row_count = factorial(len(allp)) // (factorial(len(a)) * factorial(len(b)))
        elif eid in c6:
            row_count = factorial(len(allp)) // factorial(len(a))
        elif eid in c8:
            row_count = factorial(len(allp)) // factorial(len(b))
        else:
            raise AssertionError("v0.14 root-count edge belongs to neither cycle.")
        total *= row_count
    return total


def _v014_safety_regressions() -> None:
    """Blast every new v0.14 inference/optimization against exact references."""
    G = DB(6, 8, -2)
    language = _db682_c8_language()
    tables = _db682_c8_row_mask_tables()
    order = db682_candidate_activation_orders(G, limit=1)[0]
    core_edges = tuple(order[:6])

    # 1. Exhaustively differential-test every possible ordered partial C8 row.
    # A C8 row has five crossing partners, so sum_k P(5,k)=326 states per edge.
    # The fast table must equal a literal scan of all 2,544 complete rows.
    for row_index, e in enumerate(_DB682_C8_EDGE_ORDER):
        partners = tuple(sorted({x for rows in language for x in rows[row_index]}))
        if len(partners) != 5:
            raise AssertionError("v0.14 expected exactly five C8 partners per row.")
        tested = 0
        for k in range(6):
            for seq in permutations(partners, k):
                literal = 0
                bit = 1
                for system in language:
                    if DB682FactorizedSearch._is_subsequence_tuple(seq, system[row_index]):
                        literal |= bit
                    bit <<= 1
                fast = int(tables[int(e)].get(tuple(seq), 0))
                if fast != literal:
                    raise AssertionError(
                        f"v0.14 C8 row-mask table mismatch on edge {e}, seq={seq}."
                    )
                tested += 1
        if tested != 326:
            raise AssertionError(f"v0.14 expected 326 row states on edge {e}; got {tested}.")

    # 2. Incremental support must equal full eight-row recomputation after every
    # insertion.  Build partial rows in awkward insertion orders so this checks
    # arbitrary-gap updates, not merely appends.
    dummy = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=core_edges,
    )
    insertion_order = (2, 0, 4, 1, 3)
    for rows in language[::max(1, len(language)//24)]:
        dummy.pi = {e.id: [] for e in G.edges}
        mask = dummy._v013_c8_all_mask
        chosen = {int(e): set() for e in _DB682_C8_EDGE_ORDER}
        for step in range(5):
            for e, target in zip(_DB682_C8_EDGE_ORDER, rows):
                chosen[int(e)].add(insertion_order[step])
                dummy.pi[int(e)] = [
                    x for j, x in enumerate(target) if j in chosen[int(e)]
                ]
                mask = dummy._v014_c8_refine_mask(mask, (int(e),))
                full = dummy._v013_c8_all_mask
                for f in _DB682_C8_EDGE_ORDER:
                    seq = tuple(x for x in dummy.pi[int(f)] if x in _DB682_C8_EDGE_SET)
                    full &= int(tables[int(f)].get(seq, 0))
                if mask != full:
                    raise AssertionError("v0.14 incremental C8 support differs from full recomputation.")

    # 3. The early-slot factorization may bundle only hosts outside C8.  This is
    # the entire logical reason their physical slot choices cannot change C8
    # support.  Check the condition for every target tail stage.
    template = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=core_edges,
    )
    for edge_index in range(6, len(order)):
        partners = tuple(e for e in core_edges if e in template.older_required[edge_index])
        sensitive = tuple(e for e in partners if e in _DB682_C8_EDGE_SET)
        insensitive = tuple(e for e in partners if e not in _DB682_C8_EDGE_SET)
        if any(e in _DB682_C8_EDGE_SET for e in insensitive):
            raise AssertionError("v0.14 bundled a C8-sensitive host as insensitive.")
        if any(e not in _DB682_C8_EDGE_SET for e in sensitive):
            raise AssertionError("v0.14 sensitive host classification is inconsistent.")
        if not sensitive:
            raise AssertionError("v0.14 target q-stage unexpectedly has no C8-sensitive C6 host.")

    # 4. C6+C8 pair-root arithmetic, although not yet used as a pruning rule in
    # the production DFS, is certified here because it underlies v0.14's
    # symbolic support interpretation and future pair-root partitioning.
    try:
        _BoostPlanarityBackend()
        audit_planarity = "boost"
    except Exception:
        audit_planarity = "networkx"
    cores, found_core_edges = enumerate_planar_c6_cores(
        G, activation_order=order, planarity=audit_planarity
    )
    if tuple(found_core_edges) != core_edges or len(cores) != 8:
        raise AssertionError("v0.14 C6 root audit changed the eight retained cores.")
    pair_root = _v014_pair_root_extension_count(G, core_edges)
    if pair_root <= 0:
        raise AssertionError("v0.14 C6+C8 pair-root size is not positive.")
    pair_count = len(cores) * len(language)
    if pair_count != 20352:
        raise AssertionError(f"v0.14 expected 20,352 C6+C8 root pairs; got {pair_count}.")
    valid_pair_space = pair_count * pair_root
    if valid_pair_space >= G.candidate_count():
        raise AssertionError("v0.14 C6+C8 restriction failed to reduce the full Pi space.")

    # 5. Real-stage differential for early C8-sensitive slot bundling.  Build a
    # deterministic complete Pi satisfying one C6+C8 root, project it to the
    # parent of the q9 stage, then compare literal v0.13 support on every full
    # C6-host slot combination against the v0.14 bundled decision.  Insensitive
    # slots must never change supported/dead status.
    core0 = cores[0]
    c8_rows0 = language[0]
    c8_pi0 = {int(e): list(r) for e, r in zip(_DB682_C8_EDGE_ORDER, c8_rows0)}
    c6_set = set(core_edges)
    c8_set = set(_DB682_C8_EDGE_ORDER)
    full_probe: Pi = {e.id: [] for e in G.edges}
    for edge in G.edges:
        e = edge.id
        allp = set(G._nonincident[e])
        a = list(core0.get(e, [])) if e in c6_set else []
        b = list(c8_pi0.get(e, [])) if e in c8_set else []
        if set(a) & set(b):
            raise AssertionError("v0.14 probe root has overlapping C6/C8 row constraints.")
        used = set(a) | set(b)
        full_probe[e] = a + b + sorted(allp - used)
    validate_full_pi(G, full_probe)

    probe = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend=audit_planarity, activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=core_edges,
    )
    probe_domains, _ = _db682_build_local_domains(probe, core0, core_edges)
    probe.db682_local_domains = probe_domains
    edge_index = 8  # current edge 9 in the frozen [7,10,9,8,6,11] tail.
    active = set(order[:edge_index])
    probe.pi = {e.id: [] for e in G.edges}
    for e in active:
        probe.pi[e] = [x for x in full_probe[e] if x in active]
    current = order[edge_index]
    older = tuple(probe.older_required[edge_index])
    partners = tuple(e for e in core_edges if e in older)
    extras = tuple(e for e in older if e not in probe.db682_core_set)
    _, prepared = probe._stage_allowed_weight(
        edge_index, probe_domains[current], partners, extras
    )
    parent_mask = probe._v013_c8_support_mask()
    reference_dead = bundled_dead = full_slot_states = 0
    checked_signatures = 0
    for sig, slot_lists, _ in prepared[:20]:
        probe.pi[current] = list(sig.core_order)
        sig_mask = probe._v014_c8_refine_mask(parent_mask, (current,))
        if not sig_mask:
            probe.pi[current] = []
            continue
        sensitive_idx = tuple(
            j for j, host in enumerate(partners) if host in _DB682_C8_EDGE_SET
        )
        insensitive_idx = tuple(j for j in range(len(partners)) if j not in sensitive_idx)
        sensitive_hosts = tuple(partners[j] for j in sensitive_idx)
        insensitive_hosts = tuple(partners[j] for j in insensitive_idx)
        sensitive_lists = tuple(slot_lists[j] for j in sensitive_idx)
        insensitive_lists = tuple(slot_lists[j] for j in insensitive_idx)
        insensitive_count = prod(len(x) for x in insensitive_lists) if insensitive_lists else 1
        for sensitive_combo in product(*sensitive_lists) if sensitive_lists else [()]:
            for host, pos in zip(sensitive_hosts, sensitive_combo):
                probe.pi[host].insert(pos, current)
            bundle_mask = probe._v014_c8_refine_mask(sig_mask, sensitive_hosts)
            if not bundle_mask:
                bundled_dead += insensitive_count
            iterator = product(*insensitive_lists) if insensitive_lists else [()]
            for insensitive_combo in iterator:
                for host, pos in zip(insensitive_hosts, insensitive_combo):
                    probe.pi[host].insert(pos, current)
                full_slot_states += 1
                if not probe._v013_c8_support_mask():
                    reference_dead += 1
                for host, pos in reversed(tuple(zip(insensitive_hosts, insensitive_combo))):
                    got = probe.pi[host].pop(pos)
                    if got != current:
                        raise AssertionError("v0.14 probe failed to restore insensitive host.")
            for host, pos in reversed(tuple(zip(sensitive_hosts, sensitive_combo))):
                got = probe.pi[host].pop(pos)
                if got != current:
                    raise AssertionError("v0.14 probe failed to restore sensitive host.")
        probe.pi[current] = []
        checked_signatures += 1
    if checked_signatures == 0 or full_slot_states == 0 or reference_dead == 0:
        raise AssertionError("v0.14 slot-bundling differential did not exercise a dead real-stage case.")
    if bundled_dead != reference_dead:
        raise AssertionError(
            "v0.14 sensitive-slot bundling disagrees with literal full-slot C8 support: "
            f"bundled={bundled_dead}, literal={reference_dead}."
        )

    # 6. Reflection must permute the complete C8 language exactly, so pairing
    # C6 roots never loses a C8-supported completion.
    selected = tuple(_DB682_C8_EDGE_ORDER)
    lang_index = {tuple(rows): i for i, rows in enumerate(language)}
    if len(lang_index) != len(language):
        raise AssertionError("v0.14 frozen C8 language contains duplicate systems.")
    fixed_c8 = 0
    for rows in language:
        pi: Pi = {e.id: [] for e in G.edges}
        for e, row in zip(selected, rows):
            pi[int(e)] = list(row)
        rpi = _db682_reflect_pi(pi)
        rkey = tuple(tuple(rpi[int(e)]) for e in selected)
        if rkey not in lang_index:
            raise AssertionError("v0.14 reflection maps a C8 language member outside the language.")
        if rkey == tuple(rows):
            fixed_c8 += 1
    # A fixed C8 system would not itself make the quotient unsafe, but record
    # the observed target fact and catch accidental orientation-map changes.
    if fixed_c8 != 0:
        raise AssertionError(f"v0.14 expected no fixed labeled C8 systems; found {fixed_c8}.")

    # 7. Independent C8 completeness certificate.  This is deliberately
    # stronger than merely checking that the frozen 2,544 rows are individually
    # planar.  Misereh--Nikolayevsky (Annular and pants thrackles, DMTCS 20(1),
    # 2018) report that, up to isotopy and Reidemeister-III moves, there are
    # exactly three thrackled eight-cycles.  We certify that the frozen exact
    # language is a union of exactly three distinct such classes:
    #
    #   (a) every one of all 2,544 systems is independently planar in NetworkX;
    #   (b) the language is closed under all 16 dihedral relabelings of C8;
    #   (c) whenever three pairwise nonadjacent edges have their mutual
    #       crossings consecutive on all three rows, the combinatorial RIII
    #       flip is also in the language; and
    #   (d) even after allowing ALL such combinatorial flips (a superset of
    #       geometrically legal empty-triangle RIII moves) plus dihedral
    #       relabelings, the language has exactly three connected components.
    #
    # Because the allowed graph contains every genuine isotopy/RIII transition,
    # three components imply at least three genuine equivalence classes among
    # the stored systems.  The published global classification says there are
    # only three.  Closure then makes each whole global class present, proving
    # exhaustiveness of the labeled/oriented language after dihedral labeling.
    # This certificate is independent of the historical face-routing generator.
    oriented = {e.id: (e.u, e.v) for e in G.edges}
    for i, rows in enumerate(language):
        pi: Pi = {e.id: [] for e in G.edges}
        for e, row in zip(selected, rows):
            pi[int(e)] = list(row)
        H = build_active_augmented_minor(G, pi, selected, oriented, validate=True)
        if not nx.is_planar(H):
            raise AssertionError(f"v0.14 C8 completeness certificate found nonplanar system {i}.")

    # Convert target edge IDs/orientations to local cycle-edge labels 0..7 with
    # every local edge oriented in one common direction around C8.
    edge_obj = {e.id: e for e in G.edges}
    first, second = selected[0], selected[1]
    common = set((edge_obj[first].u, edge_obj[first].v)) & set((edge_obj[second].u, edge_obj[second].v))
    if len(common) != 1:
        raise AssertionError("v0.14 C8 edge order is not a simple cyclic order.")
    v1 = next(iter(common))
    v0 = edge_obj[first].v if edge_obj[first].u == v1 else edge_obj[first].u
    cycle_vertices = [v0, v1]
    cur = v1
    for eid in selected[1:]:
        ed = edge_obj[eid]
        if ed.u == cur:
            nxt = ed.v
        elif ed.v == cur:
            nxt = ed.u
        else:
            raise AssertionError("v0.14 C8 edge order lost vertex continuity.")
        cycle_vertices.append(nxt)
        cur = nxt
    if cycle_vertices[-1] != cycle_vertices[0] or len(cycle_vertices) != 9:
        raise AssertionError("v0.14 C8 edge order failed to close exactly once.")
    edge_to_local = {int(e): i for i, e in enumerate(selected)}
    local_forward = {}
    for i, eid in enumerate(selected):
        ed = edge_obj[int(eid)]
        a, b = cycle_vertices[i], cycle_vertices[i + 1]
        if (ed.u, ed.v) == (a, b):
            local_forward[int(eid)] = True
        elif (ed.u, ed.v) == (b, a):
            local_forward[int(eid)] = False
        else:
            raise AssertionError("v0.14 C8 local orientation map is inconsistent.")

    def _localize_c8(rows):
        out = []
        for eid, row in zip(selected, rows):
            rr = [edge_to_local[int(x)] for x in row]
            if not local_forward[int(eid)]:
                rr.reverse()
            out.append(tuple(rr))
        return tuple(out)

    local_language = tuple(_localize_c8(rows) for rows in language)
    local_set = set(local_language)
    if len(local_set) != len(language):
        raise AssertionError("v0.14 C8 local normalization created duplicate systems.")
    local_index = {sys0: i for i, sys0 in enumerate(local_language)}

    def _dih(sys0, shift, sense):
        out = [None] * 8
        for i, row in enumerate(sys0):
            if sense == 1:
                j = (i + shift) % 8
                mapped = [((x + shift) % 8) for x in row]
            else:
                j = (shift - i - 1) % 8
                mapped = [((shift - x - 1) % 8) for x in row]
                mapped.reverse()
            out[j] = tuple(mapped)
        return tuple(out)

    adjacency = [set() for _ in local_language]
    for i, sys0 in enumerate(local_language):
        for sense in (1, -1):
            for shift in range(8):
                image = _dih(sys0, shift, sense)
                j = local_index.get(image)
                if j is None:
                    raise AssertionError("v0.14 C8 language is not closed under a dihedral relabeling.")
                adjacency[i].add(j)
                adjacency[j].add(i)

    triples = [
        t for t in combinations(range(8), 3)
        if all(((a - b) % 8) not in (0, 1, 7) for a, b in combinations(t, 2))
    ]
    if len(triples) != 16:
        raise AssertionError("v0.14 expected 16 triples of pairwise nonadjacent C8 edges.")

    def _r3_flip(sys0, triple):
        rows = [list(r) for r in sys0]
        for eid in triple:
            others = [x for x in triple if x != eid]
            p0, p1 = rows[eid].index(others[0]), rows[eid].index(others[1])
            if abs(p0 - p1) != 1:
                return None
        for eid in triple:
            others = [x for x in triple if x != eid]
            p0, p1 = rows[eid].index(others[0]), rows[eid].index(others[1])
            rows[eid][p0], rows[eid][p1] = rows[eid][p1], rows[eid][p0]
        return tuple(tuple(r) for r in rows)

    directed_r3 = 0
    for i, sys0 in enumerate(local_language):
        for triple in triples:
            image = _r3_flip(sys0, triple)
            if image is None:
                continue
            directed_r3 += 1
            j = local_index.get(image)
            if j is None:
                raise AssertionError("v0.14 C8 language is not closed under an RIII crossing-order flip.")
            adjacency[i].add(j)
            adjacency[j].add(i)
    if directed_r3 != 10624:
        raise AssertionError(f"v0.14 C8 RIII closure count changed: {directed_r3} != 10624.")

    seen = set()
    component_sizes = []
    for root in range(len(local_language)):
        if root in seen:
            continue
        stack = [root]
        seen.add(root)
        size = 0
        while stack:
            u = stack.pop()
            size += 1
            for v in adjacency[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        component_sizes.append(size)
    if sorted(component_sizes) != [656, 896, 992]:
        raise AssertionError(
            "v0.14 C8 classification certificate changed components: "
            f"{sorted(component_sizes)}."
        )

    # 8. Exact-coverage arithmetic must remain arbitrary precision.  One root
    # already exceeds unsigned 128-bit range, so a future native engine cannot
    # silently narrow these counts.
    if pair_root <= (1 << 128) - 1:
        raise AssertionError("v0.14 pair-root count unexpectedly fits in 128 bits; revisit overflow guard.")



# ---------------------------------------------------------------------------
# v0.15 H2 language generator / certification helpers
# ---------------------------------------------------------------------------
_V015_H2_GEN_STATE = None

def _v015_h2_generator_init(planarity: str = "boost") -> None:
    """Initialize one deterministic H2-generation worker."""
    global _V015_H2_GEN_STATE
    G = DB(6, 8, -2)
    order = db682_candidate_activation_orders(G, limit=1)[0]
    reference = BacktrackingSearch(
        G, max_recursive_calls=1, time_limit_seconds=1,
        use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
    )
    oriented = dict(reference.oriented)
    u, v = oriented[_DB682_H2_EDGE]
    oriented[_DB682_H2_EDGE] = (v, u)  # enumeration-only orientation reversal
    _V015_H2_GEN_STATE = {
        "G": G,
        "backend": _make_planarity_backend(planarity),
        "oriented": oriented,
        "crossing_cache": reference.crossing_cache,
        "language": _db682_c8_language(),
        "selected": tuple(_DB682_H2_SELECTED),
        "partners": tuple(_DB682_H2_PARTNERS),
    }


def _v015_generate_h2_parent(parent_index: int):
    """Exhaustively generate every planar H2 extension of one C8 parent.

    The DFS enumerates every permutation of the six edge-2 crossings and every
    insertion position into the six fixed partner C8 rows.  It prunes only when
    ``build_locked_prefix_minor`` is nonplanar.  That graph is a minor of every
    completion.  At a leaf the current edge is complete, so the tested graph is
    exactly the complete H2 augmented graph.  Reversing the arbitrary
    orientation of edge 2 merely reverses its row; the emitted record converts
    back to the program orientation.
    """
    if _V015_H2_GEN_STATE is None:
        _v015_h2_generator_init("boost")
    st = _V015_H2_GEN_STATE
    G = st["G"]
    parent_index = int(parent_index)
    c8_rows = st["language"][parent_index]
    pi: Pi = {e.id: [] for e in G.edges}
    for e, row in zip(_DB682_C8_EDGE_ORDER, c8_rows):
        pi[int(e)] = list(row)
    signatures = set()
    nodes = 0
    tests = 0

    def rec(remaining: Tuple[int, ...]):
        nonlocal nodes, tests
        nodes += 1
        if not remaining:
            canonical_order = tuple(reversed(pi[_DB682_H2_EDGE]))
            gaps = tuple(pi[int(e)].index(_DB682_H2_EDGE) for e in _DB682_H2_PARTNERS)
            signatures.add((parent_index, canonical_order, gaps))
            return
        for old in remaining:
            child = tuple(x for x in remaining if x != old)
            for pos in range(len(pi[int(old)]) + 1):
                pi[int(old)].insert(pos, _DB682_H2_EDGE)
                pi[_DB682_H2_EDGE].append(int(old))
                H = build_locked_prefix_minor(
                    G, pi, st["selected"], st["oriented"],
                    current_eid=_DB682_H2_EDGE, current_complete=(not child),
                    validate=False, crossing_cache=st["crossing_cache"],
                )
                tests += 1
                if st["backend"].is_planar(H):
                    rec(child)
                got_new = pi[_DB682_H2_EDGE].pop()
                got_old = pi[int(old)].pop(pos)
                if got_new != int(old) or got_old != _DB682_H2_EDGE:
                    raise AssertionError("v0.15 H2 generator failed to restore Pi.")

    rec(tuple(_DB682_H2_PARTNERS))
    return tuple(sorted(signatures)), int(nodes), int(tests)


def _v015_generate_all_h2_records(*, processes: Optional[int] = None, planarity: str = "boost"):
    """Deterministically regenerate the complete frozen H2 record set."""
    n = _DB682_C8_LANGUAGE_COUNT
    cpu = max(1, os.cpu_count() or 1)
    if processes is None:
        processes = min(cpu, 5)
    processes = max(1, int(processes))
    records = []
    nodes = tests = 0
    if processes == 1:
        _v015_h2_generator_init(planarity)
        for i in range(n):
            sigs, nn, tt = _v015_generate_h2_parent(i)
            records.extend(sigs); nodes += nn; tests += tt
    else:
        methods = mp.get_all_start_methods()
        ctx = mp.get_context("fork" if "fork" in methods else "spawn")
        with ctx.Pool(
            processes=processes,
            initializer=_v015_h2_generator_init,
            initargs=(planarity,),
        ) as pool:
            for sigs, nn, tt in pool.imap(_v015_generate_h2_parent, range(n), chunksize=2):
                records.extend(sigs); nodes += nn; tests += tt
    records = tuple(sorted(records))
    if len(set(records)) != len(records):
        raise AssertionError("v0.15 H2 regeneration produced duplicate records.")
    return records, {"nodes": int(nodes), "planarity_tests": int(tests)}


def _v015_h2_records_to_raw(records) -> bytes:
    out = bytearray()
    for parent, order, gaps in records:
        parent = int(parent)
        out.extend((parent & 255, (parent >> 8) & 255))
        out.extend(int(x) for x in order)
        out.extend(int(x) for x in gaps)
    return bytes(out)


def _v015_certify_frozen_h2_full(*, processes: Optional[int] = None, planarity: str = "boost") -> dict:
    """Regenerate H2 from first principles and require exact byte equality."""
    started = time.perf_counter()
    regenerated, report = _v015_generate_all_h2_records(processes=processes, planarity=planarity)
    frozen = _db682_h2_records()
    if regenerated != frozen:
        raise AssertionError(
            f"v0.15 full H2 regeneration differs from frozen data: "
            f"regen={len(regenerated)}, frozen={len(frozen)}."
        )
    raw = _v015_h2_records_to_raw(regenerated)
    digest = hashlib.sha256(raw).hexdigest()
    if digest != _DB682_H2_LANGUAGE_RAW_SHA256:
        raise AssertionError("v0.15 regenerated H2 byte hash differs from frozen hash.")
    return {
        "records": len(regenerated),
        "sha256": digest,
        "nodes": int(report["nodes"]),
        "planarity_tests": int(report["planarity_tests"]),
        "seconds": float(time.perf_counter() - started),
    }



def _v015_safety_regressions() -> None:
    """Pressure-test every new v0.15 negative inference against exact references."""
    if _DB682_H2_LANGUAGE_COUNT <= 0:
        raise AssertionError("v0.15 H2 safety test requires frozen H2 data.")
    G = DB(6, 8, -2)
    records = _db682_h2_records()
    if len(records) != _DB682_H2_LANGUAGE_COUNT:
        raise AssertionError("v0.15 H2 record count changed after decode.")
    groups = _db682_h2_full_row_groups()
    order = db682_candidate_activation_orders(G, limit=1)[0]
    core_edges = tuple(order[:6])

    # 1. Every frozen record reconstructs a COMPLETE H2 restriction.  Test all
    # members with the independent direct complete-Pi Boost encoder (or literal
    # NetworkX fallback), and additionally sample NetworkX even when Boost is
    # available so a compiled-encoder error cannot silently validate the data.
    selected_h2 = tuple(_DB682_H2_SELECTED)
    selected_h2_set = set(selected_h2)
    try:
        backend = _BoostPlanarityBackend()
        use_batch = True
    except Exception:
        backend = _NetworkXPlanarityBackend()
        use_batch = False
    oriented = BacktrackingSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=False,
    ).oriented

    batch = []
    sample_stride = max(1, len(records) // 128)
    for i, record in enumerate(records):
        rows = _db682_h2_complete_rows(record)
        pi: Pi = {e.id: [] for e in G.edges}
        for e in selected_h2:
            row = tuple(rows[int(e)])
            expected = {f for f in G._nonincident[int(e)] if f in selected_h2_set}
            if set(row) != expected or len(row) != len(expected):
                raise AssertionError(f"v0.15 H2 record {i} contains an incomplete selected row.")
            pi[int(e)] = list(row)
        batch.append(pi)
        if i % sample_stride == 0:
            H = build_active_augmented_minor(G, pi, selected_h2, oriented, validate=True)
            if not nx.is_planar(H):
                raise AssertionError(f"v0.15 H2 record {i} failed independent NetworkX planarity.")
        if len(batch) >= 512 or i + 1 == len(records):
            if use_batch:
                answers = backend.batch_complete_pi_planarity(
                    G, selected_h2, batch, oriented=oriented,
                    workers=min(4, max(1, os.cpu_count() or 1)),
                )
            else:
                answers = [
                    nx.is_planar(build_active_augmented_minor(
                        G, p0, selected_h2, oriented, validate=True
                    )) for p0 in batch
                ]
            if not all(answers):
                raise AssertionError("v0.15 frozen H2 language contains a nonplanar complete member.")
            batch.clear()

    # 2. The reflected H5 interpretation is literal.  For deterministic sample
    # members, reflect the complete H2 Pi, verify complete H5 row contents, and
    # compare the fast pulled-back row mask with literal membership of that bit.
    dummy = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=core_edges,
    )
    dummy.use_v015_h2_language = True
    dummy.use_v015_h5_language = True
    h5_selected = set(_DB682_H5_SELECTED_SET)
    for i in range(0, len(records), max(1, len(records)//96)):
        rows = _db682_h2_complete_rows(records[i])
        pi: Pi = {e.id: [] for e in G.edges}
        for e in selected_h2:
            pi[int(e)] = list(rows[int(e)])
        rpi = _db682_reflect_pi(pi)
        for e in h5_selected:
            expected = {f for f in G._nonincident[int(e)] if f in h5_selected}
            row = tuple(rpi[int(e)])
            if set(row) != expected or len(row) != len(expected):
                raise AssertionError("v0.15 reflected H5 member is incomplete.")
            if not (dummy._v015_h5_row_mask(int(e), row) & (1 << i)):
                raise AssertionError("v0.15 H5 pulled-back row mask lost its reflected source member.")

    # 3. Differential-test lazy H2 row masks against literal member-by-member
    # scans on deterministic partial rows.  Complete rows are reconstructed once
    # per edge so the reference is independent of the grouped-mask cache.
    for e in selected_h2:
        full_rows = [tuple(_db682_h2_complete_rows(r)[int(e)]) for r in records]
        probes = set([()])
        step = max(1, len(full_rows)//24)
        for row in full_rows[::step][:24]:
            # all 2^len(row) subsequences of a few actual complete rows
            for bits in range(1 << len(row)):
                if bits % max(1, (1 << len(row)) // 8) == 0:
                    probes.add(tuple(row[j] for j in range(len(row)) if bits & (1 << j)))
        for seq in list(probes)[:80]:
            literal = 0
            for i, row in enumerate(full_rows):
                if DB682FactorizedSearch._is_subsequence_tuple(tuple(seq), row):
                    literal |= 1 << i
            fast = dummy._v015_h2_row_mask(int(e), tuple(seq))
            if fast != literal:
                raise AssertionError(f"v0.15 H2 row-mask differential failed on edge {e}, seq={seq}.")

    # 4. Incremental H2 support must equal full nine-row recomputation after
    # every symmetrically inserted crossing, including arbitrary-gap insertions.
    def exercise_incremental(which: int, member_pi: Pi):
        selected = _DB682_H2_SELECTED_SET if which == 2 else _DB682_H5_SELECTED_SET
        dummy.pi = {e.id: [] for e in G.edges}
        mask = dummy._v015_h2_all_mask
        pairs = []
        sel = sorted(selected)
        for a_i, a in enumerate(sel):
            for b in sel[a_i+1:]:
                if b in G._nonincident[a]:
                    pairs.append((a, b))
        # An intentionally non-geometric order exercises insertions into gaps.
        pairs = tuple(reversed(pairs[::2])) + tuple(pairs[1::2])
        for a, b in pairs:
            for host, other in ((a, b), (b, a)):
                target = member_pi[int(host)]
                before = set(target[:target.index(int(other))])
                pos = sum(1 for x in dummy.pi[int(host)] if x in before)
                dummy.pi[int(host)].insert(pos, int(other))
            mask = dummy._v015_refine_selected_mask(mask, (a, b), which)
            full = dummy._v015_selected_support_mask(which)
            if mask != full:
                raise AssertionError(f"v0.15 H{which} incremental support differs from full recomputation.")

    for i in range(0, len(records), max(1, len(records)//24)):
        rows = _db682_h2_complete_rows(records[i])
        h2pi: Pi = {e.id: [] for e in G.edges}
        for e in selected_h2:
            h2pi[int(e)] = list(rows[int(e)])
        exercise_incremental(2, h2pi)
        exercise_incremental(5, _db682_reflect_pi(h2pi))

    # 5. Real q7-stage support-driven slot factoring vs literal full-slot
    # enumeration.  The two computations must classify exactly the same number
    # of complete sensitive/insensitive host tuples as impossible.
    cores, found_core_edges = enumerate_planar_c6_cores(G, activation_order=order, planarity="boost" if use_batch else "networkx")
    if tuple(found_core_edges) != core_edges or len(cores) != 8:
        raise AssertionError("v0.15 real-stage audit lost the eight C6 cores.")
    probe = DB682FactorizedSearch(
        G, use_c6_restriction=False, use_screening=False, use_lookahead=False,
        incremental_partial=False, use_cache=False, progress_interval_seconds=None,
        planarity_backend="boost" if use_batch else "networkx", activation_order="custom",
        custom_activation_order=order, use_locked_prefix_pruning=True,
        core_edges=core_edges,
    )
    probe.use_v015_h2_language = True
    probe.use_v015_h5_language = True
    probe.use_v015_support_driven_slots = True
    probe.use_v013_c8_language = True
    probe.use_v014_incremental_c8 = True
    probe.use_v014_c8_sensitive_slots = True
    _seed_search_with_core(probe, cores[0], core_edges)
    domains, _ = _db682_build_local_domains(probe, cores[0], core_edges)
    probe.db682_local_domains = domains
    edge_index = 6  # q7, no older q extras: cleanest exact host-slot differential
    current = order[edge_index]
    partners = tuple(e for e in core_edges if e in probe.older_required[edge_index])
    extras = tuple(e for e in probe.older_required[edge_index] if e not in probe.db682_core_set)
    if extras:
        raise AssertionError("v0.15 q7 slot differential expected no older q extras.")
    _, prepared = probe._stage_allowed_weight(edge_index, domains[current], partners, extras)
    pc8 = probe._v013_c8_support_mask()
    ph2 = probe._v015_selected_support_mask(2)
    ph5 = probe._v015_selected_support_mask(5)
    exercised = False
    for sig, slot_lists, _weight in prepared:
        probe.pi[current] = list(sig.core_order)
        sc8 = probe._v014_c8_child_mask(pc8, (current,))
        sh2 = probe._v015_child_selected_mask(ph2, (current,), 2)
        sh5 = probe._v015_child_selected_mask(ph5, (current,), 5)
        if probe._v015_supports_dead(sc8, sh2, sh5):
            probe.pi[current] = []
            continue
        literal_dead = 0
        total = 0
        for combo in product(*slot_lists):
            for host, pos in zip(partners, combo):
                probe.pi[host].insert(pos, current)
            fc8 = probe._v014_c8_child_mask(sc8, partners)
            fh2 = probe._v015_child_selected_mask(sh2, partners, 2)
            fh5 = probe._v015_child_selected_mask(sh5, partners, 5)
            total += 1
            if probe._v015_supports_dead(fc8, fh2, fh5):
                literal_dead += 1
            for host, pos in reversed(tuple(zip(partners, combo))):
                if probe.pi[host].pop(pos) != current:
                    raise AssertionError("v0.15 literal slot differential restore failed.")

        # Independently count the prefix-factorized dead full tuples.
        sensitive = tuple(j for j,h in enumerate(partners) if (
            h in _DB682_C8_EDGE_SET or h in _DB682_H2_SELECTED_SET or h in _DB682_H5_SELECTED_SET
        ))
        insensitive = tuple(j for j in range(len(partners)) if j not in sensitive)
        sens_hosts = tuple(partners[j] for j in sensitive)
        sens_lists = tuple(slot_lists[j] for j in sensitive)
        ins_count = prod(len(slot_lists[j]) for j in insensitive) if insensitive else 1
        prefix_dead = 0
        def rec_pref(j, c8m, h2m, h5m):
            nonlocal prefix_dead
            if j == len(sens_hosts):
                return
            host = sens_hosts[j]
            rem = prod(len(sens_lists[k]) for k in range(j+1, len(sens_lists))) if j+1 < len(sens_lists) else 1
            for pos in sens_lists[j]:
                probe.pi[host].insert(pos, current)
                nc8 = probe._v014_c8_child_mask(c8m, (host,)) if host in _DB682_C8_EDGE_SET else c8m
                nh2 = probe._v015_child_selected_mask(h2m, (host,), 2) if host in _DB682_H2_SELECTED_SET else h2m
                nh5 = probe._v015_child_selected_mask(h5m, (host,), 5) if host in _DB682_H5_SELECTED_SET else h5m
                if probe._v015_supports_dead(nc8, nh2, nh5):
                    prefix_dead += rem * ins_count
                else:
                    rec_pref(j+1, nc8, nh2, nh5)
                if probe.pi[host].pop(pos) != current:
                    raise AssertionError("v0.15 prefix slot differential restore failed.")
        rec_pref(0, sc8, sh2, sh5)
        probe.pi[current] = []
        if prefix_dead != literal_dead:
            raise AssertionError(
                f"v0.15 support-driven slot count mismatch: prefix={prefix_dead}, literal={literal_dead}."
            )
        if total and literal_dead:
            exercised = True
            break
    if not exercised:
        raise AssertionError("v0.15 support-driven differential did not exercise a dead real-stage tuple.")

    # 6. Re-run the exact frozen generator on several spread-out C8 parents and
    # require byte-for-byte record equality.  Full all-2,544 regeneration is a
    # separate release-certificate command because it is intentionally costly.
    frozen_by_parent = defaultdict(list)
    for r in records:
        frozen_by_parent[int(r[0])].append(r)
    _v015_h2_generator_init("boost" if use_batch else "networkx")
    parent_samples = sorted({0, 1, 127, 511, 1023, 1535, 2047, 2543})
    for parent in parent_samples:
        generated, _, _ = _v015_generate_h2_parent(parent)
        if tuple(generated) != tuple(frozen_by_parent[parent]):
            raise AssertionError(f"v0.15 H2 generator/frozen mismatch on C8 parent {parent}.")

def _add_common_search_args(parser, *, max_calls: int, time_limit: float):
    parser.add_argument("--max-calls", type=int, default=max_calls)
    parser.add_argument("--time-limit", type=float, default=time_limit)
    parser.add_argument("--report", type=str, default=None)
    parser.add_argument(
        "--progress",
        type=float,
        default=2.0,
        help="Progress update interval in seconds; use 0 to disable.",
    )
    parser.add_argument(
        "--progress-mode",
        choices=["auto", "single", "line", "dashboard"],
        default="auto",
        help=(
            "single shows the full multi-line dashboard and refreshes that same "
            "dashboard in place; line prints a fresh copy of the same dashboard "
            "each update; auto selects single for a real terminal and line for "
            "redirected/notebook subprocess output."
        ),
    )
    parser.add_argument(
        "--branch-order",
        choices=["natural", "constrained"],
        default="constrained",
    )
    parser.add_argument(
        "--no-screening",
        action="store_true",
        help=(
            "Disable v0.8.1 forward screening and use the v0.3-style immediate-test recursion."
        ),
    )
    parser.add_argument(
        "--no-lookahead",
        action="store_true",
        help="Keep forward screening but disable one-level lookahead ordering.",
    )
    parser.add_argument(
        "--workers", type=int, default=None,
        help="Compiled Boost worker count; auto uses up to 4 CPUs.",
    )
    parser.add_argument(
        "--conflicts", action="store_true",
        help="Enable safe exact Kuratowski-certificate cache (off by default).",
    )
    parser.add_argument(
        "--conflict-limit", type=int, default=128,
        help="Maximum exact Kuratowski certificates retained.",
    )
    parser.add_argument(
        "--no-batch",
        action="store_true",
        help="Disable v0.8.1 compiled batch screening and use serial candidate tests.",
    )
    parser.add_argument(
        "--legacy-partial-builder",
        action="store_true",
        help=(
            "Rebuild the conservative partial graph from scratch as v0.3 did, "
            "instead of maintaining the mathematically identical graph incrementally."
        ),
    )
    parser.add_argument(
        "--no-c6",
        action="store_true",
        help="Disable the published C6 crossing-order pruning rule.",
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help=(
            "Enable expensive state/coverage assertions; with incremental partial "
            "graphs this also rebuilds the legacy v0.3 graph and compares them."
        ),
    )
    parser.add_argument(
        "--cache",
        action="store_true",
        help=(
            "Enable the legacy failed-state cache only with --no-screening. "
            "v0.8.1 lookahead uses exact one-step screen reuse instead."
        ),
    )
    parser.add_argument(
        "--planarity-backend",
        choices=["auto", "boost", "networkx"],
        default="auto",
        help="Planarity oracle: auto prefers compiled Boost and falls back to NetworkX.",
    )
    parser.add_argument(
        "--no-locked-prefix",
        action="store_true",
        help="Disable the stronger v0.8 locked-prefix minor pruning (verification only).",
    )
    parser.add_argument(
        "--activation-order",
        choices=["optimized", "euler"],
        default="optimized",
        help="Original-edge activation order; this changes traversal only.",
    )
    parser.add_argument(
        "--unlimited",
        action="store_true",
        help="Disable both time and recursive-call limits. Use cautiously on large dumbbells.",
    )


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Fulek–Pach thrackle reconstruction v0.15.0"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser(
        "self-test",
        help=(
            "Run exhaustive-baseline, v0.3-compatibility, incremental-graph, "
            "screening, lookahead, C6, and exact-coverage verification tests."
        ),
    )

    sub.add_parser(
        "blast-test-v011",
        help="Run retained v0.11 whole-stage/batch/certificate safety regressions.",
    )
    sub.add_parser(
        "blast-test-v012",
        help="Run v0.12 direct-encoder and endpoint-hoisting safety regressions.",
    )
    sub.add_parser(
        "release-audit-v012",
        help=(
            "Run the v0.12 release verification ladder in isolated subprocesses "
            "so heavy differential tests cannot perturb later exact regressions."
        ),
    )

    sub.add_parser(
        "blast-test-v013",
        help="Run v0.13 C8-language and reflection-quotient safety regressions.",
    )
    sub.add_parser(
        "release-audit-v013",
        help="Run the complete retained v0.13 verification ladder in isolated subprocesses.",
    )
    sub.add_parser(
        "blast-test-v014",
        help="Run v0.14 incremental-C8, slot-bundling, pair-root, and overflow safety regressions.",
    )
    sub.add_parser(
        "release-audit-v014",
        help="Run the complete v0.14 verification ladder in isolated subprocesses.",
    )

    sub.add_parser(
        "blast-test-v015",
        help="Run v0.15 H2/H5 support and support-driven generation safety regressions.",
    )
    audit15 = sub.add_parser(
        "release-audit-v015",
        help="Run the complete v0.15 verification ladder in isolated subprocesses.",
    )
    audit15.add_argument("--full-h2-cert", action="store_true", help="Also regenerate all 2,544 H2 parent languages and require exact frozen-data equality (slow but proof-grade).")
    audit15.add_argument("--processes", type=int, default=None, help="Worker count for --full-h2-cert.")
    cert15 = sub.add_parser(
        "certify-v015-h2-language",
        help="Fully regenerate the v0.15 H2 language and compare it byte-for-byte with the frozen release data.",
    )
    cert15.add_argument("--processes", type=int, default=None)
    cert15.add_argument("--planarity-backend", choices=["boost", "networkx"], default="boost")

    cyc = sub.add_parser("search-cycle", help="Run v0.15.0 on C_n.")
    cyc.add_argument("n", type=int)
    _add_common_search_args(cyc, max_calls=10000000, time_limit=600.0)

    db = sub.add_parser("search-db", help="Run v0.15.0 on DB(c1,c2,l).")
    db.add_argument("c1", type=int)
    db.add_argument("c2", type=int)
    db.add_argument("l", type=int)
    _add_common_search_args(db, max_calls=10000000, time_limit=600.0)

    core = sub.add_parser(
        "search-db682-cores",
        help="Exact v0.15 H2/H5-supported, incremental-C8/reflection-quotiented search specialized to DB(6,8,-2).",
    )
    core.add_argument("--processes", type=int, default=None)
    core.add_argument("--time-limit-per-core", type=float, default=None)
    core.add_argument("--max-calls-per-core", type=int, default=None)
    core.add_argument("--planarity-backend", choices=["auto", "boost", "networkx"], default="auto")
    core.add_argument("--no-superdomain", action="store_true", help="Disable exact completed-restriction superdomain pruning (verification/reference only).")
    core.add_argument("--no-whole-stage", action="store_true", help="Disable exact q6/q11 whole-stage DEAD certificates (verification/reference only).")
    core.add_argument("--no-endpoint-hoist", action="store_true", help="Disable v0.12 early q7->q6 and q10->q11 exact certificates (verification/reference only).")
    core.add_argument("--no-direct-pi-encoder", action="store_true", help="Disable v0.12 direct compiled complete-Pi encoder and use the v0.11 NetworkX construction path.")
    core.add_argument("--no-c8-language", action="store_true", help="Disable v0.13 exhaustive C8-language extension pruning (verification/reference only).")
    core.add_argument("--no-v014-precomputed-c8-rows", action="store_true", help="Disable v0.14 precomputed exact C8 row masks and use the v0.13 first-use literal scans.")
    core.add_argument("--no-v014-incremental-c8", action="store_true", help="Disable v0.14 exact incremental C8 mask propagation and recompute support as v0.13 did.")
    core.add_argument("--no-v014-sensitive-slots", action="store_true", help="Disable v0.14 early C8-sensitive C6-host slot bundling (verification/reference only).")
    core.add_argument("--no-v015-h2", action="store_true", help="Disable v0.15 exact H2=C8+e2 language support (verification/reference only).")
    core.add_argument("--no-v015-h5", action="store_true", help="Disable v0.15 exact reflected H5=C8+e5 language support (verification/reference only).")
    core.add_argument("--no-v015-support-driven-slots", action="store_true", help="Disable v0.15 support-driven sensitive-slot prefix generation and enumerate full sensitive tuples as v0.14 did.")
    core.add_argument("--no-automorphism-quotient", action="store_true", help="Disable v0.13 exact reflection quotient and search all eight planar C6 cores.")
    core.add_argument("--kuratowski-learning", action="store_true", help="Opt in to literal Kuratowski-certificate learning (off by default in v0.12 because it is slower on the target).")
    core.add_argument("--no-kuratowski-learning", action="store_true", help="Backward-compatible explicit disable; v0.12 already defaults to off.")
    core.add_argument("--exact-iso-cache", action="store_true", help="Enable exact-isomorphism planarity reuse. Hashes are lookup buckets only; every hit is verified by exact isomorphism.")
    core.add_argument("--report", type=str, default=None)
    core.add_argument("--progress", type=float, default=2.0, help="Refresh the live core/orbit dashboard every N seconds; 0 disables it.")
    core.add_argument("--progress-mode", choices=["auto", "single", "line", "dashboard"], default="auto", help="single refreshes one v0.6.1.1-style dashboard in place; line prints each refresh below the last.")
    core.add_argument("--quiet", action="store_true")

    inspect = sub.add_parser(
        "inspect-db",
        help="Show graph size, Euler data, exact Pi count, and detected 6-cycles.",
    )
    inspect.add_argument("c1", type=int)
    inspect.add_argument("c2", type=int)
    inspect.add_argument("l", type=int)

    args = parser.parse_args()

    if args.command == "self-test":
        rows, dumbbell_results = self_test()
        for row in rows:
            print(
                f"{row['graph']}: baseline={row['baseline_found']} | "
                f"v03-compat={row['v03_compat_status']} "
                f"({row['v03_compat_calls']:,} calls, {row['v03_compat_tests']:,} tests) | "
                f"screening={row['screening_status']} | "
                f"lookahead={row['lookahead_status']} | "
                f"optimized={row['optimized_status']} "
                f"({row['optimized_calls']:,} calls, {row['optimized_tests']:,} tests, "
                f"C6 prunes={row['optimized_c6_prunes']:,}, "
                f"{row['optimized_time']:.4f}s)"
            )
        for pars, result in dumbbell_results:
            print(
                f"DB{pars}: {result.status}, coverage="
                f"{coverage_percent_string(result.stats.resolved_candidates, result.stats.total_candidates, precision=18)}"
            )
        print("\nAll retained self-tests passed under v0.15.0.")
        return

    if args.command == "blast-test-v011":
        _v011_safety_regressions()
        print("All retained v0.11 target-specific blast regressions passed under v0.15.0.")
        return

    if args.command == "blast-test-v012":
        # Keep this target-specific suite in its own process.  Earlier release
        # testing found that running a large unrelated graph differential first
        # could leave allocator/cache state that made this exact endpoint suite
        # needlessly slow.  Isolation changes no search semantics; it makes the
        # verification command reproducible.
        _v012_safety_regressions()
        print("All retained v0.12.0 endpoint/direct-encoder blast regressions passed under v0.15.0.")
        return

    if args.command == "release-audit-v012":
        script = os.path.abspath(__file__)
        commands = [
            [sys.executable, script, "self-test"],
            [sys.executable, script, "blast-test-v011"],
            [sys.executable, script, "blast-test-v012"],
        ]
        for cmd in commands:
            print("\n[release audit]", " ".join(cmd), flush=True)
            subprocess.run(cmd, check=True)
        print("\nAll isolated v0.12.0 release-audit stages passed.")
        return

    if args.command == "blast-test-v013":
        _v013_safety_regressions()
        print("All retained v0.13 C8-language/reflection safety regressions passed under v0.15.0.")
        return

    if args.command == "release-audit-v013":
        script = os.path.abspath(__file__)
        commands = [
            [sys.executable, script, "self-test"],
            [sys.executable, script, "blast-test-v011"],
            [sys.executable, script, "blast-test-v012"],
            [sys.executable, script, "blast-test-v013"],
        ]
        for cmd in commands:
            print("\n[v0.13 retained audit]", " ".join(cmd), flush=True)
            subprocess.run(cmd, check=True)
        print("\nAll retained v0.13 verification stages passed under v0.15.0.")
        return

    if args.command == "blast-test-v014":
        _v014_safety_regressions()
        print("All v0.14.0 incremental-C8/slot-bundling safety regressions passed.")
        return

    if args.command == "release-audit-v014":
        script = os.path.abspath(__file__)
        commands = [
            [sys.executable, script, "self-test"],
            [sys.executable, script, "blast-test-v011"],
            [sys.executable, script, "blast-test-v012"],
            [sys.executable, script, "blast-test-v013"],
            [sys.executable, script, "blast-test-v014"],
        ]
        for cmd in commands:
            print("\n[v0.14 release audit]", " ".join(cmd), flush=True)
            subprocess.run(cmd, check=True)
        print("\nAll isolated v0.14.0 release-audit stages passed.")
        return

    if args.command == "blast-test-v015":
        _v015_safety_regressions()
        print("All v0.15.0 H2/H5/support-driven safety regressions passed.")
        return

    if args.command == "certify-v015-h2-language":
        rep = _v015_certify_frozen_h2_full(
            processes=args.processes, planarity=args.planarity_backend
        )
        print(
            "v0.15 full H2 language certificate PASSED: "
            f"records={rep['records']:,}, sha256={rep['sha256']}, "
            f"nodes={rep['nodes']:,}, tests={rep['planarity_tests']:,}, "
            f"seconds={rep['seconds']:.2f}"
        )
        return

    if args.command == "release-audit-v015":
        script = os.path.abspath(__file__)
        commands = [
            [sys.executable, script, "self-test"],
            [sys.executable, script, "blast-test-v011"],
            [sys.executable, script, "blast-test-v012"],
            [sys.executable, script, "blast-test-v013"],
            [sys.executable, script, "blast-test-v014"],
            [sys.executable, script, "blast-test-v015"],
        ]
        for cmd in commands:
            print("\n[v0.15 release audit]", " ".join(cmd), flush=True)
            subprocess.run(cmd, check=True)
        if args.full_h2_cert:
            cmd = [sys.executable, script, "certify-v015-h2-language", "--planarity-backend", "boost"]
            if args.processes is not None:
                cmd.extend(["--processes", str(args.processes)])
            print("\n[v0.15 release audit]", " ".join(cmd), flush=True)
            subprocess.run(cmd, check=True)
        print("\nAll isolated v0.15.0 release-audit stages passed.")
        return

    if args.command == "search-db682-cores":
        run_db682_cores(
            processes=args.processes,
            time_limit_per_core=args.time_limit_per_core,
            max_calls_per_core=args.max_calls_per_core,
            planarity=args.planarity_backend,
            use_superdomain=not args.no_superdomain,
            use_whole_stage=not args.no_whole_stage,
            use_endpoint_hoisting=not args.no_endpoint_hoist,
            use_direct_pi_encoder=not args.no_direct_pi_encoder,
            use_c8_language=not args.no_c8_language,
            use_v014_precomputed_c8_rows=not args.no_v014_precomputed_c8_rows,
            use_v014_incremental_c8=not args.no_v014_incremental_c8,
            use_v014_c8_sensitive_slots=not args.no_v014_sensitive_slots,
            use_v015_h2_language=not args.no_v015_h2,
            use_v015_h5_language=not args.no_v015_h5,
            use_v015_support_driven_slots=not args.no_v015_support_driven_slots,
            use_automorphism_quotient=not args.no_automorphism_quotient,
            use_kuratowski_learning=bool(args.kuratowski_learning and not args.no_kuratowski_learning),
            use_exact_iso_cache=args.exact_iso_cache,
            report=args.report,
            verbose=not args.quiet,
            progress=None if args.quiet else args.progress,
            progress_mode=args.progress_mode,
        )
        return

    if args.command == "inspect-db":
        G = dumbbell(args.c1, args.c2, args.l)
        search = BacktrackingSearch(
            G,
            use_c6_restriction=True,
            progress_interval_seconds=None,
            graph_label=f"DB({args.c1},{args.c2},{args.l})",
        )
        print(
            f"DB({args.c1},{args.c2},{args.l}) has "
            f"{G.graph.number_of_nodes()} vertices and {len(G.edges)} edges."
        )
        print(f"Required proper crossings: {G.total_required_crossings()}")
        print(f"Euler edge order: {search.order}")
        print("Euler orientations:")
        for eid in search.order:
            print(f"  {eid}: {search.oriented[eid][0]} -> {search.oriented[eid][1]}")
        print(f"Naive complete-Pi systems: {search.total_candidates:,}")
        print(f"Detected simple C6 cycles: {len(search.six_cycles)}")
        for c in search.six_cycles:
            print(f"  C6 #{c.id}: edges={list(c.edges)}, vertices={list(c.vertices)}")
        return

    if args.command == "search-cycle":
        G = cycle_graph(args.n)
        label = f"C{args.n}"
    else:
        G = dumbbell(args.c1, args.c2, args.l)
        label = f"DB({args.c1},{args.c2},{args.l})"

    progress = None if args.progress <= 0 else args.progress
    search = BacktrackingSearch(
        G,
        max_recursive_calls=None if args.unlimited else args.max_calls,
        time_limit_seconds=None if args.unlimited else args.time_limit,
        use_c6_restriction=not args.no_c6,
        branch_order=args.branch_order,
        use_screening=not args.no_screening,
        use_lookahead=(not args.no_lookahead) and (not args.no_screening),
        incremental_partial=not args.legacy_partial_builder,
        debug=args.debug,
        use_cache=args.cache,
        use_batch_screening=not args.no_batch,
        planarity_workers=args.workers,
        use_kuratowski_cache=args.conflicts,
        kuratowski_cache_limit=args.conflict_limit,
        progress_interval_seconds=progress,
        progress_mode=args.progress_mode,
        graph_label=label,
        planarity_backend=args.planarity_backend,
        activation_order=args.activation_order,
        use_locked_prefix_pruning=not args.no_locked_prefix,
    )
    print(
        f"Starting {label}: {G.graph.number_of_nodes()} vertices, "
        f"{len(G.edges)} edges, {search.total_required_crossings} required crossings, "
        f"{search.total_candidates:,} complete Pi systems, "
        f"C6 cycles active={len(search.six_cycles)}, "
        f"screening={search.use_screening}, lookahead={search.use_lookahead}, "
        f"incremental-partial={search.incremental_partial}, "
        f"planarity={search.planarity.name}, workers={search.planarity_workers}, "
        f"exact-conflicts={search.use_kuratowski_cache}."
    )
    result = search.run()
    print_result(result)

    if args.report:
        write_json_report(args.report, label, G, search, result)
        print(f"Wrote report: {args.report}")


if __name__ == "__main__":
    main()
