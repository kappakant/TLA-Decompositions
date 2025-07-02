Inv91_1_0_def == \E rmi \in RMs : \A rmj \in RMs : (Fluent7_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv462_1_1_def == \E rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgs))
Inv99_1_2_def == \E rmi \in RMs : \A rmj \in RMs : (Fluent7_0[rmi]) \/ (~(rmState[rmj] = "committed"))
Inv480_1_0_def == \E rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(Fluent7_0[rmj]))
Inv243_1_1_def == \E rmi \in RMs : \A rmj \in RMs : ([type |-> "Prepared", theRM |-> rmj] \in msgs) \/ (~(Fluent6_0[rmj]))
Inv625_1_2_def == \E rmi \in RMs : \A rmj \in RMs : ~([type |-> "Prepared", theRM |-> rmj] \in msgs) \/ (~(rmState[rmj] = "working"))
Inv667_1_3_def == \E rmi \in RMs : \A rmj \in RMs : ~(rmState[rmj] = "aborted") \/ (~(tmState = "committed"))
Inv5137_2_4_def == \E rmi \in RMs : \A rmj \in RMs : (rmState[rmj] = "prepared") \/ (~([type |-> "Prepared", theRM |-> rmj] \in msgs)) \/ (~(tmState = "init"))
Inv103_1_0_def == \E rmi \in RMs : \A rmj \in RMs : (Fluent7_0[rmi]) \/ (~(tmState = "committed"))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv91_1_0_def
/\ Inv462_1_1_def
/\ Inv99_1_2_def
/\ Inv480_1_0_def
/\ Inv243_1_1_def
/\ Inv625_1_2_def
/\ Inv667_1_3_def
/\ Inv5137_2_4_def
/\ Inv103_1_0_def
----------------------------------------
Initial random seed: 20
opt_quant_minimize: 0
Total number of CTIs eliminated: 1006
Total number of invariants generated: 88
Total number of invariants checked: 7334
CTI generation duration: 28.712359 secs.
Invariant checking duration: 7.589005 secs.
CTI elimination checks duration: 42.257350 secs.
Total duration: 78.67 secs.
python3 /Users/johnnguyen/Desktop/TLA/endive/endive.py --seed 20 --ninvs 1500  338.47s user 22.25s system 457% cpu 1:18.77 total


Mini paper about TwoPhase, talking about inductive invariant thought processes. Complete by July 11th
Good practice for the presentation on the 22nd, also first draft presentation on July 15
Also think of an outline for it on July 11th


Consider dumping the proof and try to get a TLAPS proof from ChatGPT.

Apparently adding hyperproperties in Alloy 7.
