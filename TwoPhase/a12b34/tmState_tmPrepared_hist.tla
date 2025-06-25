--------------------------- MODULE tmState_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned several fluents (13, 6, 9)
VARIABLES Fluent5_0, tmState, Fluent19_0, tmPrepared, Fluent8_0, Fluent20_0, Fluent12_0

vars == <<Fluent5_0, tmState, Fluent19_0, tmPrepared, Fluent8_0, Fluent20_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent20_0[var1]) => (Fluent5_0[var0])
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (~(Fluent8_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (~(Fluent12_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (Fluent19_0[var0])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent20_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent20_0, Fluent12_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent20_0' = [Fluent20_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent12_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED tmPrepared
/\ Fluent19_0' = [[x0 \in RMs |-> FALSE] EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = FALSE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent20_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent5_0 \in  [RMs -> BOOLEAN]
/\ Fluent19_0 \in [RMs -> BOOLEAN]
/\ Fluent8_0 \in  [RMs -> BOOLEAN]
/\ Fluent20_0 \in [RMs -> BOOLEAN]
/\ Fluent12_0 \in [RMs -> BOOLEAN]


NumRandElems == 5
TypeOKRand ==
/\ (tmState \in RandomSubset(NumRandElems, {"init", "committed", "aborted"}))
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent5_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent19_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent8_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent20_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent12_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Inv314_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~(Fluent12_0[rmi]))
Inv184_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent5_0[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv223_1_2_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent8_0[rmi]) \/ (~(Fluent20_0[rmi]))
Inv285_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (tmPrepared = tmPrepared \cup {rmi}) \/ (~(Fluent5_0[rmi]))
Inv232_1_4_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent8_0[rmi]) \/ (~(tmState = "committed"))
Inv312_2_5_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent12_0[rmi]) \/ (~(Fluent5_0[rmj])) \/ ((Fluent8_0[rmi]))
Inv334_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(Fluent20_0[rmi]))
Inv112_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent19_0[rmj]) \/ (~(tmState = "committed"))
Inv1047_2_2_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent19_0[rmi]) \/ (~(Fluent5_0[rmi]) \/ (~(tmState = "init")))

\* The inductive invariant candidate.
IndAuto ==
/\ CandSep
/\ Inv314_1_0_def /\ Inv184_1_1_def /\ Inv223_1_2_def
/\ Inv285_1_3_def
/\ Inv232_1_4_def
/\ Inv312_2_5_def
/\ Inv334_1_0_def
/\ Inv112_1_1_def
/\ Inv1047_2_2_def

IndRand ==
/\ TypeOKRand
/\ IndAuto

IISpec == IndRand /\ [][Next]_vars

=============================================================================
