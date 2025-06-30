--------------------------- MODULE tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (6)
VARIABLES Fluent17_0, Fluent18_0, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0

vars == <<Fluent17_0, Fluent18_0, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent17_0[var0]) => (Fluent18_0[var1])

Init ==
/\ tmPrepared = {}
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent17_0>>
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>

SndCommit(rm) ==
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0>>
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK == 
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent17_0 \in [RMs -> BOOLEAN]
/\ Fluent18_0 \in [RMs -> BOOLEAN]
/\ Fluent7_0  \in [RMs -> BOOLEAN]
/\ Fluent11_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0 \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent17_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent18_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent11_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive
Inv145_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent18_0[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))

The inductive invariant candidate.
IndAuto ==
/\ CandSep
/\ Inv145_1_0_def
=============================================================================
