--------------------------- MODULE tmState_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

VARIABLES tmState, Fluent7_0, Fluent20_0, Fluent22_0, Fluent11_0, Fluent21_0, Fluent10_0, Fluent23_0

vars == <<tmState, Fluent7_0, Fluent20_0, Fluent22_0, Fluent11_0, Fluent21_0, Fluent10_0, Fluent23_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent23_0[var0]) => (~(Fluent22_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (~(Fluent21_0[var0]))

Init ==
/\ tmState = "init"
/\ Fluent20_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent22_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent21_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent23_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 =  [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ UNCHANGED tmState
/\ Fluent22_0' = [x0 \in RMs |-> TRUE]
/\ Fluent21_0' = [Fluent21_0 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent20_0, Fluent23_0>>
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ Fluent22_0' = [Fluent22_0 EXCEPT ![rm] = FALSE]
/\ Fluent21_0' = [x0 \in RMs |-> TRUE]
/\ Fluent23_0' = [Fluent23_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent20_0>>
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ Fluent20_0' = [Fluent20_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent22_0, Fluent21_0, Fluent23_0>>
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ Fluent7_0  \in [RMs -> BOOLEAN] 
/\ Fluent20_0 \in [RMs -> BOOLEAN]
/\ Fluent22_0 \in [RMs -> BOOLEAN]
/\ Fluent11_0 \in [RMs -> BOOLEAN]
/\ Fluent21_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0 \in [RMs -> BOOLEAN]
/\ Fluent23_0 \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (tmState \in RandomSubset(NumRandElems, {"init","committed","aborted"}))
/\ Fluent7_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN]) 
/\ Fluent20_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent22_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent11_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent21_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent23_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive
Inv382_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(Fluent21_0[rmi]))
Inv197_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent21_0[rmi]) \/ (~(Fluent23_0[rmj]))
Inv363_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~(Fluent20_0[rmi]))

IndAuto ==
/\ CandSep
/\ Inv382_1_0_def
/\ Inv197_1_1_def
/\ Inv363_1_0_def

IISpec == TypeOK /\ IndAuto /\ [][Next]_vars
=============================================================================
