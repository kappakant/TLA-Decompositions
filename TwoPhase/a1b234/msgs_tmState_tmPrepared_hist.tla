--------------------------- MODULE msgs_tmState_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (11)
VARIABLES Fluent6_0, msgs, tmState, tmPrepared, Fluent7_0, Fluent10_0

vars == <<Fluent6_0, msgs, tmState, tmPrepared, Fluent7_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10_0, Fluent7_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent10_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent7_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0  \in [RMs -> BOOLEAN]


NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems ,{"init","committed","aborted"}))
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive
Inv320_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgs))
Inv337_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~([type |-> "Commit"] \in msgs))
Inv399_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent6_0[rmi]) \/ (~(tmState = "aborted"))
Inv28_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~(tmState = "committed"))
Inv318_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~(Fluent7_0[rmi]))
Inv401_1_1_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent6_0[rmi]) \/ (~(tmState = "init"))
Inv25_1_2_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv22_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))

\* The inductive invariant candidate.
IndAuto ==
/\ CandSep
/\ Inv320_1_0_def
/\ Inv337_1_1_def
/\ Inv399_1_2_def
/\ Inv28_1_3_def
/\ Inv318_1_0_def
/\ Inv401_1_1_def
/\ Inv25_1_2_def
/\ Inv22_1_3_def

IISpec == TypeOK /\ IndAuto /\ [][Next]_vars
=============================================================================

