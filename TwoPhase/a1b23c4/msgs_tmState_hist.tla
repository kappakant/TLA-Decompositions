--------------------------- MODULE msgs_tmState_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (6)
VARIABLES msgs, tmState, Fluent17_0, Fluent18_0, Fluent7_0, Fluent11_0, Fluent10_0

vars == <<msgs, tmState, Fluent17_0, Fluent18_0, Fluent7_0, Fluent11_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent17_0[var0]) => (Fluent18_0[var1])

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent18_0, Fluent17_0>>
/\ CandSep'
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent11_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ UNCHANGED tmState
/\ UNCHANGED msgs
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent17_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent18_0, Fluent17_0>>
/\ CandSep'
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent10_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED<<Fluent18_0, Fluent17_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent18_0, Fluent17_0>>
/\ CandSep'
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11_0, Fluent10_0>>
/\ CandSep'

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
/\ Fluent17_0 \in [RMs -> BOOLEAN]
/\ Fluent18_0 \in [RMs -> BOOLEAN]
/\ Fluent7_0  \in [RMs -> BOOLEAN]
/\ Fluent11_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0 \in [RMs -> BOOLEAN]

Safety ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent11_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent11_0[var0]))

NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems, {"init","committed","aborted"}))
/\ Fluent17_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent18_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent11_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive
Inv369_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgs))
Inv387_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~([type |-> "Commit"] \in msgs))
Inv450_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent11_0[rmi]) \/ (~(tmState = "aborted"))
Inv30_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~(tmState = "committed"))
Inv306_1_0_def == \A rmi \in RMs : \A rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(Fluent17_0[rmi]))
Inv367_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~(Fluent7_0[rmi]))
Inv452_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent11_0[rmi]) \/ (~(tmState = "init"))
Inv21_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~(Fluent18_0[rmi]))
Inv27_1_4_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent10_0[rmi]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))

\* The inductive invariant candidate.
IndAuto ==
/\ Safety
/\ Inv369_1_0_def
/\ Inv387_1_1_def
/\ Inv450_1_2_def
/\ Inv30_1_3_def
/\ Inv306_1_0_def
/\ Inv367_1_1_def
/\ Inv452_1_2_def
/\ Inv21_1_3_def
/\ Inv27_1_4_def

=============================================================================
