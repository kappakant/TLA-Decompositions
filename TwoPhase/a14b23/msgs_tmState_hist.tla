--------------------------- MODULE msgs_tmState_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (18)
VARIABLES Fluent6_0, msgs, Fluent5_0, tmState, Fluent4_0, Fluent17_0, Fluent3_0

vars == <<Fluent6_0, msgs, Fluent5_0, tmState, Fluent4_0, Fluent17_0, Fluent3_0>>

CandSep ==
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent4_0[var0]) => (Fluent3_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent4_0[var0]) => (~(Fluent17_0[var1]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent5_0[var0])

NextUnchanged == UNCHANGED vars

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent4_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent3_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED tmState
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent4_0, Fluent17_0, Fluent3_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ UNCHANGED tmState
/\ UNCHANGED msgs
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ Fluent3_0' = [Fluent3_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent17_0, Fluent3_0>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0>>

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
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent5_0  \in [RMs -> BOOLEAN]
/\ Fluent4_0  \in [RMs -> BOOLEAN]
/\ Fluent17_0 \in [RMs -> BOOLEAN]
/\ Fluent3_0  \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems, {"init", "committed", "aborted"}))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent5_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent4_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent17_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent3_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive 
Inv304_1_0_def == \A rmi \in RMs : \E rmj \in RMs: ([type |-> "Commit"] \in msgs) \/ (~(Fluent3_0[rmi]))
Inv369_1_1_def == \A rmi \in RMs : \E rmj \in RMs: (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgs))
Inv387_1_0_def == \A rmi \in RMs : \E rmj \in RMs: (tmState = "committed") \/ (~([type |-> "Commit"] \in msgs))
Inv120_1_1_def == \A rmi \in RMs : \E rmj \in RMs: (Fluent3_0[rmj]) \/ (~(tmState = "committed"))
Inv409_1_2_def == \A rmi \in RMs : \E rmj \in RMs: ~(Fluent17_0[rmi]) \/ (~(Fluent3_0[rmi]))
Inv359_1_0_def == \A rmi \in RMs : \E rmj \in RMs: (tmState = "aborted") \/ (~(Fluent17_0[rmi]))
Inv198_1_1_def == \A rmi \in RMs : \E rmj \in RMs: (Fluent5_0[rmi]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))

\* The inductive invariant candidate.
IndAuto ==
/\ CandSep
/\ Inv304_1_0_def
/\ Inv369_1_1_def
/\ Inv387_1_0_def
/\ Inv120_1_1_def
/\ Inv409_1_2_def
/\ Inv359_1_0_def
/\ Inv198_1_1_def

=============================================================================
