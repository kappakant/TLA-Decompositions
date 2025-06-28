--------------------------- MODULE rmState_msgs_tmState_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

VARIABLES Fluent6_0, msgs, tmState, Fluent7_0, rmState

vars == <<Fluent6_0, msgs, tmState, Fluent7_0, rmState>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var0]) => (Fluent6_0[var1])

Init ==
/\ tmState = "init"
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState>>
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ UNCHANGED tmState
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ UNCHANGED rmState
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED rmState
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SndAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (msgs \in SUBSET(Message))
/\ (tmState \in {"init","committed","aborted"})
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent7_0 \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (rmState \in RandomSubset(NumRandElems, [RMs -> {"working","prepared","committed","aborted"}]))
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems, {"init", "committed", "aborted"}))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

\* added by endive
Inv462_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgs))
Inv482_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~([type |-> "Commit"] \in msgs))
Inv645_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~(rmState[rmi] = "committed") \/ (~(tmState = "aborted"))
Inv34_1_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent6_0[rmi]) \/ (~(tmState = "committed"))
Inv523_1_4_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent6_0[rmi]) \/ (~(rmState[rmi] = "working"))
Inv637_1_5_def == \A rmi \in RMs : \A rmj \in RMs : ~(rmState[rmi] = "aborted") \/ (~(tmState = "committed"))
Inv213_1_0_def == \A rmi \in RMs : \A rmj \in RMs : ([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(Fluent6_0[rmi]))
Inv647_1_1_def == \A rmi \in RMs : \A rmj \in RMs : ~(rmState[rmi] = "committed") \/ (~(tmState = "init"))
Inv610_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(rmState[rmi] = "working"))
Inv563_1_3_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent7_0[rmi]) \/ (~(tmState = "init"))
Inv4321_2_4_def == \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "prepared") \/ (~(tmState = "init")) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv462_1_0_def
/\ Inv482_1_1_def
/\ Inv645_1_2_def
/\ Inv34_1_3_def
/\ Inv523_1_4_def
/\ Inv637_1_5_def
/\ Inv213_1_0_def
/\ Inv647_1_1_def
/\ Inv610_1_2_def
/\ Inv563_1_3_def
/\ Inv4321_2_4_def

IISpec == TypeOK /\ IndAuto /\ [][Next]_vars
=============================================================================
