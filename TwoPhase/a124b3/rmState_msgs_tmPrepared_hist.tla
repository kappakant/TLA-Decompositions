--------------------------- MODULE rmState_msgs_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

VARIABLES msgs, Fluent14_0, tmPrepared, rmState, Fluent13_0

vars == <<msgs, Fluent14_0, tmPrepared, rmState, Fluent13_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent13_0[var1]) => (~(Fluent14_0[var0]))

Init ==
/\ tmPrepared = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent13_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
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
/\ (tmPrepared \in SUBSET(RMs))

NumRandElems == 5
TypeOKRand ==
/\ (rmState \in RandomSubset(4, [RMs -> {"working","prepared","committed","aborted"}]))
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent13_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent14_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

Inv191_1_0_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "committed"))
Inv123_1_1_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent14_0[rmj]) \/ (~([type |-> "Abort"] \in msgs))
Inv57_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent13_0[rmj]) \/ (~([type |-> "Commit"] \in msgs))
Inv458_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (tmPrepared = RMs) \/ (~(Fluent13_0[rmi]))
Inv595_1_1_def == \A rmi \in RMs : \E rmj \in RMs : ~([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "aborted"))
Inv660_1_2_def == \A rmi \in RMs : \E rmj \in RMs : ~(rmState[rmi] = "working") \/ (~(tmPrepared = RMs))
Inv610_1_0_def == \A rmi \in RMs : \E rmj \in RMs : ~([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(rmState[rmi] = "working"))
Inv661_1_1_def == \A rmi \in RMs : \E rmj \in RMs : ~(rmState[rmi] = "working") \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv183_1_2_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(Fluent13_0[rmi]))
Inv1924_2_3_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent14_0[rmj]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(rmState[rmi] = "aborted")))
Inv229_1_0_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(tmPrepared = tmPrepared \cup {rmi}))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv191_1_0_def
/\ Inv123_1_1_def
/\ Inv57_1_0_def
/\ Inv458_1_0_def
/\ Inv595_1_1_def
/\ Inv660_1_2_def
/\ Inv610_1_0_def
/\ Inv661_1_1_def
/\ Inv183_1_2_def
/\ Inv1924_2_3_def
/\ Inv229_1_0_def

=============================================================================
