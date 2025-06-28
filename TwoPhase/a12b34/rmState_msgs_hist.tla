--------------------------- MODULE rmState_msgs_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned several fluents (13, 6, 9)
VARIABLES msgs, Fluent5_0, Fluent19_0, Fluent8_0, rmState, Fluent20_0, Fluent12_0

vars == <<msgs, Fluent5_0, Fluent19_0, Fluent8_0, rmState, Fluent20_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent20_0[var1]) => (Fluent5_0[var0])
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (~(Fluent8_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (~(Fluent12_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (Fluent19_0[var0])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent20_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent20_0, Fluent12_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent20_0, Fluent12_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ UNCHANGED rmState
/\ Fluent20_0' = [Fluent20_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent12_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent20_0, Fluent12_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED rmState
/\ Fluent19_0' = [[x0 \in RMs |-> FALSE] EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = FALSE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent20_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent20_0, Fluent12_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent8_0, Fluent20_0, Fluent12_0>>
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
/\ Fluent5_0 \in  [RMs -> BOOLEAN]
/\ Fluent19_0 \in [RMs -> BOOLEAN]
/\ Fluent8_0 \in  [RMs -> BOOLEAN]
/\ Fluent20_0 \in [RMs -> BOOLEAN]
/\ Fluent12_0 \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (rmState \in RandomSubset(NumRandElems, [RMs -> {"working","prepared","committed","aborted"}]))
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ Fluent5_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent19_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent8_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent20_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent12_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

\* Added by endive
Inv331_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent8_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv335_1_1_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent8_0[rmi]) \/ (~(rmState[rmi] = "committed"))
Inv325_1_2_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent8_0[rmi]) \/ (~(Fluent20_0[rmi]))
Inv453_1_0_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(Fluent5_0[rmi]))
Inv431_1_1_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "committed"))
Inv324_1_2_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent8_0[rmi]) \/ (~(Fluent19_0[rmj]))
Inv71_1_3_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmj]) \/ (~([type |-> "Abort"] \in msgs))
Inv814_1_4_def == \A rmi \in RMs : \E rmj \in RMs : ~(Fluent5_0[rmi]) \/ (~(rmState[rmi] = "working"))
Inv421_1_5_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(Fluent20_0[rmi]))
Inv386_1_6_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Abort"] \in msgs) \/ (~(Fluent12_0[rmi]))
Inv146_1_7_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent19_0[rmj]) \/ (~(Fluent5_0[rmi]))
Inv144_2_8_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmi]) \/ ((Fluent8_0[rmi])) \/ (~(Fluent5_0[rmi]))
Inv471_2_9_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmi]) \/ (~([type |-> "Abort"] \in msgs)) \/ (~(Fluent19_0[rmi]))
Inv262_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent5_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv883_1_1_def == \A rmi \in RMs : \E rmj \in RMs : ~([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(rmState[rmi] = "working"))
Inv112_1_2_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent19_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv763_1_3_def == \A rmi \in RMs : \E rmj \in RMs : ~(Fluent19_0[rmj]) \/ (~(rmState[rmi] = "aborted"))
Inv294_1_4_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent5_0[rmj]) \/ (~(Fluent8_0[rmi]))
Inv226_1_5_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent20_0[rmj]) \/ (~([type |-> "Commit"] \in msgs))
Inv1092_2_6_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmj]) \/ (~(rmState[rmi] = "aborted")) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))
Inv255_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent5_0[rmi]) \/ (~(Fluent19_0[rmj]))
Inv932_2_1_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmj]) \/ (~(Fluent19_0[rmi])) \/ ((Fluent5_0[rmi]))
Inv597_2_2_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent12_0[rmj]) \/ ((Fluent19_0[rmi]) \/ (~(Fluent5_0[rmi])))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv331_1_0_def
/\ Inv335_1_1_def
/\ Inv325_1_2_def
/\ Inv453_1_0_def
/\ Inv431_1_1_def
/\ Inv324_1_2_def
/\ Inv71_1_3_def
/\ Inv814_1_4_def
/\ Inv421_1_5_def
/\ Inv386_1_6_def
/\ Inv146_1_7_def
/\ Inv144_2_8_def
/\ Inv471_2_9_def
/\ Inv262_1_0_def
/\ Inv883_1_1_def
/\ Inv112_1_2_def
/\ Inv763_1_3_def
/\ Inv294_1_4_def
/\ Inv226_1_5_def
/\ Inv1092_2_6_def
/\ Inv255_1_0_def
/\ Inv932_2_1_def
/\ Inv597_2_2_def
=============================================================================
