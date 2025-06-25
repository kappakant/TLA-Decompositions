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

NumRandElems == 4
TypeOKRand ==
/\ (rmState \in RandomSubset(4, [RMs -> {"working","prepared","committed","aborted"}]))
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ Fluent5_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent19_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent8_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent20_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent12_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

\* Added from endive
Inv308_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent8_0[rmi]) \/ ((Fluent8_0[rmj]))
Inv0_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent12_0[rmi]) \/ ((Fluent12_0[rmj]))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv308_1_0_def
/\ Inv0_1_0_def

IndRand ==
/\ TypeOKRand
/\ IndAuto

IISpec == IndRand /\ [][Next]_vars
=============================================================================
