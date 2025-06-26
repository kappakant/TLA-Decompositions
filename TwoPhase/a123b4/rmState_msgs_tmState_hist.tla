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

NumRandElems == 5
TypeOKRand ==
/\ (rmState \in RandomSubset(NumRandElems, [RMs -> {"working","prepared","committed","aborted"}]))
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems, {"init", "committed", "aborted"}))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
