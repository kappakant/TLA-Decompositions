--------------------------- MODULE msgs_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

VARIABLES Fluent6_0, msgs, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0, Fluent24_0, Fluent23_0

vars == <<Fluent6_0, msgs, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0, Fluent24_0, Fluent23_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent23_0[var1]) => (~(Fluent24_0[var0]))

Init ==
/\ msgs = {}
/\ tmPrepared = {}
/\ Fluent24_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent23_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ Fluent23_0' = [Fluent23_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent24_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs,tmPrepared>>
/\ UNCHANGED<<Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent10_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ Fluent24_0' = [Fluent24_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs,tmPrepared>>
/\ UNCHANGED<<Fluent24_0, Fluent23_0>>
/\ CandSep'
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent11_0, Fluent10_0>>
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
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent24_0 \in [RMs -> BOOLEAN]
/\ Fluent23_0 \in [RMs -> BOOLEAN]
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent7_0  \in [RMs -> BOOLEAN]
/\ Fluent11_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0 \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent24_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent23_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent11_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Safety ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent11_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))

\* added by endive
Inv403_1_0_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(Fluent6_0[rmi]))
Inv253_1_1_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent24_0[rmj]) \/ (~([type |-> "Abort"] \in msgs))
Inv195_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent23_0[rmj]) \/ (~([type |-> "Commit"] \in msgs))
Inv30_1_1_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent10_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv251_1_0_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent24_0[rmj]) \/ (~(Fluent7_0[rmi]))
Inv399_1_1_def == \A rmi \in RMs : \E rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(Fluent23_0[rmi]))
Inv34_1_2_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent10_0[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv31_1_3_def == \A rmi \in RMs : \E rmj \in RMs : (Fluent10_0[rmi]) \/ (~([type |-> "Prepared", theRM |-> rmi] \in msgs))

\* The inductive invariant candidate.
IndAuto ==
/\ Safety
/\ Inv403_1_0_def
/\ Inv253_1_1_def
/\ Inv195_1_0_def
/\ Inv30_1_1_def
/\ Inv251_1_0_def
/\ Inv399_1_1_def
/\ Inv34_1_2_def
/\ Inv31_1_3_def

=============================================================================
