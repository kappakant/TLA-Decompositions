--------------------------- MODULE tmState_tmPrepared_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, tmState, Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0

vars == <<Fluent6_0, tmState, Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0, tmPrepared, Fluent7_0, Fluent11_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent17_0[var0]) => (Fluent18_0[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent28_0[var0]) => (~(Fluent29_0[var1]))

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent28_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent29_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = FALSE]
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent28_0, Fluent29_0>>
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent17_0' = [x0 \in RMs |-> TRUE]
/\ Fluent28_0' = [Fluent28_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0, Fluent29_0>>
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED tmPrepared
/\ Fluent29_0' = [Fluent29_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent17_0, Fluent28_0, Fluent18_0>>
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================
