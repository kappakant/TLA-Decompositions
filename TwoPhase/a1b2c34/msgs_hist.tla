--------------------------- MODULE msgs_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, msgs, Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0, Fluent7_0, Fluent11_0, Fluent10_0

vars == <<Fluent6_0, msgs, Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0, Fluent7_0, Fluent11_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent17_0[var0]) => (Fluent18_0[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent28_0[var0]) => (~(Fluent29_0[var1]))

Init ==
/\ msgs = {}
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent28_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent29_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0>>
/\ CandSep'
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED msgs
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = FALSE]
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent28_0, Fluent29_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ Fluent17_0' = [x0 \in RMs |-> TRUE]
/\ Fluent28_0' = [Fluent28_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0, Fluent29_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0>>
/\ CandSep'
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent10_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ Fluent29_0' = [Fluent29_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent17_0, Fluent28_0, Fluent18_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent6_0, Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent17_0, Fluent28_0, Fluent18_0, Fluent29_0>>
/\ CandSep'
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

Safety ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent11_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))
=============================================================================
