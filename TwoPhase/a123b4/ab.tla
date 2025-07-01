-------------------------------- MODULE ab --------------------------------
CONSTANT RMs

VARIABLES Fluent6_0, msgs, tmState, Fluent7_0, rmState, tmPrepared

vars == <<Fluent6_0, msgs, tmState, Fluent7_0, rmState, tmPrepared>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var0]) => (Fluent6_0[var1])

a == INSTANCE rmState_msgs_tmState_hist WITH RMs <- RMs, Fluent6_0 <- Fluent6_0, msgs <- msgs, tmState <- tmState, Fluent7_0 <- Fluent7_0, rmState <- rmState
b == INSTANCE tmPrepared_hist WITH RMs <- RMs, Fluent6_0 <- Fluent6_0, Fluent7_0 <- Fluent7_0, tmPrepared <- tmPrepared

vars_ab == <<Fluent6_0, msgs, tmState, Fluent7_0, rmState, tmPrepared>>
vars_a  == <<msgs, tmState, rmState>>
vars_b  == <<tmPrepared>>

Init == a!Init /\ b!Init

SndPrepare(rm)     == a!SndPrepare(rm) /\ UNCHANGED(vars_b)
SyncRcvPrepare(rm) == a!RcvPrepare(rm) /\ b!RcvPrepare(rm)
SyncSndCommit(rm)  == a!SndCommit(rm) /\ b!SndCommit(rm)
RcvCommit(rm)      == a!RcvCommit(rm) /\ UNCHANGED(vars_b)
SndAbort(rm)       == a!SndAbort(rm) /\ UNCHANGED(vars_b)
RcvAbort(rm)       == a!RcvAbort(rm) /\ UNCHANGED(vars_b)
SilentAbort(rm)    == a!SilentAbort(rm) /\ UNCHANGED(vars_b)

NextUnchanged == UNCHANGED vars_ab

Next ==
\E rm \in RMs:
\/ SndPrepare(rm)
\/ SyncRcvPrepare(rm)
\/ SyncSndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars_ab)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (msgs \in SUBSET(Message))
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent6_0 \in [RMs -> BOOLEAN]
/\ Fluent7_0 \in [RMs -> BOOLEAN]

I2 == a!IndAuto
I1 == b!IndAuto

\* Ok, so now we follow Ian's WIP paper's format for inductive invariant proofs.
\* Init /\ A => In
\* In /\ Next /\ A /\ A' => In'
\* In => G
=============================================================================
