--------------------------- MODULE msgs_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned 6
VARIABLES msgs, tmPrepared, Fluent7_0, Fluent20_0, Fluent22_0, Fluent11_0, Fluent21_0, Fluent10_0, Fluent23_0

vars == <<msgs, tmPrepared, Fluent7_0, Fluent20_0, Fluent22_0, Fluent11_0, Fluent21_0, Fluent10_0, Fluent23_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent23_0[var0]) => (~(Fluent22_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (~(Fluent21_0[var0]))

Init ==
/\ msgs = {}
/\ tmPrepared = {}
/\ Fluent20_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent22_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent21_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent23_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent20_0, Fluent22_0, Fluent21_0, Fluent23_0>>
/\ CandSep'
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent11_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs>>
/\ Fluent22_0' = [x0 \in RMs |-> TRUE]
/\ Fluent21_0' = [Fluent21_0 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent20_0, Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ Fluent22_0' = [Fluent22_0 EXCEPT ![rm] = FALSE]
/\ Fluent21_0' = [x0 \in RMs |-> TRUE]
/\ Fluent23_0' = [Fluent23_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent20_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs,tmPrepared>>
/\ UNCHANGED<<Fluent20_0, Fluent22_0, Fluent21_0, Fluent23_0>>
/\ CandSep'
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0, Fluent10_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ Fluent20_0' = [Fluent20_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent22_0, Fluent21_0, Fluent23_0>>
/\ CandSep'
/\ UNCHANGED<<Fluent7_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs,tmPrepared>>
/\ UNCHANGED<<Fluent20_0, Fluent22_0, Fluent21_0, Fluent23_0>>
/\ CandSep'
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent11_0, Fluent10_0>>
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
/\ Fluent7_0  \in [RMs -> BOOLEAN] 
/\ Fluent20_0 \in [RMs -> BOOLEAN]
/\ Fluent22_0 \in [RMs -> BOOLEAN]
/\ Fluent11_0 \in [RMs -> BOOLEAN]
/\ Fluent21_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0 \in [RMs -> BOOLEAN]
/\ Fluent23_0 \in [RMs -> BOOLEAN]

Safety ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent11_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent11_0[var0]))

NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent7_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN]) 
/\ Fluent20_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent22_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent11_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent21_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent23_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* added by endive
Inv1405_1_0_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : ~(Fluent11_0[rmi]) \/ (~([type |-> "Abort"] \in msgs))
Inv427_1_1_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent20_0[rmj]) \/ (~([type |-> "Abort"] \in msgs))
Inv527_1_0_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent21_0[rmi]) \/ (~([type |-> "Commit"] \in msgs))
Inv150_1_1_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent10_0[rmk]) \/ (~(Fluent21_0[rmi]))
Inv830_1_2_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent23_0[rmj]) \/ (~(Fluent21_0[rmi]))
Inv511_1_0_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent21_0[rmi]) \/ (~(Fluent11_0[rmk]))
Inv167_1_1_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent10_0[rmk]) \/ (~(tmPrepared = RMs))
Inv166_1_2_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent10_0[rmk]) \/ (~([type |-> "Prepared", theRM |-> rmk] \in msgs))
Inv1113_1_0_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : ([type |-> "Prepared", theRM |-> rmi] \in msgs) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv424_1_1_def == \A rmi \in RMs : \E rmj \in RMs : \A rmk \in RMs : (Fluent20_0[rmj]) \/ (~(Fluent7_0[rmi]))

\* The inductive invariant candidate.
IndAuto ==
/\ Safety
/\ Inv1405_1_0_def
/\ Inv427_1_1_def
/\ Inv527_1_0_def
/\ Inv150_1_1_def
/\ Inv830_1_2_def
/\ Inv511_1_0_def
/\ Inv167_1_1_def
/\ Inv166_1_2_def
/\ Inv1113_1_0_def
/\ Inv424_1_1_def

IISpec == TypeOK /\ IndAuto /\ [][Next]_vars
=============================================================================
