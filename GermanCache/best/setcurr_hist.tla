--------------------------- MODULE setcurr_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

VARIABLES ShrSet, InvSet

vars == <<ShrSet, InvSet>>

CandSep ==
/\ UNSAT

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == (CACHE_STATE \X DATA)

MSG == (MSG_CMD \X DATA)

Init ==
/\ InvSet = [i \in NODE |-> FALSE]
/\ ShrSet = [i \in NODE |-> FALSE]

TypeOK ==
/\ (InvSet \in [NODE -> BOOLEAN])
/\ (ShrSet \in [NODE -> BOOLEAN])

NumRandSubsets == 5

TypeOKRand ==
/\ (InvSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (ShrSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))

Symmetry == Permutations(NODE)

RecvReqS(i) ==
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED<<>>

RecvReqE(i) ==
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED<<>>

SendInv(i) ==
/\ InvSet[i] = TRUE
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED<<>>

RecvInvAck(i) ==
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<InvSet>>
/\ UNCHANGED<<>>

SendGntS(i) ==
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ UNCHANGED <<InvSet>>
/\ UNCHANGED<<>>

SendGntE(i) ==
/\ (\A j \in NODE : ShrSet[j] = FALSE)
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ UNCHANGED <<InvSet>>
/\ UNCHANGED<<>>

Next ==
\E i \in NODE :
\/ RecvReqS(i)
\/ RecvReqE(i)
\/ SendInv(i)
\/ RecvInvAck(i)
\/ SendGntS(i)
\/ SendGntE(i)

Spec == ((Init /\ TypeOK) /\ [][Next]_vars)

NextUnchanged == UNCHANGED vars
=============================================================================
