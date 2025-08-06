--------------------------- MODULE b_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

VARIABLES CurCmd, CurPtr, ShrSet, InvSet

vars == <<CurCmd, CurPtr, ShrSet, InvSet>>

CandSep ==
/\ UNSAT

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == (CACHE_STATE \X DATA)

MSG == (MSG_CMD \X DATA)

Init ==
/\ InvSet = [i \in NODE |-> FALSE]
/\ ShrSet = [i \in NODE |-> FALSE]
/\ CurCmd = "Empty"
/\ CurPtr = 1

TypeOK ==
/\ (InvSet \in [NODE -> BOOLEAN])
/\ (ShrSet \in [NODE -> BOOLEAN])
/\ (CurCmd \in MSG_CMD)
/\ (CurPtr \in NODE)

NumRandSubsets == 5

TypeOKRand ==
/\ (InvSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (ShrSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (CurCmd \in RandomSubset(NumRandSubsets,MSG_CMD))
/\ (CurPtr \in RandomSubset(NumRandSubsets,NODE))

Symmetry == Permutations(NODE)

RecvReqS(i) ==
/\ CurCmd = "Empty"
/\ CurCmd' = "ReqS"
/\ CurPtr' = i
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED<<>>

RecvReqE(i) ==
/\ CurCmd = "Empty"
/\ CurCmd' = "ReqE"
/\ CurPtr' = i
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED<<>>

SendInvA(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqE"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED<<>>

SendInvB(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqS"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED<<>>

RecvInvAckA(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<InvSet,CurCmd,CurPtr>>
/\ UNCHANGED<<>>

RecvInvAckB(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<InvSet,CurCmd,CurPtr>>
/\ UNCHANGED<<>>

SendGntS(i) ==
/\ CurCmd = "ReqS"
/\ CurPtr = i
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<InvSet,CurPtr>>
/\ UNCHANGED<<>>

SendGntE(i) ==
/\ CurCmd = "ReqE"
/\ CurPtr = i
/\ (\A j \in NODE : ShrSet[j] = FALSE)
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<InvSet,CurPtr>>
/\ UNCHANGED<<>>

Next ==
\E i \in NODE :
\/ RecvReqS(i)
\/ RecvReqE(i)
\/ SendInvA(i)
\/ SendInvB(i)
\/ RecvInvAckA(i)
\/ RecvInvAckB(i)
\/ SendGntS(i)
\/ SendGntE(i)

Spec == ((Init /\ TypeOK) /\ [][Next]_vars)

NextUnchanged == UNCHANGED vars
=============================================================================
