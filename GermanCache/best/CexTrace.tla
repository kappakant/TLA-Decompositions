--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS DATA, NODE, NUM2, NUM3, NUM1

VARIABLES CurCmd, CurPtr, err, ShrSet, InvSet, cexTraceIdx

vars == <<CurCmd, CurPtr, err, ShrSet, InvSet, cexTraceIdx>>

NoErr == err = FALSE

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == (CACHE_STATE \X DATA)

MSG == (MSG_CMD \X DATA)

Init ==
/\ InvSet = [i \in NODE |-> FALSE]
/\ ShrSet = [i \in NODE |-> FALSE]
/\ CurCmd = "Empty"
/\ CurPtr = 1
/\ cexTraceIdx = 0
/\ err = FALSE

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
/\ cexTraceIdx' = cexTraceIdx + 1

RecvReqE(i) ==
/\ CurCmd = "Empty"
/\ CurCmd' = "ReqE"
/\ CurPtr' = i
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ cexTraceIdx' = cexTraceIdx + 1

SendInvA(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqE"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<ShrSet,CurCmd,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

SendInvB(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqS"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<ShrSet,CurCmd,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

RecvInvAckA(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<InvSet,CurCmd,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

RecvInvAckB(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<InvSet,CurCmd,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

SendGntS(i) ==
/\ CurCmd = "ReqS"
/\ CurPtr = i
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<InvSet,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

SendGntE(i) ==
/\ CurCmd = "ReqE"
/\ CurPtr = i
/\ (\A j \in NODE : ShrSet[j] = FALSE)
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<InvSet,CurPtr>>
/\ cexTraceIdx' = cexTraceIdx + 1

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

TraceConstraint ==
/\ cexTraceIdx = 0 => RecvReqS(1) /\ err' = err
/\ cexTraceIdx = 1 => SendGntS(1) /\ err' = err
/\ cexTraceIdx = 2 => RecvReqE(2) /\ err' = err
/\ cexTraceIdx = 3 => SendInvA(1) /\ err' = err
/\ cexTraceIdx = 4 => RecvInvAckB(1) /\ err' = err
/\ cexTraceIdx = 5 => SendGntE(2) /\ err' = TRUE
/\ cexTraceIdx >= 6 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================
