--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS DATA, NODE, NUM2, NUM3, NUM1

VARIABLES CurCmd, CurPtr, ShrSet, InvSet, Fluent1_0, cexTraceIdx, Chan1

vars == <<CurCmd, CurPtr, ShrSet, InvSet, Fluent1_0, cexTraceIdx, Chan1>>

TraceConstraint ==
/\ cexTraceIdx = 0 =>
  /\ CurCmd = "Empty"
  /\ CurPtr = 1
  /\ InvSet = <<FALSE, FALSE, FALSE>>
  /\ Chan1 = <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>
  /\ Fluent1_0 = <<FALSE, FALSE, FALSE>>
  /\ ShrSet = <<FALSE, FALSE, FALSE>>

/\ cexTraceIdx = 1 =>
  /\ CurCmd = "Empty"
  /\ CurPtr = 1
  /\ InvSet = <<FALSE, FALSE, FALSE>>
  /\ Chan1 = <<<<"ReqS", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>
  /\ Fluent1_0 = <<FALSE, FALSE, FALSE>>
  /\ ShrSet = <<FALSE, FALSE, FALSE>>

/\ cexTraceIdx = 2 =>
  /\ CurCmd = "ReqS"
  /\ CurPtr = 1
  /\ InvSet = <<FALSE, FALSE, FALSE>>
  /\ Chan1 = <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>
  /\ Fluent1_0 = <<FALSE, FALSE, FALSE>>
  /\ ShrSet = <<FALSE, FALSE, FALSE>>

/\ cexTraceIdx = 3 =>
  /\ CurCmd = "Empty"
  /\ CurPtr = 1
  /\ InvSet = <<FALSE, FALSE, FALSE>>
  /\ Chan1 = <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>
  /\ Fluent1_0 = <<TRUE, FALSE, FALSE>>
  /\ ShrSet = <<TRUE, FALSE, FALSE>>


CandSep == (\A var0 \in DATA : (\A var1 \in DATA : (Fluent1_0[var1] => ~(var1 <= var0))))

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == (CACHE_STATE \X DATA)

MSG == (MSG_CMD \X DATA)

Init ==
/\ Chan1 = [i \in NODE |-> <<"Empty",1>>]
/\ InvSet = [i \in NODE |-> FALSE]
/\ ShrSet = [i \in NODE |-> FALSE]
/\ CurCmd = "Empty"
/\ CurPtr = 1
/\ Fluent1_0 = [x0 \in NODE |-> FALSE]
/\ cexTraceIdx = 0
/\ TraceConstraint

TypeOK ==
/\ (Chan1 \in [NODE -> MSG])
/\ (InvSet \in [NODE -> BOOLEAN])
/\ (ShrSet \in [NODE -> BOOLEAN])
/\ (CurCmd \in MSG_CMD)
/\ (CurPtr \in NODE)

NumRandSubsets == 5

TypeOKRand ==
/\ (Chan1 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (InvSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (ShrSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (CurCmd \in RandomSubset(NumRandSubsets,MSG_CMD))
/\ (CurPtr \in RandomSubset(NumRandSubsets,NODE))

Symmetry == Permutations(NODE)

SendReqS(i) ==
/\ Chan1[i][1] = "Empty"
/\ Chan1' = [Chan1 EXCEPT![i] = <<"ReqS",Chan1[i][2]>>]
/\ UNCHANGED <<InvSet,ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendReqE(i) ==
/\ Chan1[i][1] = "Empty"
/\ Chan1' = [Chan1 EXCEPT![i] = <<"ReqE",Chan1[i][2]>>]
/\ UNCHANGED <<InvSet,ShrSet,CurCmd,CurPtr>>

SendReqEA(i) ==
/\ Chan1[i][1] = "Empty"
/\ Chan1' = [Chan1 EXCEPT![i] = <<"ReqE",Chan1[i][2]>>]
/\ UNCHANGED <<InvSet,ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendReqEB(i) ==
/\ Chan1[i][1] = "Empty"
/\ Chan1' = [Chan1 EXCEPT![i] = <<"ReqE",Chan1[i][2]>>]
/\ UNCHANGED <<InvSet,ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvReqS(i) ==
/\ CurCmd = "Empty"
/\ Chan1[i][1] = "ReqS"
/\ CurCmd' = "ReqS"
/\ CurPtr' = i
/\ Chan1' = [Chan1 EXCEPT![i] = <<"Empty",Chan1[i][2]>>]
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvReqE(i) ==
/\ CurCmd = "Empty"
/\ Chan1[i][1] = "ReqE"
/\ CurCmd' = "ReqE"
/\ CurPtr' = i
/\ Chan1' = [Chan1 EXCEPT![i] = <<"Empty",Chan1[i][2]>>]
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<ShrSet>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendInvA(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqE"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<Chan1,ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendInvB(i) ==
/\ InvSet[i] = TRUE
/\ CurCmd = "ReqS"
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<Chan1,ShrSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvInvAckA(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<Chan1,InvSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

RecvInvAckB(i) ==
/\ CurCmd /= "Empty"
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<Chan1,InvSet,CurCmd,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendGntS(i) ==
/\ CurCmd = "ReqS"
/\ CurPtr = i
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<Chan1,InvSet,CurPtr>>
/\ Fluent1_0' = [Fluent1_0 EXCEPT![i] = TRUE]
/\ UNCHANGED <<>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

SendGntE(i) ==
/\ CurCmd = "ReqE"
/\ CurPtr = i
/\ (\A j \in NODE : ShrSet[j] = FALSE)
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<Chan1,InvSet,CurPtr>>
/\ UNCHANGED <<Fluent1_0>>
/\ cexTraceIdx' = cexTraceIdx + 1
/\ TraceConstraint'

Next ==
\E i \in NODE :
\/ SendReqS(i)
\/ SendReqEA(i)
\/ SendReqEB(i)
\/ RecvReqS(i)
\/ RecvReqE(i)
\/ SendInvA(i)
\/ SendInvB(i)
\/ RecvInvAckA(i)
\/ RecvInvAckB(i)
\/ SendGntS(i)
\/ SendGntE(i)

Spec == ((Init /\ TypeOK) /\ [][Next]_vars)

Inv == TypeOK

NextUnchanged == UNCHANGED vars
=============================================================================
