--------------------------- MODULE GermanCache_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

VARIABLES CurCmd, Chan2, ExGntd, Chan3, CurPtr, ShrSet, MemData, InvSet, Chan1, Cache

vars == <<CurCmd, Chan2, ExGntd, Chan3, CurPtr, ShrSet, MemData, InvSet, Chan1, Cache>>

CandSep ==
TRUE

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == [State : CACHE_STATE,Data : DATA]

MSG == [Cmd : MSG_CMD,Data : DATA]

Init ==
/\ Cache = [i \in NODE |-> [State |-> "I",Data |-> 1]]
/\ Chan1 = [i \in NODE |-> [Cmd |-> "Empty",Data |-> 1]]
/\ Chan2 = [i \in NODE |-> [Cmd |-> "Empty",Data |-> 1]]
/\ Chan3 = [i \in NODE |-> [Cmd |-> "Empty",Data |-> 1]]
/\ InvSet = [i \in NODE |-> FALSE]
/\ ShrSet = [i \in NODE |-> FALSE]
/\ ExGntd = FALSE
/\ CurCmd = "Empty"
/\ CurPtr = 1
/\ MemData = 1

TypeOK ==
/\ (Cache \in [NODE -> CACHE])
/\ (Chan1 \in [NODE -> MSG])
/\ (Chan2 \in [NODE -> MSG])
/\ (Chan3 \in [NODE -> MSG])
/\ (InvSet \in [NODE -> BOOLEAN])
/\ (ShrSet \in [NODE -> BOOLEAN])
/\ (ExGntd \in BOOLEAN)
/\ (CurCmd \in MSG_CMD)
/\ (CurPtr \in NODE)
/\ (MemData \in DATA)

NumRandSubsets == 5

TypeOKRand ==
/\ (Cache \in RandomSubset(NumRandSubsets,[NODE -> CACHE]))
/\ (Chan1 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (Chan2 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (Chan3 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (InvSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (ShrSet \in RandomSubset(NumRandSubsets,[NODE -> BOOLEAN]))
/\ (ExGntd \in RandomSubset(NumRandSubsets,BOOLEAN))
/\ (CurCmd \in RandomSubset(NumRandSubsets,MSG_CMD))
/\ (CurPtr \in RandomSubset(NumRandSubsets,NODE))
/\ (MemData \in RandomSubset(NumRandSubsets,DATA))

Symmetry == Permutations(NODE)

SendReqS(i) ==
/\ Chan1[i].Cmd = "Empty"
/\ Cache[i].State = "I"
/\ Chan1' = [Chan1 EXCEPT![i][Cmd] = "ReqS"]
/\ UNCHANGED <<Cache,Chan2,Chan3,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendReqE(i) ==
/\ Chan1[i].Cmd = "Empty"
/\ (Cache[i].State = "I" \/ Cache[i].State = "S")
/\ Chan1' = [Chan1 EXCEPT![i][Cmd] = "ReqE"]
/\ UNCHANGED <<Cache,Chan2,Chan3,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvReqS(i) ==
/\ CurCmd = "Empty"
/\ Chan1[i].Cmd = "ReqS"
/\ CurCmd' = "ReqS"
/\ CurPtr' = i
/\ Chan1' = [Chan1 EXCEPT![i][Cmd] = "Empty"]
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<Cache,Chan2,Chan3,ShrSet,ExGntd,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvReqE(i) ==
/\ CurCmd = "Empty"
/\ Chan1[i].Cmd = "ReqE"
/\ CurCmd' = "ReqE"
/\ CurPtr' = i
/\ Chan1' = [Chan1 EXCEPT![i][Cmd] = "Empty"]
/\ InvSet' = [j \in NODE |-> ShrSet[j]]
/\ UNCHANGED <<Cache,Chan2,Chan3,ShrSet,ExGntd,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInv(i) ==
/\ Chan2[i].Cmd = "Empty"
/\ InvSet[i] = TRUE
/\ (CurCmd = "ReqE" \/ (CurCmd = "ReqS" /\ ExGntd = TRUE))
/\ Chan2' = [Chan2 EXCEPT![i][Cmd] = "Inv"]
/\ InvSet' = [InvSet EXCEPT![i] = FALSE]
/\ UNCHANGED <<Cache,Chan1,Chan3,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInvAck(i) ==
/\ Chan2[i].Cmd = "Inv"
/\ Chan3[i].Cmd = "Empty"
/\ Chan2' = [Chan2 EXCEPT![i][Cmd] = "Empty"]
/\ Chan3' = [Chan3 EXCEPT![i] = [Cmd |-> "InvAck",Data |-> IF Cache[i].State |-> "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
/\ Cache' = [Cache EXCEPT![i][State] = "I"]
/\ UNCHANGED <<Chan1,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvInvAck(i) ==
/\ Chan3[i].Cmd = "InvAck"
/\ CurCmd /= "Empty"
/\ Chan3' = [Chan3 EXCEPT![i][Cmd] = "Empty"]
/\ ShrSet' = [ShrSet EXCEPT![i] = FALSE]
/\ IF ExGntd = TRUE THEN (ExGntd' = FALSE /\ MemData' = Chan3[i].Data) ELSE (UNCHANGED ExGntd /\ UNCHANGED MemData)
/\ UNCHANGED <<Cache,Chan1,Chan2,InvSet,CurCmd,CurPtr>>
/\ UNCHANGED<<>>
/\ CandSep'

SendGntS(i) ==
/\ CurCmd = "ReqS"
/\ CurPtr = i
/\ Chan2[i].Cmd = "Empty"
/\ ExGntd = FALSE
/\ Chan2' = [Chan2 EXCEPT![i] = [Cmd |-> "GntS",Data |-> MemData]]
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ CurCmd' = "Empty"
/\ UNCHANGED <<Cache,Chan1,Chan3,InvSet,CurPtr,ExGntd,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendGntE(i) ==
/\ CurCmd = "ReqE"
/\ CurPtr = i
/\ Chan2[i].Cmd = "Empty"
/\ ExGntd = FALSE
/\ (\A j \in NODE : ShrSet[j] = FALSE)
/\ Chan2' = [Chan2 EXCEPT![i] = [Cmd |-> "GntE",Data |-> MemData]]
/\ ShrSet' = [ShrSet EXCEPT![i] = TRUE]
/\ ExGntd' = TRUE
/\ CurCmd' = "Empty"
/\ UNCHANGED <<Cache,Chan1,Chan3,InvSet,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvGntS(i) ==
/\ Chan2[i].Cmd = "GntS"
/\ Cache' = [Cache EXCEPT![i] = [State |-> "S",Data |-> Chan2[i].Data]]
/\ Chan2' = [Chan2 EXCEPT![i][Cmd] = "Empty"]
/\ UNCHANGED <<Chan1,Chan3,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvGntE(i) ==
/\ Chan2[i].Cmd = "GntE"
/\ Cache' = [Cache EXCEPT![i] = [State |-> "E",Data |-> Chan2[i].Data]]
/\ Chan2' = [Chan2 EXCEPT![i][Cmd] = "Empty"]
/\ UNCHANGED <<Chan1,Chan3,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

Store(i,d) ==
/\ Cache[i].State = "E"
/\ Cache' = [Cache EXCEPT![i][Data] = d]
/\ UNCHANGED <<Chan1,Chan2,Chan3,InvSet,ShrSet,ExGntd,CurCmd,CurPtr,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendReqSAction == (TRUE /\ (\E i \in NODE : SendReqS(i)))

SendReqEAction == (TRUE /\ (\E i \in NODE : SendReqE(i)))

RecvReqSAction == (TRUE /\ (\E i \in NODE : RecvReqS(i)))

RecvReqEAction == (TRUE /\ (\E i \in NODE : RecvReqE(i)))

SendInvAction == (TRUE /\ (\E i \in NODE : SendInv(i)))

SendInvAckAction == (TRUE /\ (\E i \in NODE : SendInvAck(i)))

RecvInvAckAction == (TRUE /\ (\E i \in NODE : RecvInvAck(i)))

SendGntSAction == (TRUE /\ (\E i \in NODE : SendGntS(i)))

SendGntEAction == (TRUE /\ (\E i \in NODE : SendGntE(i)))

RecvGntSAction == (TRUE /\ (\E i \in NODE : RecvGntS(i)))

RecvGntEAction == (TRUE /\ (\E i \in NODE : RecvGntE(i)))

StoreAction == (TRUE /\ (\E i \in NODE, d \in DATA : Store(i,d)))

NextOld ==
\/ SendReqSAction
\/ SendReqEAction
\/ RecvReqSAction
\/ RecvReqEAction
\/ SendInvAction
\/ SendInvAckAction
\/ RecvInvAckAction
\/ SendGntSAction
\/ SendGntEAction
\/ RecvGntSAction
\/ RecvGntEAction
\/ StoreAction

Next ==
\E i \in NODE :
\/ SendReqS(i)
\/ SendReqE(i)
\/ RecvReqS(i)
\/ RecvReqE(i)
\/ SendInv(i)
\/ SendInvAck(i)
\/ RecvInvAck(i)
\/ SendGntS(i)
\/ SendGntE(i)
\/ RecvGntS(i)
\/ RecvGntE(i)
\/ (\E d \in DATA : Store(i,d))

CtrlProp1 == (\A i,j \in NODE : (i /= j => (Cache[i].State = "E" => Cache[j].State = "I")))

CtrlProp == (\A i,j \in NODE : (i /= j => ((Cache[i].State = "E" => Cache[j].State = "I") /\ (Cache[i].State = "S" => (Cache[j].State = "I" \/ Cache[j].State = "S")))))

Invariant ==
/\ CtrlProp

NextUnchanged == UNCHANGED vars
=============================================================================
