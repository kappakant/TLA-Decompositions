------------------------- MODULE setcurr -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

CACHE_STATE == {"I", "S", "E"}
MSG_CMD == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

CACHE == CACHE_STATE \X DATA
MSG == MSG_CMD \X DATA

VARIABLES
    \* Cache,  \* array [NODE] of CACHE
    \* Chan1,  \* array [NODE] of MSG, channels for Req*
    \* Chan2,  \* array [NODE] of MSG, channels for Gnt* and Inv
    \* Chan3,  \* array [NODE] of MSG, channels for InvAck
    InvSet, \* array [NODE] of BOOLEAN, nodes to be invalidated
    ShrSet, \* array [NODE] of BOOLEAN, nodes having S or E copies
    \* ExGntd, \* BOOLEAN, E copy has been granted
    CurCmd, \* MSG_CMD, current request command
    CurPtr, \* NODE, current request node
    \* MemData,\* DATA, memory data
    AuxData \* DATA, latest value of cache line

vars == <<Chan1, Chan3, AuxData>>

Init ==
    \* /\ Cache = [i \in NODE |-> [State |-> "I", Data |-> 1]]
    \* /\ Chan1 = [i \in NODE |-> <<"Empty", 1>>]
    \* /\ Chan2 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    \* /\ Chan3 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ InvSet = [i \in NODE |-> FALSE]
    /\ ShrSet = [i \in NODE |-> FALSE]
    \* /\ ExGntd = FALSE
    /\ CurCmd = "Empty"
    /\ CurPtr = 3 
    \* /\ MemData = 1
    /\ AuxData = 1

TypeOK ==
    \* /\ Cache \in [NODE -> CACHE]
    \* /\ Chan1 \in [NODE -> MSG]
    \* /\ Chan2 \in [NODE -> MSG]
    \* /\ Chan3 \in [NODE -> MSG]
    /\ InvSet \in [NODE -> BOOLEAN]
    /\ ShrSet \in [NODE -> BOOLEAN]
    \* /\ ExGntd \in BOOLEAN
    /\ CurCmd \in MSG_CMD
    /\ CurPtr \in NODE
    \* /\ MemData \in DATA
    /\ AuxData \in DATA

NumRandSubsets == 5

TypeOKRand ==
    \* /\ Cache   \in RandomSubset(NumRandSubsets, [NODE -> CACHE])
    \* /\ Chan1   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    \* /\ Chan2   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    \* /\ Chan3   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    /\ InvSet  \in RandomSubset(NumRandSubsets, [NODE -> BOOLEAN])
    /\ ShrSet  \in RandomSubset(NumRandSubsets, [NODE -> BOOLEAN])
    \* /\ ExGntd  \in RandomSubset(NumRandSubsets, BOOLEAN)
    /\ CurCmd  \in RandomSubset(NumRandSubsets, MSG_CMD)
    /\ CurPtr  \in RandomSubset(NumRandSubsets, NODE)
    \* /\ MemData \in RandomSubset(NumRandSubsets, DATA)
    /\ AuxData \in RandomSubset(NumRandSubsets, DATA)

Symmetry == Permutations(NODE)

(* Define state transitions here, following the Murphi model *)
\* SendReqS(i) ==
    \* /\ Chan1[i][1] = "Empty"
\*     /\ Cache[i].State = "I"
    \* /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqS", Chan1[i][2]>>]
    \* /\ UNCHANGED <<Chan3, AuxData>>
\* 
\* SendReqEA(i) ==
\*     /\ Chan1[i][1] = "Empty"
\* \*  /\ Cache[i].State = "I" 
\*     /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqE", Chan1[i][2]>>]
\*     /\ UNCHANGED <<AuxData>>

\* SendReqEB(i) ==
\*     /\ Chan1[i][1] = "Empty"
\* \*  /\ Cache[i].State = "S" 
\*     /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqE", Chan1[i][2]>>]
\*     /\ UNCHANGED <<AuxData>>

RecvReqS(i) ==
    /\ CurCmd = "Empty"
\*     /\ Chan1[i][1] = "ReqS"
    /\ CurCmd' = "ReqS"
    /\ CurPtr' = i
\*     /\ Chan1' = [Chan1 EXCEPT ![i] = <<"Empty", Chan1[i][2]>>]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<ShrSet, AuxData>>

RecvReqE(i) ==
    /\ CurCmd = "Empty"
    \* /\ Chan1[i][1] = "ReqE"
    /\ CurCmd' = "ReqE"
    /\ CurPtr' = i
    \* /\ Chan1' = [Chan1 EXCEPT ![i] = <<"Empty", Chan1[i][2]>>]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<ShrSet, AuxData>>

SendInvA(i) ==
    \* /\ Chan2[i].Cmd = "Empty"
    /\ InvSet[i] = TRUE
    /\ CurCmd = "ReqE" 
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"]
    \* /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    \* /\ UNCHANGED <<ShrSet>>

SendInvB(i) ==
    \* /\ Chan2[i].Cmd = "Empty"
    /\ InvSet[i] = TRUE
    /\ CurCmd = "ReqS" 
    /\ ExGntd = TRUE
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"]
    \* /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    \* /\ UNCHANGED <<ShrSet>>
    

SendInvAck(i) ==
\*     /\ Chan2[i].Cmd = "Inv"
    /\ Chan3[i][1] = "Empty"
\*     /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck", Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
\*     /\ Cache' = [Cache EXCEPT ![i].State = "I"]
    /\ UNCHANGED <<Chan1, AuxData>>

RecvInvAckA(i) ==
    /\ Chan3[i].Cmd = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i].Cmd = "Empty"]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ ExGntd = TRUE
    /\ ExGntd' = FALSE
    /\ MemData' = Chan3[i].Data
    /\ UNCHANGED <<Chan1, AuxData>>

RecvInvAckB(i) ==
    /\ Chan3[i].Cmd = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i].Cmd = "Empty"]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ ExGntd = FALSE
    /\ UNCHANGED ExGntd
    /\ UNCHANGED MemData
    /\ UNCHANGED <<Chan1, AuxData>>


\* SendGntS(i) ==
    \* /\ CurCmd = "ReqS"
    \* /\ CurPtr = i
    \* /\ Chan2[i].Cmd = "Empty"
    \* /\ ExGntd = FALSE
    \* /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntS", Data |-> MemData]]
    \* /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    \* /\ CurCmd' = "Empty"
    \* /\ UNCHANGED <<InvSet>>

\* SendGntE(i) ==
    \* /\ CurCmd = "ReqE"
    \* /\ CurPtr = i
    \* /\ Chan2[i].Cmd = "Empty"
    \* /\ ExGntd = FALSE
    \* /\ \A j \in NODE : ShrSet[j] = FALSE
    \* /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntE", Data |-> MemData]]
    \* /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    \* /\ ExGntd' = TRUE
    \* /\ CurCmd' = "Empty"
    \* /\ UNCHANGED <<InvSet>>

\* RecvGntS(i) ==
\*     /\ Chan2[i].Cmd = "GntS"
\*     /\ Cache' = [Cache EXCEPT ![i] = [State |-> "S", Data |-> Chan2[i].Data]]
\*     /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
\*     /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

\* RecvGntE(i) ==
\*     /\ Chan2[i].Cmd = "GntE"
\*     /\ Cache' = [Cache EXCEPT ![i] = [State |-> "E", Data |-> Chan2[i].Data]]
\*     /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
\*     /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Store(i, d) ==
\*     /\ Cache[i].State = "E"
\*     /\ Cache' = [Cache EXCEPT ![i].Data = d]
    /\ AuxData' = d
    /\ UNCHANGED <<Chan1, Chan3>>
Next == 
    \E i \in NODE:
        \* \/ SendReqS(i)
        \* \/ SendReqE(i)
        \/ RecvReqS(i)
        \/ RecvReqE(i)
        \* \/ SendInvA(i)
        \* \/ SendInvB(i)
        \* \/ SendInvAck(i)
        \/ RecvInvAck(i)
        \* \/ SendGntS(i)
        \* \/ SendGntE(i)
        \* \/ RecvGntS(i)
        \* \/ RecvGntE(i)
        \/ \E d \in DATA: Store(i, d)

Spec == Init /\ TypeOK /\ [][Next]_vars

NextUnchanged == UNCHANGED vars

====
