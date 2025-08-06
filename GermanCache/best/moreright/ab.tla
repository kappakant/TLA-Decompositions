------------------------- MODULE ab -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization

\* converted NODE_NUM to actual sets of nodes
\* Nodes are also numbered along with data, for type safety or something like that
CONSTANTS NODE, DATA

CACHE_STATE == {"I", "S", "E"}
MSG_CMD == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

CACHE == CACHE_STATE \X DATA
MSG == MSG_CMD \X DATA

\* carini doesn't seem to work with records, so just convert records to functions
VARIABLES
    Cache,  \* array [NODE] of CACHE
    Chan1,  \* array [NODE] of MSG, channels for Req*
    Chan2,  \* array [NODE] of MSG, channels for Gnt* and Inv
    Chan3,  \* array [NODE] of MSG, channels for InvAck
    InvSet, \* array [NODE] of BOOLEAN, nodes to be invalidated
    ShrSet, \* array [NODE] of BOOLEAN, nodes having S or E copies
    ExGntd, \* BOOLEAN, E copy has been granted
    CurCmd, \* MSG_CMD, current request command
    CurPtr, \* NODE, current request node
    MemData, \* DATA, memory data
    AuxData \* DATA, latest value of cache line

vars == <<Cache, Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Init ==
    /\ Cache = [i \in NODE |-> <<"I", 1>>]
    /\ Chan1 = [i \in NODE |-> <<"Empty", 1>>]
    /\ Chan2 = [i \in NODE |-> <<"Empty", 1>>]
    /\ Chan3 = [i \in NODE |-> <<"Empty", 1>>]
    /\ InvSet = [i \in NODE |-> FALSE]
    /\ ShrSet = [i \in NODE |-> FALSE]
    /\ ExGntd = FALSE
    /\ CurCmd = "Empty"
    /\ CurPtr = 1
    /\ MemData = 1 
    /\ AuxData = 1

TypeOK ==
    /\ Cache \in [NODE -> CACHE]
    /\ Chan1 \in [NODE -> MSG]
    /\ Chan2 \in [NODE -> MSG]
    /\ Chan3 \in [NODE -> MSG]
    /\ InvSet \in [NODE -> BOOLEAN]
    /\ ShrSet \in [NODE -> BOOLEAN]
    /\ ExGntd \in BOOLEAN
    /\ CurCmd \in MSG_CMD
    /\ CurPtr \in NODE
    /\ MemData \in DATA
    /\ AuxData \in DATA

NumRandSubsets == 5

TypeOKRand ==
    /\ Cache   \in RandomSubset(NumRandSubsets, [NODE -> CACHE])
    /\ Chan1   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    /\ Chan2   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    /\ Chan3   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    /\ InvSet  \in RandomSubset(NumRandSubsets, [NODE -> BOOLEAN])
    /\ ShrSet  \in RandomSubset(NumRandSubsets, [NODE -> BOOLEAN])
    /\ ExGntd  \in RandomSubset(NumRandSubsets, BOOLEAN)
    /\ CurCmd  \in RandomSubset(NumRandSubsets, MSG_CMD)
    /\ CurPtr  \in RandomSubset(NumRandSubsets, NODE)
    /\ MemData \in RandomSubset(NumRandSubsets, DATA)
    /\ AuxData \in RandomSubset(NumRandSubsets, DATA)

Symmetry == Permutations(NODE)

(* Define state transitions here, following the Murphi model *)
\* maybe perfect situation? simply eliminate the behavior to just clauses.
\* cache shows up in functions but doesn't change value
SendReqS(i) ==
    /\ Chan1[i][1] = "Empty"
    /\ Cache[i][1] = "I"
    /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqS", Chan1[i][2]>>]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendReqE(i) ==
    /\ Chan1[i][1] = "Empty"
    /\ Cache[i][1] = "I" \/ Cache[i][1] = "S"
    /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqE", Chan1[i][2]>>]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>
    
\* SendReqEA(i) ==
\*     /\ Chan1[i][1] = "Empty"
\*     /\ Cache[i][1] = "I" 
\*     /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqE", Chan1[i][2]>>]
\*     /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>
\* 
\* SendReqEB(i) ==
\*     /\ Chan1[i][1] = "Empty"
\*     /\ Cache[i][1] = "S"
\*     /\ Chan1' = [Chan1 EXCEPT ![i] = <<"ReqE", Chan1[i][2]>>]
\*     /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>


RecvReqS(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i][1] = "ReqS"
    /\ CurCmd' = "ReqS"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i] = <<"Empty", Chan1[i][2]>>]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

RecvReqE(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i][1] = "ReqE"
    /\ CurCmd' = "ReqE"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i] = <<"Empty", Chan1[i][2]>>]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

SendInvA(i) ==
    /\ Chan2[i][1] = "Empty"
    /\ InvSet[i] = TRUE
    /\ CurCmd = "ReqE" 
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Inv", Chan2[i][2]>>]
    /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendInvB(i) ==
    /\ Chan2[i][1] = "Empty"
    /\ InvSet[i] = TRUE
    /\ CurCmd = "ReqS" 
    /\ ExGntd = TRUE
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Inv", Chan2[i][2]>>]
    /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

\* SendInvAck(i) ==
\*     /\ Chan2[i][1] = "Inv"
\*     /\ Chan3[i][1] = "Empty"
\*     /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Empty", Chan2[i][2]>>]
\*     /\ Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck", Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
\*     /\ Cache' = [Cache EXCEPT ![i].State = "I"]
\*     /\ UNCHANGED <<Chan1, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendInvAckA(i) ==
    /\ Cache[i][1] = "E"
    /\ Chan2[i][1] = "Inv"
    /\ Chan3[i][1] = "Empty"
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Empty", Chan2[i][2]>>]
    /\ Chan3' = [Chan3 EXCEPT ![i] = <<"InvAck", Cache[i][2]>>]
    /\ Cache' = [Cache EXCEPT ![i] = <<"I", Cache[i][2]>>]
    /\ UNCHANGED <<Chan1, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendInvAckB(i) ==
    /\ Cache[i][1] # "E"
    /\ Chan2[i][1] = "Inv"
    /\ Chan3[i][1] = "Empty"
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Empty", Chan2[i][2]>>]
    /\ Chan3' = [Chan3 EXCEPT ![i] = <<"InvAck", Chan3[i][2]>>]
    /\ UNCHANGED <<Cache, Chan1, InvSet, ShrSet, CurCmd, CurPtr, ExGntd, MemData, AuxData>>

RecvInvAckA(i) ==
    /\ Chan3[i][1] = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i] = <<"Empty", Chan3[i][2]>>]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ ExGntd = TRUE
    /\ ExGntd' = FALSE
    /\ MemData' = Chan3[i][2]
    /\ UNCHANGED <<Cache, Chan1, Chan2, InvSet, CurCmd, CurPtr, AuxData>>

RecvInvAckB(i) ==
    /\ Chan3[i][1] = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i] = <<"Empty", Chan3[i][2]>>]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ ExGntd = FALSE
    /\ UNCHANGED <<Cache, Chan1, Chan2, InvSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendGntS(i) ==
    /\ CurCmd = "ReqS"
    /\ CurPtr = i
    /\ Chan2[i][1] = "Empty"
    /\ ExGntd = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"GntS", MemData>>]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, ExGntd, CurPtr, MemData, AuxData>>

SendGntE(i) ==
    /\ CurCmd = "ReqE"
    /\ CurPtr = i
    /\ Chan2[i][1] = "Empty"
    /\ ExGntd = FALSE
    /\ \A j \in NODE : ShrSet[j] = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"GntE", MemData>>]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ ExGntd' = TRUE
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, CurPtr, MemData, AuxData>>

RecvGntS(i) ==
    /\ Chan2[i][1] = "GntS"
    /\ Cache' = [Cache EXCEPT ![i] = <<"S", Chan2[i][2]>>]
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Empty", Chan2[i][2]>>]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvGntE(i) ==
    /\ Chan2[i][1] = "GntE"
    /\ Cache' = [Cache EXCEPT ![i] = <<"E", Chan2[i][2]>>]
    /\ Chan2' = [Chan2 EXCEPT ![i] = <<"Empty", Chan2[i][2]>>]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Store(i, d) ==
    /\ Cache[i][1] = "E"
    /\ Cache' = [Cache EXCEPT ![i] = <<Cache[i][1], d>>]
    /\ AuxData' = d
    /\ UNCHANGED <<Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData>>

Next == 
    \E i \in NODE:
        \/ SendReqS(i)
        \/ SendReqEA(i)
        \/ SendReqEB(i)
        \/ RecvReqS(i)
        \/ RecvReqE(i)
        \/ SendInvA(i)
        \/ SendInvB(i)
        \/ SendInvAckA(i)
        \/ SendInvAckB(i)
        \/ RecvInvAckA(i)
        \/ RecvInvAckB(i)
        \/ SendGntS(i)
        \/ SendGntE(i)
        \/ RecvGntS(i)
        \/ RecvGntE(i)
        \/ \E d \in DATA: Store(i, d)

Spec == Init /\ TypeOK /\ [][Next]_vars

CtrlProp ==
    \A i, j \in NODE :
        i /= j =>
            /\ (Cache[i][1] = "E" => Cache[j][1] = "I")
            /\ (Cache[i][1] = "S" => (Cache[j][1] # "I" => Cache[j][1] = "S"))

DataProp ==
    /\ (ExGntd = FALSE => MemData = AuxData)
    /\ \A i \in NODE : 
        Cache[i][1] /= "I" => Cache[i][2] = AuxData

Inv ==
    /\ TypeOK
    /\ CtrlProp
    /\ DataProp

NextUnchanged == UNCHANGED vars

====
