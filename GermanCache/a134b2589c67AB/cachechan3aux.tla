------------------------- MODULE cachechan3aux -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE_NUM, DATA_NUM
ASSUME NODE_NUM \in Nat /\ NODE_NUM > 0
ASSUME DATA_NUM \in Nat /\ DATA_NUM > 0

NODE == 1..NODE_NUM
DATA == 1..DATA_NUM

CACHE_STATE == {"I", "S", "E"}
MSG_CMD == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

CACHE == [State: CACHE_STATE, Data: DATA]
MSG == [Cmd: MSG_CMD, Data: DATA]

VARIABLES
    Cache,  \* array [NODE] of CACHE
    Chan3,  \* array [NODE] of MSG, channels for InvAck
    AuxData

vars == <<Cache, Chan3, AuxData>>

Init ==
    /\ Cache = [i \in NODE |-> [State |-> "I", Data |-> 1]]
    /\ Chan3 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ AuxData = 1

TypeOK ==
    /\ Cache \in [NODE -> CACHE]
    /\ Chan3 \in [NODE -> MSG]
    /\ AuxData \in DATA

NumRandSubsets == 5

TypeOKRand ==
    /\ Cache   \in RandomSubset(NumRandSubsets, [NODE -> CACHE])
    /\ Chan3   \in RandomSubset(NumRandSubsets, [NODE -> MSG])
    /\ AuxData \in RandomSubset(NumRandSubsets, DATA)

Symmetry == Permutations(NODE)

(* Define state transitions here, following the Murphi model *)
\* no need for fluent variables
\* SendReqS(i) ==
    \* /\ Cache[i].State = "I"
    \* /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

\* SendReqE(i) ==
    \* /\ (Cache[i].State = "I" \/ Cache[i].State = "S")
    \* /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

\* RecvReqS(i) ==
    \* /\ Chan1[i].Cmd = "ReqS"
    \* /\ CurCmd' = "ReqS"
    \* /\ CurPtr' = i
    \* /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
    \* /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    \* /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

\* RecvReqE(i) ==
\*     /\ CurCmd = "Empty"
\*     /\ Chan1[i].Cmd = "ReqE"
\*     /\ CurCmd' = "ReqE"
\*     /\ CurPtr' = i
\*     /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
\*     /\ InvSet' = [j \in NODE |-> ShrSet[j]]
\*     /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

\* SendInv(i) ==
    \* /\ Chan2[i].Cmd = "Empty"
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"]
    \* /\ UNCHANGED <<Cache, Chan3>>

SendInvAck(i) ==
    \* /\ Chan2[i].Cmd = "Inv"
    /\ Chan3[i].Cmd = "Empty"
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck", Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
    /\ Cache' = [Cache EXCEPT ![i].State = "I"]
    /\ UNCHANGED <<AuxData>>

RecvInvAck(i) ==
    /\ Chan3[i].Cmd = "InvAck"
    \* /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i].Cmd = "Empty"]
    \* /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    \* /\ IF ExGntd = TRUE
    \*    THEN /\ ExGntd' = FALSE
    \*         /\ MemData' = Chan3[i].Data
    \*    ELSE /\ UNCHANGED ExGntd
    \*         /\ UNCHANGED MemData
    /\ UNCHANGED <<Cache, AuxData>>

\* SendGntS(i) ==
    \* /\ CurCmd = "ReqS"
    \* /\ CurPtr = i
    \* /\ Chan2[i].Cmd = "Empty"
    \* /\ ExGntd = FALSE
    \* /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntS", Data |-> MemData]]
    \* /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    \* /\ CurCmd' = "Empty"
    \* /\ UNCHANGED <<Cache, Chan3>>

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
    \* /\ UNCHANGED <<Cache, Chan3>>

RecvGntS(i) ==
    \* /\ Chan2[i].Cmd = "GntS"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "S", Data |-> Chan2[i].Data]]
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan3>>

RecvGntE(i) ==
    \* /\ Chan2[i].Cmd = "GntE"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "E", Data |-> Chan2[i].Data]]
    \* /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan3, AuxData>>

Store(i, d) ==
    /\ Cache[i].State = "E"
    /\ Cache' = [Cache EXCEPT ![i].Data = d]
    /\ AuxData' = d
    /\ UNCHANGED <<Chan3>>

Next == 
    \E i \in NODE:
        \* \/ SendReqS(i)
        \* \/ SendReqE(i)
        \* \/ RecvReqS(i)
        \* \/ RecvReqE(i)
        \* \/ SendInv(i)
        \/ SendInvAck(i)
        \/ RecvInvAck(i)
        \* \/ SendGntS(i)
        \* \/ SendGntE(i)
        \/ RecvGntS(i)
        \/ RecvGntE(i)
        \/ \E d \in DATA: Store(i, d)

\* Invariant properties.
CtrlProp ==
    \A i, j \in NODE :
        i /= j =>
            /\ (Cache[i].State = "E" => Cache[j].State = "I")
            /\ (Cache[i].State = "S" => (Cache[j].State = "I" \/ Cache[j].State = "S"))

NextUnchanged == UNCHANGED vars

====
