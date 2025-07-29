--------------------------- MODULE a_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

VARIABLES Chan2, ExGntd, Chan3, MemData, AuxData, Cache

vars == <<Chan2, ExGntd, Chan3, MemData, AuxData, Cache>>

CandSep ==
TRUE

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == (CACHE_STATE \X DATA)

MSG == (MSG_CMD \X DATA)

Init ==
/\ Cache = [i \in NODE |-> <<"I",1>>]
/\ Chan2 = [i \in NODE |-> <<"Empty",1>>]
/\ Chan3 = [i \in NODE |-> <<"Empty",1>>]
/\ ExGntd = FALSE
/\ MemData = 1
/\ AuxData = 1

TypeOK ==
/\ (Cache \in [NODE -> CACHE])
/\ (Chan2 \in [NODE -> MSG])
/\ (Chan3 \in [NODE -> MSG])
/\ (ExGntd \in BOOLEAN)
/\ (MemData \in DATA)
/\ (AuxData \in DATA)

NumRandSubsets == 5

TypeOKRand ==
/\ (Cache \in RandomSubset(NumRandSubsets,[NODE -> CACHE]))
/\ (Chan2 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (Chan3 \in RandomSubset(NumRandSubsets,[NODE -> MSG]))
/\ (ExGntd \in RandomSubset(NumRandSubsets,BOOLEAN))
/\ (MemData \in RandomSubset(NumRandSubsets,DATA))
/\ (AuxData \in RandomSubset(NumRandSubsets,DATA))

Symmetry == Permutations(NODE)

SendReqS(i) ==
/\ Cache[i][1] = "I"
/\ UNCHANGED <<Cache,Chan2,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendReqEA(i) ==
/\ Cache[i][1] = "I"
/\ UNCHANGED <<Cache,Chan2,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendReqEB(i) ==
/\ Cache[i][1] = "S"
/\ UNCHANGED <<Cache,Chan2,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInvA(i) ==
/\ Chan2[i][1] = "Empty"
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Inv",Chan2[i][2]>>]
/\ UNCHANGED <<Cache,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInvB(i) ==
/\ Chan2[i][1] = "Empty"
/\ ExGntd = TRUE
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Inv",Chan2[i][2]>>]
/\ UNCHANGED <<Cache,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInvAckA(i) ==
/\ Cache[i][1] = "E"
/\ Chan2[i][1] = "Inv"
/\ Chan3[i][1] = "Empty"
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Empty",Chan2[i][2]>>]
/\ Chan3' = [Chan3 EXCEPT![i] = <<"InvAck",Cache[i][2]>>]
/\ Cache' = [Cache EXCEPT![i] = <<"I",Cache[i][2]>>]
/\ UNCHANGED <<ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendInvAckB(i) ==
/\ Cache[i][1] /= "E"
/\ Chan2[i][1] = "Inv"
/\ Chan3[i][1] = "Empty"
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Empty",Chan2[i][2]>>]
/\ Chan3' = [Chan3 EXCEPT![i] = <<"InvAck",Chan3[i][2]>>]
/\ UNCHANGED <<Cache,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvInvAckA(i) ==
/\ Chan3[i][1] = "InvAck"
/\ Chan3' = [Chan3 EXCEPT![i] = <<"Empty",Chan3[i][2]>>]
/\ ExGntd = TRUE
/\ ExGntd' = FALSE
/\ MemData' = Chan3[i][2]
/\ UNCHANGED <<Cache,Chan2,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvInvAckB(i) ==
/\ Chan3[i][1] = "InvAck"
/\ Chan3' = [Chan3 EXCEPT![i] = <<"Empty",Chan3[i][2]>>]
/\ ExGntd = FALSE
/\ UNCHANGED <<Cache,Chan2,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendGntS(i) ==
/\ Chan2[i][1] = "Empty"
/\ ExGntd = FALSE
/\ Chan2' = [Chan2 EXCEPT![i] = <<"GntS",MemData>>]
/\ UNCHANGED <<Cache,Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

SendGntE(i) ==
/\ Chan2[i][1] = "Empty"
/\ ExGntd = FALSE
/\ Chan2' = [Chan2 EXCEPT![i] = <<"GntE",MemData>>]
/\ ExGntd' = TRUE
/\ UNCHANGED <<Cache,Chan3,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvGntS(i) ==
/\ Chan2[i][1] = "GntS"
/\ Cache' = [Cache EXCEPT![i] = <<"S",Chan2[i][2]>>]
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Empty",Chan2[i][2]>>]
/\ UNCHANGED <<Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

RecvGntE(i) ==
/\ Chan2[i][1] = "GntE"
/\ Cache' = [Cache EXCEPT![i] = <<"E",Chan2[i][2]>>]
/\ Chan2' = [Chan2 EXCEPT![i] = <<"Empty",Chan2[i][2]>>]
/\ UNCHANGED <<Chan3,ExGntd,MemData,AuxData>>
/\ UNCHANGED<<>>
/\ CandSep'

Store(i,d) ==
/\ Cache[i][1] = "E"
/\ Cache' = [Cache EXCEPT![i] = <<Cache[i][1],d>>]
/\ AuxData' = d
/\ UNCHANGED <<Chan2,Chan3,ExGntd,MemData>>
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\E i \in NODE :
\/ SendReqS(i)
\/ SendReqEA(i)
\/ SendReqEB(i)
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
\/ (\E d \in DATA : Store(i,d))

Spec == ((Init /\ TypeOK) /\ [][Next]_vars)

CtrlProp == (\A i,j \in NODE : (i /= j => ((Cache[i][1] = "E" => Cache[j][1] = "I") /\ (Cache[i][1] = "S" => (Cache[j][1] /= "I" => Cache[j][1] = "S")))))

DataProp ==
/\ (ExGntd = FALSE => MemData = AuxData)
/\ (\A i \in NODE : (Cache[i][1] /= "I" => Cache[i][2] = AuxData))

Inv ==
/\ TypeOK
/\ CtrlProp
/\ DataProp

NextUnchanged == UNCHANGED vars
=============================================================================
