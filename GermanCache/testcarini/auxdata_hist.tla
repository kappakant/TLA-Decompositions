--------------------------- MODULE auxdata_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS NODE, DATA

VARIABLES AuxData

vars == <<AuxData>>

CandSep ==
TRUE

CACHE_STATE == {"I","S","E"}

MSG_CMD == {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE"}

CACHE == [State : CACHE_STATE,Data : DATA]

MSG == [Cmd : MSG_CMD,Data : DATA]

Init ==
/\ AuxData = 1

TypeOK ==
/\ (AuxData \in DATA)

NumRandSubsets == 5

TypeOKRand ==
/\ (AuxData \in RandomSubset(NumRandSubsets,DATA))

Symmetry == Permutations(NODE)

Store(i,d) ==
/\ AuxData' = d
/\ UNCHANGED<<>>

StoreAction == (TRUE /\ (\E i \in NODE, d \in DATA : Store(i,d)))

NextOld ==
\/ StoreAction

Next ==
\E i \in NODE :
\/ (\E d \in DATA : Store(i,d))

NextUnchanged == UNCHANGED vars
=============================================================================
