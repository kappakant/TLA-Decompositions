--------------------------- MODULE decision_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Value, Quorum

VARIABLES decision

vars == <<decision>>

Round == {0,1,2,3}

CandSep ==
TRUE

None == -.(1)

Decide(n,r,v,Q) ==
/\ decision' = (decision \cup {<<n,r,v>>})
/\ UNCHANGED<<>>
/\ CandSep'

Init ==
/\ decision = {}

NumRandSubsets == 5

kNumSubsets == 3

nAvgSubsetSize == 2

TypeOKRandom ==
/\ (decision \in RandomSubset(NumRandSubsets,SUBSET((Node \X Round \X Value))))

Next ==
\/ (\E n \in Node, v \in Value, r \in Round, Q \in Quorum : Decide(n,v,r,Q))

Spec == (Init /\ [][Next]_vars)

Symmetry == (Permutations(Node) \cup Permutations(Value))

NextUnchanged == UNCHANGED vars

Safety == (\A n1,n2 \in Node, r1,r2 \in Round, v1,v2 \in Value : (((<<n1,r1,v1>> \in decision) /\ (<<n2,r2,v2>> \in decision)) => v1 = v2))
=============================================================================
