-------------------------------- MODULE decision -------------------------------
EXTENDS Integers, FiniteSets, TLC, Randomization

CONSTANT Value, Node, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Node
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
Round == {0, 1, 2, 3}

None == -1

VARIABLE decision

vars == <<decision>>

Decide(n, r, v, Q) == 
    decision' = decision \cup {<<n, r, v>>}

Init == decision = {}

NumRandSubsets == 5

kNumSubsets == 3
nAvgSubsetSize == 2

TypeOKRandom ==
    /\ decision \in RandomSubset(NumRandSubsets, SUBSET(Node \X Round \X Value))

Next == 
    \/ \E n \in Node, v \in Value, r \in Round, Q \in Quorum : Decide(n,v,r,Q)

Spec == Init /\ [][Next]_vars

Symmetry == Permutations(Node) \cup Permutations(Value)

NextUnchanged == UNCHANGED vars

Safety == 
    \A n1,n2 \in Node, r1,r2 \in Round, v1,v2 \in Value : 
        (<<n1,r1,v1>> \in decision /\ <<n2,r2,v2>> \in decision) => v1 = v2

============================================================================
