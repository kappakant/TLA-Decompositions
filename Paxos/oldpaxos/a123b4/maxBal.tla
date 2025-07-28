CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
None == CHOOSE v : v \notin Value

VARIABLE maxBal

vars == <<maxBal>>

TypeOK == maxBal \in [Acceptor -> Ballot \cup {-1}]
