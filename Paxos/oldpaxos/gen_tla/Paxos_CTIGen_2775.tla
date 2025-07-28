---- MODULE Paxos_CTIGen_2775 ----
EXTENDS Paxos

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====