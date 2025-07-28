---- MODULE Paxos_CTIGen_3418 ----
EXTENDS Paxos

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====