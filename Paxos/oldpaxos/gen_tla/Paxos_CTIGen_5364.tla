---- MODULE Paxos_CTIGen_5364 ----
EXTENDS Paxos

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====