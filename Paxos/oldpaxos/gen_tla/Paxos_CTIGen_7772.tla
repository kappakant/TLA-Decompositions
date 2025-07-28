---- MODULE Paxos_CTIGen_7772 ----
EXTENDS Paxos

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====