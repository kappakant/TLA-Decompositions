---- MODULE Paxos_CTIGen_6742 ----
EXTENDS Paxos

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====