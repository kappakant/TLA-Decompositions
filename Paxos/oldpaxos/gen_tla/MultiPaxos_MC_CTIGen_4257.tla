---- MODULE MultiPaxos_MC_CTIGen_4257 ----
EXTENDS MultiPaxos_MC

InvStrengthened ==
    /\ Linearizability

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====