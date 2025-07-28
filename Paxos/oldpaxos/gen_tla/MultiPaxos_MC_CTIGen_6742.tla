---- MODULE MultiPaxos_MC_CTIGen_6742 ----
EXTENDS MultiPaxos_MC

InvStrengthened ==
    /\ Linearizability

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====