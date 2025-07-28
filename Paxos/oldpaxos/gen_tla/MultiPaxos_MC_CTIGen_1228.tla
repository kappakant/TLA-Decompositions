---- MODULE MultiPaxos_MC_CTIGen_1228 ----
EXTENDS MultiPaxos_MC

InvStrengthened ==
    /\ Linearizability

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====