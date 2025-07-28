---- MODULE MultiPaxos_MC_CTIGen_2775 ----
EXTENDS MultiPaxos_MC

InvStrengthened ==
    /\ Linearizability

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====