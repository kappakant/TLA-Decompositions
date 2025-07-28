---- MODULE MultiPaxos_MC_CTIGen_7772 ----
EXTENDS MultiPaxos_MC

InvStrengthened ==
    /\ Linearizability

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====