---- MODULE paxos_epr_CTIGen_3418 ----
EXTENDS paxos_epr

InvStrengthened ==
    /\ Safety

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====