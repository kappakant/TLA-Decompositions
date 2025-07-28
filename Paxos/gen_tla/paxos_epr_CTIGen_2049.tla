---- MODULE paxos_epr_CTIGen_2049 ----
EXTENDS paxos_epr

InvStrengthened ==
    /\ Safety

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====