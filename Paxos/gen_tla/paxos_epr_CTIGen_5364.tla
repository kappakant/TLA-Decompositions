---- MODULE paxos_epr_CTIGen_5364 ----
EXTENDS paxos_epr

InvStrengthened ==
    /\ Safety

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====