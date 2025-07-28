---- MODULE paxos_epr_CTIGen_7362 ----
EXTENDS paxos_epr

InvStrengthened ==
    /\ Safety

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====