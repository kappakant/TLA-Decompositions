---- MODULE paxos_epr_CTIGen_6742 ----
EXTENDS paxos_epr

InvStrengthened ==
    /\ Safety

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====