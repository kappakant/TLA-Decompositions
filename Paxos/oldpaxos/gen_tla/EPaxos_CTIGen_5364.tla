---- MODULE EPaxos_CTIGen_5364 ----
EXTENDS EPaxos

InvStrengthened ==
    /\ H_Consistency

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====