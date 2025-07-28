---- MODULE EPaxos_CTIGen_5192 ----
EXTENDS EPaxos

InvStrengthened ==
    /\ H_Consistency

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====