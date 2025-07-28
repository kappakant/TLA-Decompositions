---- MODULE EPaxos_CTIGen_2775 ----
EXTENDS EPaxos

InvStrengthened ==
    /\ H_Consistency

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====