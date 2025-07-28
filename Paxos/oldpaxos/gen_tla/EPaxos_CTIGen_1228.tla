---- MODULE EPaxos_CTIGen_1228 ----
EXTENDS EPaxos

InvStrengthened ==
    /\ H_Consistency

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====