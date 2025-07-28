---- MODULE EPaxos_CTIGen_6742 ----
EXTENDS EPaxos

InvStrengthened ==
    /\ H_Consistency

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====