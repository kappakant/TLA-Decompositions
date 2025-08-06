---- MODULE ab_CTIGen_6742 ----
EXTENDS ab

InvStrengthened ==
    /\ Inv

IndCand ==
    /\ TypeOKRand
    /\ InvStrengthened
====