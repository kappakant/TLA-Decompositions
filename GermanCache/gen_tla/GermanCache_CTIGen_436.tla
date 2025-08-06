---- MODULE GermanCache_CTIGen_436 ----
EXTENDS GermanCache

Inv1592_1_0 == \A VARI \in NODE : \E VARJ \in NODE : (CurCmd = "ReqE") \/ ((CurPtr = VARI))
InvStrengthened ==
    /\ DataProp
    /\ Inv1592_1_0

IndCand ==
    /\ TypeOKRand
    /\ InvStrengthened
====