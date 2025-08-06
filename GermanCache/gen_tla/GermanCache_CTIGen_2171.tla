---- MODULE GermanCache_CTIGen_2171 ----
EXTENDS GermanCache

Inv1592_1_0 == \A VARI \in NODE : \E VARJ \in NODE : (CurCmd = "ReqE") \/ ((CurPtr = VARI))
Inv1682_1_0 == \A VARI \in NODE : \E VARJ \in NODE : (CurPtr = VARI) \/ ((ExGntd))
Inv1937_1_0 == \A VARI \in NODE : \E VARJ \in NODE : (InvSet[VARI]) \/ (~(ExGntd))
Inv1729_1_0 == \A VARI \in NODE : \E VARJ \in NODE : (CurPtr = VARI) \/ (~(ExGntd))
InvStrengthened ==
    /\ DataProp
    /\ Inv1592_1_0
    /\ Inv1682_1_0
    /\ Inv1937_1_0
    /\ Inv1729_1_0

IndCand ==
    /\ TypeOKRand
    /\ InvStrengthened
====