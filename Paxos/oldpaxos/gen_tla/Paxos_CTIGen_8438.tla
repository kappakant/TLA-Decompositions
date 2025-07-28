---- MODULE Paxos_CTIGen_8438 ----
EXTENDS Paxos

Inv4612_1_0 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2b(ACCI,BALJ,VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv1170_1_1 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALI)) \/ (~(msg2a(BALI,VALI)))
Inv4101_1_2 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2a(BALI,VALI)) \/ (~(ChosenAt(BALI, VALI)))
Inv5926_1_3 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : ~(maxBal[ACCI] < BALI) \/ (~(maxVBal[ACCI] = BALI))
InvStrengthened ==
    /\ Inv
    /\ Inv4612_1_0
    /\ Inv1170_1_1
    /\ Inv4101_1_2
    /\ Inv5926_1_3

IndCand ==
    /\ TypeOKRandom
    /\ InvStrengthened
====