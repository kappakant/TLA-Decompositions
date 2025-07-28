----------------------------- MODULE aTheorems -----------------------------
EXTENDS aLemmas
  
\* module A with respect to carini, <R>B||C2<G> with respect to assume-guarantee reasoning

\* Init /\ A => In
\* In /\ Next /\ A /\ A' => I'
\* In => Consistent

THEOREM I2Initialization ==
    Init /\ CandSep => I2
    <1> SUFFICES ASSUME Init /\ CandSep
                 PROVE  I2
                 OBVIOUS
    
    <1>. QED

THEOREM I2Induction ==
    I2 /\ Next /\ CandSep /\ CandSep' => I2'
    <1> SUFFICES ASSUME I2 /\ CandSep /\ CandSep', NEW rmi \in RMs,
                        SndPrepare(rmi) \/ RcvPrepare(rmi) \/ SndCommit(rmi) \/ 
                        RcvCommit(rmi) \/ SndAbort(rmi) \/ RcvAbort(rmi) \/ SilentAbort(rmi)
                 PROVE  TypeOK' /\ Consistent' /\ 
                        Inv1' /\ Inv2' /\ Inv3' /\ Inv4' /\ 
                        Inv5' /\ Inv6' /\ Inv7' /\ Inv8' /\ Inv9'
                 BY DEF I2, Next
    
    <1>a TypeOK' BY I2TypeOKInduction
    <1>b Consistent' BY I2ConsistentInduction
    <1>c Inv1' BY I2Inv1Induction
    <1>d Inv2' BY I2Inv2Induction
    <1>e Inv3' BY I2Inv3Induction
    <1>f Inv4' BY I2Inv4Induction
    <1>g Inv5' BY I2Inv5Induction
    <1>h Inv6' BY I2Inv6Induction
    <1>i Inv7' BY I2Inv7Induction
    <1>j Inv8' BY I2Inv8Induction
    <1>k Inv9' BY I2Inv9Induction
    
    <1>. QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k
    
THEOREM I2Safety ==
    I2 => Consistent BY DEF I2


=============================================================================
\* Modification History
\* Last modified Tue Jul 08 16:59:08 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:07:51 EDT 2025 by johnnguyen
