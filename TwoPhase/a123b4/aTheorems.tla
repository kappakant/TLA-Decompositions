----------------------------- MODULE aTheorems -----------------------------
EXTENDS aLemmas

CONSTANT RMs

VARIABLES Fluent6_0, msgs, tmState, Fluent7_0, rmState
a == INSTANCE rmState_msgs_tmState_hist WITH RMs <- RMs, 
                                             Fluent6_0 <- Fluent6_0, 
                                             msgs <- msgs, tmState <- tmState, 
                                             Fluent7_0 <- Fluent7_0, rmState <- rmState     
\* module A with respect to carini, <R>B||C2<G> with respect to assume-guarantee reasoning

\* Init /\ A => In
\* In /\ Next /\ A /\ A' => I'
\* In => Consistent
Consistent == a!Consistent  

A == \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var0]) => (Fluent6_0[var1])       

Init == a!Init
I2   == a!IndAuto
Next == a!Next

\* lol, good luck with this
\* IndAuto ==
\* /\ Consistent
\* /\ Inv462_1_0_def
\* /\ Inv482_1_1_def
\* /\ Inv645_1_2_def
\* /\ Inv34_1_3_def
\* /\ Inv523_1_4_def
\* /\ Inv637_1_5_def
\* /\ Inv213_1_0_def
\* /\ Inv647_1_1_def
\* /\ Inv610_1_2_def
\* /\ Inv563_1_3_def

THEOREM I2Initialization ==
    Init /\ A => I2
    <1> SUFFICES ASSUME Init /\ A
                 PROVE  I2
                 OBVIOUS
    
    <1>. QED

THEOREM I2Induction ==
    I2 /\ Next /\ A /\ A' => I2'
    <1> SUFFICES ASSUME I2 /\ Next /\ A /\ A'
                 PROVE I2
                 OBVIOUS
    
    <1>. QED
    
THEOREM I2Safety ==
    I2 => Consistent BY DEF I2, a!IndAuto, Consistent


=============================================================================
\* Modification History
\* Last modified Tue Jul 01 10:32:06 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:07:51 EDT 2025 by johnnguyen
