----------------------------- MODULE bTheorems -----------------------------
CONSTANT RMs

VARIABLES Fluent6_0, Fluent7_0, tmPrepared
b == INSTANCE tmPrepared_hist WITH RMs <- RMs, tmPrepared <- tmPrepared,
                                   Fluent6_0 <- Fluent6_0, 
                                   Fluent7_0 <- Fluent7_0 

\* module B with respect to carini, <A>C1||B<R> with respect to assume-guarantee reasoning

\* Init /\ TRUE => I1
\* I1 /\ Next /\ TRUE /\ TRUE' => I1'
\* I1' => CandSep

CandSep == b!CandSep
Inv1 == b!Inv10_1_0_def

Init == b!Init
I1   == b!IndAuto
Next == b!Next

\* IndAuto ==                                                                                                                                                                                                                                                                       
\* /\ CandSep                                                                                                                                                                                                                                                                       
\* /\ Inv10_1_0_def       

\* CandSep ==                                                                                                                                                                                                             
\* /\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var0]) => (Fluent6_0[var1])   

\* Inv1 == 
\* \A rmi \in RMs : \A rmj \in RMs : (Fluent6_0[rmi]) \/ (~(tmPrepared = tmPrepared \cup {rmi}))   

THEOREM I1Initialization == 
    Init => I1
    <1>1 SUFFICES ASSUME Init
                  PROVE CandSep /\ Inv1
                  BY DEF I1, CandSep, Inv1, b!IndAuto
    
    <1>a CandSep BY <1>1 DEF Init, b!Init, CandSep, b!CandSep
    <1>b Inv1 BY <1>1 DEF Init, b!Init, Inv1, b!Inv10_1_0_def
     
    <1>. QED BY <1>a, <1>b

THEOREM I1Induction ==
    I1 /\ Next => I1'
    <1> SUFFICES ASSUME I1 /\ Next
                 PROVE I1'
                 OBVIOUS
    
    <1>. QED
    
THEOREM I1Safety ==
    I1 => CandSep BY DEF I1, b!IndAuto, CandSep
=============================================================================
\* Modification History
\* Last modified Wed Jul 02 01:07:06 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:08:21 EDT 2025 by johnnguyen
