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

Init == b!Init
I1   == b!IndAuto
Next == b!Next

\* IndAuto ==                                                                                                                                                                                                                                                                       
\* /\ CandSep                                                                                                                                                                                                                                                                       
\* /\ Inv10_1_0_def        

THEOREM I1Initialization == 
    Init => I1

THEOREM I1Induction ==
    I1 /\ Next => I1'
    
THEOREM I1Safety ==
    I1 => CandSep BY DEF I1, b!IndAuto, CandSep
=============================================================================
\* Modification History
\* Last modified Tue Jul 01 10:37:56 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:08:21 EDT 2025 by johnnguyen
