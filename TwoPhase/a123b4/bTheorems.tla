----------------------------- MODULE bTheorems -----------------------------
EXTENDS tmPrepared_hist

\* module B with respect to carini, <A>C1||B<R> with respect to assume-guarantee reasoning

\* Init /\ TRUE => I1
\* I1 /\ Next /\ TRUE /\ TRUE' => I1'
\* I1' => CandSep

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
                  PROVE TypeOK /\ CandSep /\ Inv1
                  BY DEF I1
    
    <1>a TypeOK BY <1>1 DEF Init, TypeOK
    <1>b CandSep BY <1>1 DEF Init, CandSep
    <1>c Inv1 BY <1>1 DEF Init, Inv1
     
    <1>. QED BY <1>a, <1>b, <1>c

THEOREM I1Induction ==
    I1 /\ Next => I1'
    <1>1 SUFFICES ASSUME TypeOK /\ CandSep /\ Inv1, NEW rmi \in RMs, 
                         RcvPrepare(rmi) \/ SndCommit(rmi)
                  PROVE  TypeOK' /\ CandSep' /\ Inv1'
                  BY DEF I1, Next
                  
    <1>a TypeOK' BY <1>1 DEF TypeOK, RcvPrepare, SndCommit
    
    \* if Fluent7_0'[var0], then in RcvPrepare, it was true in the previous state and var1 are all unchanged. Thus true
    \* In the SndCommit state, then tmPrepared = RMs so by Inv1, must be true.
    \* Must assume new rmj, rmk in <2>1 instead of above, for some reason?
    <1>b \A var0 \in RMs: \A var1 \in RMs : Fluent7_0'[var0] => Fluent6_0'[var1]
        <2>1 SUFFICES ASSUME NEW rmj \in RMs, NEW rmk \in RMs,
                                 Fluent7_0'[rmj]
                      PROVE      Fluent6_0'[rmk]
                      OBVIOUS
                      
        <2>a CASE RcvPrepare(rmi)
            <3>1 Fluent7_0' = Fluent7_0 BY <2>a DEF RcvPrepare
            <3>2 Fluent7_0[rmj] BY <2>1, <3>1
            <3>3 Fluent6_0[rmk] BY <3>2, <1>1 DEF CandSep
            <3>4 Fluent6_0' = [Fluent6_0 EXCEPT ![rmi] = TRUE] BY <2>a DEF RcvPrepare
            <3>5 Fluent6_0'[rmk] BY <2>a, <3>3, <3>4
            
            <3>. QED BY <3>5
            
        <2>b CASE SndCommit(rmi)
            <3>1 tmPrepared = RMs BY <2>b DEF SndCommit
            <3>2 Fluent6_0[rmk] BY <1>1, <3>1 DEF Inv1
            <3>3 Fluent6_0' = Fluent6_0 BY <2>b DEF SndCommit
            <3>4 Fluent6_0'[rmk] BY <3>2, <3>3
            
            <3>. QED BY <3>4
            
        <2>. QED BY <1>1, <2>a, <2>b
    
    <1>c \A rm1 \in RMs : Fluent6_0'[rm1] \/ ~(tmPrepared' = tmPrepared' \cup {rm1})
        \* material implication as a possibility
        <2>1 SUFFICES ASSUME NEW rmj \in RMs
                      PROVE  Fluent6_0'[rmj] \/ ~(tmPrepared' = tmPrepared' \cup {rmj})
                      OBVIOUS
        
        <2>a CASE RcvPrepare(rmi)
            <3>1 SUFFICES ASSUME tmPrepared' = tmPrepared' \cup {rmj}
                          PROVE Fluent6_0'[rmj]
                          OBVIOUS
                          
            <3>2 rmj \in tmPrepared' BY <3>1
            <3>3 tmPrepared' = (tmPrepared \cup {rmi}) BY <2>a DEF RcvPrepare
            <3>4 rmj = rmi \/ rmj # rmi OBVIOUS
            
            <3>a CASE rmj = rmi
                <4>1 Fluent6_0' = [Fluent6_0 EXCEPT ![rmj] = TRUE] BY <2>a, <3>a DEF RcvPrepare
                <4>2 Fluent6_0'[rmj] BY <1>1, <4>1 DEF TypeOK
                
                <4>. QED BY <4>2
            
            <3>b CASE rmj # rmi
                <4>1 rmj \in tmPrepared BY <3>2, <3>3, <3>b
                <4>2 (tmPrepared = tmPrepared \cup {rmj}) BY <4>1
                <4>3 Fluent6_0[rmj] BY <1>1, <4>2 DEF Inv1
                <4>4 Fluent6_0'[rmj] BY <2>a, <4>3 DEF RcvPrepare
                
                <4>. QED BY <4>4
            
            <3>. QED BY <3>a, <3>b
        
        <2>b CASE SndCommit(rmi)
            <3>1 tmPrepared' = tmPrepared' \cup {rmj} BY <2>b DEF SndCommit
            <3>2 tmPrepared = tmPrepared \cup {rmj} BY <2>b DEF SndCommit
            <3>3 Fluent6_0[rmj] BY <1>1, <3>2 DEF Inv1
            <3>4 Fluent6_0'[rmj] BY <2>b, <3>3 DEF SndCommit
            <3>. QED BY <3>4
        
        <2>. QED BY <1>1, <2>a, <2>b 
    
    <1>. QED BY <1>a, <1>b, <1>c DEF TypeOK, CandSep, Inv1
    
THEOREM I1Safety ==
    I1 => CandSep BY DEF I1
=============================================================================
\* Modification History
\* Last modified Tue Jul 08 16:43:11 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:08:21 EDT 2025 by johnnguyen
