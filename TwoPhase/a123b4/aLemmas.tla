------------------------------ MODULE aLemmas ------------------------------
EXTENDS rmState_msgs_tmState_hist

\* Proof left as an exercise for the reader
THEOREM I2TypeOKInduction ==
    I2 /\ Next /\ CandSep /\ CandSep' => TypeOK'
    <1> SUFFICES ASSUME I2 /\ CandSep /\ CandSep', NEW rmi \in RMs,
                        SndPrepare(rmi) \/ RcvPrepare(rmi) \/ SndCommit(rmi) \/ 
                        RcvCommit(rmi) \/ SndAbort(rmi) \/ RcvAbort(rmi) \/ SilentAbort(rmi)
                 PROVE TypeOK'
                 BY DEF Next
                 
    <1>a (rmState' \in [RMs -> {"working","prepared","committed","aborted"}])
    
    <1>b (msgs' \in SUBSET(Message))
    
    <1>c (tmState' \in {"init","committed","aborted"})
    
    <1>d Fluent6_0' \in [RMs -> BOOLEAN]
    
    <1>e Fluent7_0' \in [RMs -> BOOLEAN]
    
    <1>. QED BY <1>a, <1>b , <1>c, <1>d, <1>e DEF TypeOK

THEOREM I2ConsistentInduction ==
    I2 /\ Next /\ CandSep /\ CandSep' => Consistent'
    <1> SUFFICES ASSUME I2 /\ CandSep /\ CandSep', 
                        NEW rmi \in RMs, NEW rmj \in RMs, rmState'[rmj] = "aborted", NEW rmk \in RMs,
                        SndPrepare(rmi) \/ RcvPrepare(rmi) \/ SndCommit(rmi) \/ 
                        RcvCommit(rmi) \/ SndAbort(rmi) \/ RcvAbort(rmi) \/ SilentAbort(rmi)
                 PROVE  ~rmState'[rmk] = "committed"
                 BY DEF Next, Consistent
                 
    <1>a CASE SndPrepare(rmi)
        
        
    <1>. QED
=============================================================================
\* Modification History
\* Last modified Tue Jul 08 17:44:42 EDT 2025 by johnnguyen
\* Created Tue Jul 01 10:12:09 EDT 2025 by johnnguyen
