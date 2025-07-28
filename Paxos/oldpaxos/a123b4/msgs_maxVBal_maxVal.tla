CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
None == CHOOSE v : v \notin Value

\* messages encodes maxVBal and maxVal into mbal and mval respectivy 
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLE msgs, maxVBal, maxVal

vars == <<maxVBal, maxVal, msgs>>

TypeOK == /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message


NumRandSubsets == 35

kNumSubsets == 18
nAvgSubsetSize == 4

TypeOKRandom == 
    /\ maxVBal \in RandomSubset(NumRandSubsets, [Acceptor -> Ballot \cup {-1}])
    /\ maxVal \in RandomSubset(NumRandSubsets, [Acceptor -> Value \cup {None}])
    /\ msgs \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, Message)

Send(m) == msgs' = msgs \cup {m}

\* maybe syntactically wrong here
msg1a(a,b) == \E m \in msgs : m.type= "1b" /\ m.bal = a
msg1b(a,b,mb,v) == \E m \in msgs : m.type= "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = mb /\ m.mval = v
msg2a(b,v) == \E m \in msgs : m.type= "2a" /\ m.bal = b /\ m.val = v
msg2b(a,b,v) == \E m \in msgs : m.type= "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxVal>>

\* Send encodes a maxVBal and maxVal value into msgs.
Phase1b(a) == /\ \E m \in msgs : 
                  /\ m.type = "1a"
                  \* hmm, could be equivalent to splitting "guard" clause variable
                  \* /\ m.bal > maxBal[a]
                  \* /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
              /\ UNCHANGED <<maxVBal, maxVal>>

Q1b(Q, b) ==
    {m \in msgs : /\ m.type = "1b"
                  /\ m.acc \in Q
                  /\ m.bal = b}

Q1bv(Q, b) == {m \in Q1b(Q,b) : m.mbal \geq 0}
    
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in Q1b(Q,b) : m.acc = a 
        /\ \/ Q1bv(Q, b) = {}
           \/ \E m \in Q1bv(Q, b) : 
                /\ m.mval = v
                /\ \A mm \in Q1bv(Q, b) : m.mbal \geq mm.mbal 
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxVBal, maxVal>>


Phase2b(a) == \E m \in msgs : /\ m.type = "2a"
                              /\ m.bal \geq maxBal[a]
                              \* /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
                              /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                              /\ Send([type |-> "2b", acc |-> a,
                                       bal |-> m.bal, val |-> m.val]) 

Next == 
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E b \in Ballot : \E v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase1b(a) 
    \/ \E a \in Acceptor : Phase2b(a)

Spec == Init /\ [][Next]_vars

votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum : 
      \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
   
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) : 
      /\ (c /= -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

Inv == 
    /\ Cardinality(chosen) <= 1

Ind ==
    /\ TypeOKRandom
    /\ Inv

Symmetry == Permutations(Acceptor) \cup Permutations(Value)

NextUnchanged == UNCHANGED vars

\* do I really need this?
\* K == \A ACCI \in Acceptor : (\E m \in msgs : m.bal >= maxBal[ACCI]) \/ ((maxVBal[ACCI] = -1) /\ (TRUE))




