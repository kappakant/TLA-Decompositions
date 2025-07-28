--------------------------- MODULE rest_hist ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Value, Quorum

VARIABLES proposal, left_rnd, one_b, one_a, one_b_max_vote, vote

vars == <<proposal, left_rnd, one_b, one_a, one_b_max_vote, vote>>

Round == {0,1,2}

CandSep ==
TRUE

None == -.(1)

Send1a(b) ==
/\ one_a' = (one_a \cup {b})
/\ UNCHANGED <<one_b_max_vote,one_b,left_rnd,proposal,vote>>
/\ UNCHANGED<<>>

JoinRound(n,r) ==
/\ (\E maxr \in (Round \cup {None}), maxv \in Value : ((r \in one_a) /\ (<<n,r>> \notin left_rnd) /\ ((maxr = None /\ (\A rx \in Round, vx \in Value : ~((r > rx /\ (<<n,rx,vx>> \in vote))))) \/ (maxr /= None /\ (r > maxr /\ (<<n,maxr,maxv>> \in vote)) /\ (\A mr \in Round, v \in Value : ((r > mr /\ (<<n,mr,v>> \in vote)) => mr <= maxr)))) /\ one_b_max_vote' = (one_b_max_vote \cup {<<n,r,maxr,maxv>>}) /\ one_b' = (one_b \cup {<<n,r>>}) /\ left_rnd' = left_rnd /\ UNCHANGED <<one_a,proposal,vote>>))
/\ UNCHANGED<<>>

Propose(r,Q) ==
/\ (\E maxr \in (Round \cup {None}), v \in Value : (((maxr = None /\ (\A n \in Node, mr \in Round, mv \in Value : ~((((n \in Q) /\ r > mr) /\ (<<n,mr,mv>> \in vote))))) \/ (maxr /= None /\ (\E n \in Node : (((n \in Q) /\ ~(r <= maxr)) /\ (<<n,maxr,v>> \in vote))) /\ (\A n \in Node, mr \in Round, mv \in Value : ((((n \in Q) /\ ~(r <= mr)) /\ (<<n,maxr,mv>> \in vote)) => mr <= maxr)))) /\ (\A mv \in Value : (<<r,mv>> \notin proposal)) /\ (\A n \in Node : ((n \in Q) => (<<n,r>> \in one_b))) /\ proposal' = (proposal \cup {<<r,v>>}) /\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,vote>>))
/\ UNCHANGED<<>>

CastVote(n,v,r) ==
/\ r /= None
/\ (<<n,r>> \notin left_rnd)
/\ (<<r,v>> \in proposal)
/\ vote' = (vote \cup {<<n,r,v>>})
/\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,proposal>>
/\ UNCHANGED<<>>

Decide(n,r,v,Q) ==
/\ r /= None
/\ (\A m \in Node : ((m \in Q) => (<<m,r,v>> \in vote)))
/\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,proposal,vote>>
/\ UNCHANGED<<>>

Init ==
/\ one_a = {}
/\ one_b_max_vote = {}
/\ one_b = {}
/\ left_rnd = {}
/\ proposal = {}
/\ vote = {}

NumRandSubsets == 5

kNumSubsets == 3

nAvgSubsetSize == 2

TypeOKRandom ==
/\ (one_a \in RandomSubset(NumRandSubsets,SUBSET(Round)))
/\ (one_b_max_vote \in RandomSubset(NumRandSubsets,SUBSET((Node \X Round \X Round \X Value))))
/\ (one_b \in RandomSetOfSubsets(kNumSubsets,nAvgSubsetSize,SUBSET((Node \X Round))))
/\ (left_rnd \in RandomSubset(NumRandSubsets,SUBSET((Node \X Round))))
/\ (proposal \in RandomSubset(NumRandSubsets,SUBSET((Round \X Value))))
/\ (vote \in RandomSubset(NumRandSubsets,SUBSET((Node \X Round \X Value))))

Next ==
\/ (\E b \in Round : Send1a(b))
\/ (\E n \in Node, r \in Round : JoinRound(n,r))
\/ (\E r \in Round, Q \in Quorum : Propose(r,Q))
\/ (\E n \in Node, v \in Value, r \in Round : CastVote(n,v,r))
\/ (\E n \in Node, v \in Value, r \in Round, Q \in Quorum : Decide(n,v,r,Q))

Spec == (Init /\ [][Next]_vars)

Symmetry == (Permutations(Node) \cup Permutations(Value))

NextUnchanged == UNCHANGED vars
=============================================================================
