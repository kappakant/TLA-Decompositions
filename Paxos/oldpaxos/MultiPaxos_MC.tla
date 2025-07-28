(**********************************************************************************)
(* MultiPaxos in state machine replication (SMR) style with write/read commands   *)
(* on a single key. Please refer to the detailed comments in PlusCal code to see  *)
(* how this spec closely models a practical SMR log replication system.           *)
(*                                                                                *)
(* Network is modeled as a monotonic set of sent messages. This is a particularly *)
(* efficient model for a practical non-Byzantine asynchronous network: messages   *)
(* may be arbitrarily delayed, may be duplicatedly received, and may be lost (but *)
(* in this case the sender would repeatedly retry and thus the message should     *)
(* eventually gets received).                                                     *)
(*                                                                                *)
(* Linearizability is checked from global client's point of view on the sequence  *)
(* of client observed request/acknowledgement events after termination.           *)
(*                                                                                *)
(* Liveness is checked by not having deadlocks till observation of all requests.  *)
(*                                                                                *)
(* Possible further extensions include node failure injection, leader lease and   *)
(* local read mechanism, asymmetric write/read quorum sizes, etc.                 *)
(**********************************************************************************)

---- MODULE MultiPaxos_MC ----
EXTENDS FiniteSets, Sequences, Integers, TLC, Randomization

(*******************************)
(* Model inputs & assumptions. *)
(*******************************)
CONSTANT Replicas,   \* symmetric set of server nodes
         Writes,     \* symmetric set of write commands (each w/ unique value)
         Reads,      \* symmetric set of read commands
         MaxBallot,  \* maximum ballot pickable for leader preemption
         CommitNoticeOn,  \* if true, turn on CommitNotice messages
         NodeFailuresOn   \* if true, turn on node failures injection

ReplicasAssumption == /\ IsFiniteSet(Replicas)
                      /\ Cardinality(Replicas) >= 1
                      /\ "none" \notin Replicas

WritesAssumption == /\ IsFiniteSet(Writes)
                    /\ Cardinality(Writes) >= 1
                    /\ "nil" \notin Writes
                            \* a write command model value serves as both the
                            \* ID of the command and the value to be written

ReadsAssumption == /\ IsFiniteSet(Reads)
                   /\ Cardinality(Reads) >= 0
                   /\ "nil" \notin Writes

MaxBallotAssumption == /\ MaxBallot \in Nat
                       /\ MaxBallot >= 2

CommitNoticeOnAssumption == CommitNoticeOn \in BOOLEAN

NodeFailuresOnAssumption == NodeFailuresOn \in BOOLEAN

ASSUME /\ ReplicasAssumption
       /\ WritesAssumption
       /\ ReadsAssumption
       /\ MaxBallotAssumption
       /\ CommitNoticeOnAssumption
       /\ NodeFailuresOnAssumption

----------

(********************************)
(* Useful constants & typedefs. *)
(********************************)
Commands == Writes \cup Reads

NumCommands == Cardinality(Commands)

Range(seq) == {seq[i]: i \in 1..Len(seq)}

\* Client observable events.
ClientEvents ==      [type: {"Req"}, cmd: Commands]
                \cup [type: {"Ack"}, cmd: Commands,
                                     val: {"nil"} \cup Writes]

ReqEvent(c) == [type |-> "Req", cmd |-> c]

AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]
                        \* val is the old value for a write command

InitPending ==    (CHOOSE ws \in [1..Cardinality(Writes) -> Writes]
                        : Range(ws) = Writes)
               \o (CHOOSE rs \in [1..Cardinality(Reads) -> Reads]
                        : Range(rs) = Reads)
                    \* W.L.O.G., choose any sequence contatenating writes
                    \* commands and read commands as the sequence of reqs;
                    \* all other cases are either symmetric or less useful
                    \* than this one

\* Server-side constants & states.
MajorityNum == (Cardinality(Replicas) \div 2) + 1

Ballots == 1..MaxBallot

Slots == 1..NumCommands

Statuses == {"Preparing", "Accepting", "Committed"}

InstStates == [status: {"Empty"} \cup Statuses,
               cmd: {"nil"} \cup Commands,
               voted: [bal: {0} \cup Ballots,
                       cmd: {"nil"} \cup Commands]]

NullInst == [status |-> "Empty",
             cmd |-> "nil",
             voted |-> [bal |-> 0, cmd |-> "nil"]]

NodeStates == [leader: {"none"} \cup Replicas,
               kvalue: {"nil"} \cup Writes,
               commitUpTo: {0} \cup Slots,
               balPrepared: {0} \cup Ballots,
               balMaxKnown: {0} \cup Ballots,
               insts: [Slots -> InstStates]]

NullNode == [leader |-> "none",
             kvalue |-> "nil",
             commitUpTo |-> 0,
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts |-> [s \in Slots |-> NullInst]]

FirstEmptySlot(insts) ==
    CHOOSE s \in Slots:
        /\ insts[s].status = "Empty"
        /\ \A t \in 1..(s-1): insts[t].status # "Empty"

\* Service-internal messages.
PrepareMsgs == [type: {"Prepare"}, src: Replicas,
                                   bal: Ballots]

PrepareMsg(r, b) == [type |-> "Prepare", src |-> r,
                                         bal |-> b]

InstsVotes == [Slots -> [bal: {0} \cup Ballots,
                         cmd: {"nil"} \cup Commands]]
                             
VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

PrepareReplyMsgs == [type: {"PrepareReply"}, src: Replicas,
                                             bal: Ballots,
                                             votes: InstsVotes]

PrepareReplyMsg(r, b, iv) ==
    [type |-> "PrepareReply", src |-> r,
                              bal |-> b,
                              votes |-> iv]

PeakVotedCmd(prs, s) ==
    IF \A pr \in prs: pr.votes[s].bal = 0
        THEN "nil"
        ELSE LET ppr ==
                    CHOOSE ppr \in prs:
                        \A pr \in prs: pr.votes[s].bal =< ppr.votes[s].bal
             IN  ppr.votes[s].cmd

AcceptMsgs == [type: {"Accept"}, src: Replicas,
                                 bal: Ballots,
                                 slot: Slots,
                                 cmd: Commands]

AcceptMsg(r, b, s, c) == [type |-> "Accept", src |-> r,
                                             bal |-> b,
                                             slot |-> s,
                                             cmd |-> c]

AcceptReplyMsgs == [type: {"AcceptReply"}, src: Replicas,
                                           bal: Ballots,
                                           slot: Slots]

AcceptReplyMsg(r, b, s) == [type |-> "AcceptReply", src |-> r,
                                                    bal |-> b,
                                                    slot |-> s]

CommitNoticeMsgs == [type: {"CommitNotice"}, upto: Slots]

CommitNoticeMsg(u) == [type |-> "CommitNotice", upto |-> u]

Messages ==      PrepareMsgs
            \cup PrepareReplyMsgs
            \cup AcceptMsgs
            \cup AcceptReplyMsgs
            \cup CommitNoticeMsgs

VARIABLES msgs, node, pending, observed, crashed, pc

(* define statement *)
UnseenPending(insts) ==
    LET filter(c) == c \notin {insts[s].cmd: s \in Slots}
    IN  SelectSeq(pending, filter)

RemovePending(cmd) ==
    LET filter(c) == c # cmd
    IN  SelectSeq(pending, filter)

reqsMade == {e.cmd: e \in {e \in Range(observed): e.type = "Req"}}

acksRecv == {e.cmd: e \in {e \in Range(observed): e.type = "Ack"}}

terminated == /\ Len(pending) = 0
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

numCrashed == Cardinality({r \in Replicas: crashed[r]})


vars == << msgs, node, pending, observed, crashed, pc >>

ProcSet == (Replicas)

Init == (* Global variables *)
        /\ msgs = {}
        /\ node = [r \in Replicas |-> NullNode]
        /\ pending = InitPending
        /\ observed = <<>>
        /\ crashed = [r \in Replicas |-> FALSE]
        /\ pc = [self \in ProcSet |-> "rloop"]

rloop(self) == /\ pc[self] = "rloop"
               /\ IF (~terminated) /\ (~crashed[self])
                     THEN /\ \/ /\ node[self].leader # self
                                /\ \E b \in Ballots:
                                     /\ /\ b > node[self].balMaxKnown
                                        /\ ~\E m \in msgs: (m.type = "Prepare") /\ (m.bal = b)
                                     /\ node' = [node EXCEPT ![self].leader = self,
                                                             ![self].balPrepared = 0,
                                                             ![self].balMaxKnown = b,
                                                             ![self].insts = [s \in Slots |->
                                                                                 [node[self].insts[s]
                                                                                     EXCEPT !.status = IF @ = "Accepting"
                                                                                                         THEN "Preparing"
                                                                                                         ELSE @]]]
                                     /\ msgs' = (msgs \cup ({PrepareMsg(self, b),
                                                             PrepareReplyMsg(self, b, VotesByNode(node'[self]))}))
                                /\ UNCHANGED <<pending, observed, crashed>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Prepare"
                                        /\ m.bal > node[self].balMaxKnown
                                     /\ node' = [node EXCEPT ![self].leader = m.src,
                                                             ![self].balMaxKnown = m.bal,
                                                             ![self].insts = [s \in Slots |->
                                                                                 [node[self].insts[s]
                                                                                     EXCEPT !.status = IF @ = "Accepting"
                                                                                                         THEN "Preparing"
                                                                                                         ELSE @]]]
                                     /\ msgs' = (msgs \cup ({PrepareReplyMsg(self, m.bal, VotesByNode(node'[self]))}))
                                /\ UNCHANGED <<pending, observed, crashed>>
                             \/ /\ /\ node[self].leader = self
                                   /\ node[self].balPrepared = 0
                                /\ LET prs == {m \in msgs: /\ m.type = "PrepareReply"
                                                           /\ m.bal = node[self].balMaxKnown} IN
                                     /\ Cardinality(prs) >= MajorityNum
                                     /\ node' = [node EXCEPT ![self].balPrepared = node[self].balMaxKnown,
                                                             ![self].insts = [s \in Slots |->
                                                                                 [node[self].insts[s]
                                                                                     EXCEPT !.status = IF \/ @ = "Preparing"
                                                                                                          \/ /\ @ = "Empty"
                                                                                                             /\ PeakVotedCmd(prs, s) # "nil"
                                                                                                         THEN "Accepting"
                                                                                                         ELSE @,
                                                                                            !.cmd = PeakVotedCmd(prs, s)]]]
                                     /\ msgs' = (msgs \cup (UNION
                                                            {{AcceptMsg(self, node'[self].balPrepared, s, node'[self].insts[s].cmd),
                                                              AcceptReplyMsg(self, node'[self].balPrepared, s)}:
                                                             s \in {s \in Slots: node'[self].insts[s].status = "Accepting"}}))
                                /\ UNCHANGED <<pending, observed, crashed>>
                             \/ /\ /\ node[self].leader = self
                                   /\ node[self].balPrepared = node[self].balMaxKnown
                                   /\ \E s \in Slots: node[self].insts[s].status = "Empty"
                                   /\ Len(UnseenPending(node[self].insts)) > 0
                                /\ LET s == FirstEmptySlot(node[self].insts) IN
                                     LET c == Head(UnseenPending(node[self].insts)) IN
                                       /\ node' = [node EXCEPT ![self].insts[s].status = "Accepting",
                                                               ![self].insts[s].cmd = c,
                                                               ![self].insts[s].voted.bal = node[self].balPrepared,
                                                               ![self].insts[s].voted.cmd = c]
                                       /\ msgs' = (msgs \cup ({AcceptMsg(self, node'[self].balPrepared, s, c),
                                                               AcceptReplyMsg(self, node'[self].balPrepared, s)}))
                                       /\ IF (ReqEvent(c)) \notin Range(observed)
                                             THEN /\ observed' = Append(observed, (ReqEvent(c)))
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED observed
                                /\ UNCHANGED <<pending, crashed>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Accept"
                                        /\ m.bal >= node[self].balMaxKnown
                                        /\ m.bal > node[self].insts[m.slot].voted.bal
                                     /\ node' = [node EXCEPT ![self].leader = m.src,
                                                             ![self].balMaxKnown = m.bal,
                                                             ![self].insts[m.slot].status = "Accepting",
                                                             ![self].insts[m.slot].cmd = m.cmd,
                                                             ![self].insts[m.slot].voted.bal = m.bal,
                                                             ![self].insts[m.slot].voted.cmd = m.cmd]
                                     /\ msgs' = (msgs \cup ({AcceptReplyMsg(self, m.bal, m.slot)}))
                                /\ UNCHANGED <<pending, observed, crashed>>
                             \/ /\ /\ node[self].leader = self
                                   /\ node[self].balPrepared = node[self].balMaxKnown
                                   /\ node[self].commitUpTo < NumCommands
                                   /\ node[self].insts[node[self].commitUpTo+1].status = "Accepting"
                                /\ LET s == node[self].commitUpTo + 1 IN
                                     LET c == node[self].insts[s].cmd IN
                                       LET v == node[self].kvalue IN
                                         LET ars == {m \in msgs: /\ m.type = "AcceptReply"
                                                                 /\ m.slot = s
                                                                 /\ m.bal = node[self].balPrepared} IN
                                           /\ Cardinality(ars) >= MajorityNum
                                           /\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
                                                                   ![self].commitUpTo = s,
                                                                   ![self].kvalue = IF c \in Writes THEN c ELSE @]
                                           /\ IF (AckEvent(c, v)) \notin Range(observed)
                                                 THEN /\ observed' = Append(observed, (AckEvent(c, v)))
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED observed
                                           /\ pending' = RemovePending(c)
                                           /\ msgs' = (msgs \cup ({CommitNoticeMsg(s)}))
                                /\ UNCHANGED crashed
                             \/ /\ IF CommitNoticeOn
                                      THEN /\ /\ node[self].leader # self
                                              /\ node[self].commitUpTo < NumCommands
                                              /\ node[self].insts[node[self].commitUpTo+1].status = "Accepting"
                                           /\ LET s == node[self].commitUpTo + 1 IN
                                                LET c == node[self].insts[s].cmd IN
                                                  \E m \in msgs:
                                                    /\ /\ m.type = "CommitNotice"
                                                       /\ m.upto = s
                                                    /\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
                                                                            ![self].commitUpTo = s,
                                                                            ![self].kvalue = IF c \in Writes THEN c ELSE @]
                                      ELSE /\ TRUE
                                           /\ node' = node
                                /\ UNCHANGED <<msgs, pending, observed, crashed>>
                             \/ /\ IF NodeFailuresOn
                                      THEN /\ /\ MajorityNum + numCrashed < Cardinality(Replicas)
                                              /\ ~crashed[self]
                                              /\ node[self].balMaxKnown < MaxBallot
                                           /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED crashed
                                /\ UNCHANGED <<msgs, node, pending, observed>>
                          /\ pc' = [pc EXCEPT ![self] = "rloop"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << msgs, node, pending, observed, 
                                          crashed >>

Replica(self) == rloop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Replicas: Replica(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

(****************************)
(* TLC config-related defs. *)
(****************************)
ConditionalPerm(set) == IF Cardinality(set) > 1
                          THEN Permutations(set)
                          ELSE {}

SymmetricPerms ==      ConditionalPerm(Replicas)
                  \cup ConditionalPerm(Writes)
                  \cup ConditionalPerm(Reads)

ConstMaxBallot == 2

(*************************)
(* Type check invariant. *)
(*************************)
\* not updated compared to typeokrandom
TypeOK == /\ msgs \in Messages
          /\ \A r \in Replicas: node[r] \in NodeStates
          /\ Len(pending) =< NumCommands
          /\ Cardinality(Range(pending)) = Len(pending)
          /\ \A c \in Range(pending): c \in Commands
          /\ Len(observed) =< 2 * NumCommands
          /\ Cardinality(Range(observed)) = Len(observed)
          /\ Cardinality(reqsMade) >= Cardinality(acksRecv)
          /\ \A e \in Range(observed): e \in ClientEvents
          /\ \A r \in Replicas: crashed[r] \in BOOLEAN

THEOREM Spec => []TypeOK

NumRandElems == 6
TypeOKRandom == /\ msgs \in RandomSubset(NumRandElems, Messages)
                /\ node \in RandomSubset(NumRandElems, NodeStates)
                /\ Len(pending) =< NumCommands \* not randomized
                /\ Cardinality(Range(pending)) = Len(pending)
                /\ \A c \in Range(pending): c \in RandomSubset(NumRandElems, Commands)
                /\ Len(observed) =< 2 * NumCommands
                /\ Cardinality(Range(observed)) = Len(observed)
                /\ Cardinality(reqsMade) >= Cardinality(acksRecv)
                /\ \A e \in Range(observed): e \in RandomSubset(NumRandElems, ClientEvents) 
                /\ \A r \in RandomSubset(NumRandElems, Replicas): crashed[r] \in BOOLEAN

(*******************************)
(* Linearizability constraint. *)
(*******************************)
ReqPosOfCmd(c) == CHOOSE i \in 1..Len(observed):
                        /\ observed[i].type = "Req"
                        /\ observed[i].cmd = c

AckPosOfCmd(c) == CHOOSE i \in 1..Len(observed):
                        /\ observed[i].type = "Ack"
                        /\ observed[i].cmd = c

ResultOfCmd(c) == observed[AckPosOfCmd(c)].val

OrderIdxOfCmd(order, c) == CHOOSE j \in 1..Len(order): order[j] = c

LastWriteBefore(order, j) ==
    LET k == CHOOSE k \in 0..(j-1):
                    /\ (k = 0 \/ order[k] \in Writes)
                    /\ \A l \in (k+1)..(j-1): order[l] \in Reads
    IN  IF k = 0 THEN "nil" ELSE order[k]

IsLinearOrder(order) ==
    /\ {order[j]: j \in 1..Len(order)} = Commands
    /\ \A j \in 1..Len(order):
            ResultOfCmd(order[j]) = LastWriteBefore(order, j)

ObeysRealTime(order) ==
    \A c1, c2 \in Commands:
        (AckPosOfCmd(c1) < ReqPosOfCmd(c2))
            => (OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2))

Linearizability ==
    terminated => 
        \E order \in [1..NumCommands -> Commands]:
            /\ IsLinearOrder(order)
            /\ ObeysRealTime(order)

THEOREM Spec => Linearizability

====




