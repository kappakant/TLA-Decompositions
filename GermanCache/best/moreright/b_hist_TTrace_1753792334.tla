---- MODULE b_hist_TTrace_1753792334 ----
EXTENDS Sequences, TLCExt, Toolbox, b_hist, Naturals, TLC

_expression ==
    LET b_hist_TEExpression == INSTANCE b_hist_TEExpression
    IN b_hist_TEExpression!expression
----

_trace ==
    LET b_hist_TETrace == INSTANCE b_hist_TETrace
    IN b_hist_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        CurCmd = ("Empty")
        /\
        CurPtr = (1)
        /\
        ShrSet = (<<TRUE, FALSE, FALSE>>)
        /\
        InvSet = (<<FALSE, FALSE, FALSE>>)
        /\
        Fluent1_0 = (<<TRUE, FALSE, FALSE>>)
        /\
        Chan1 = (<<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>)
    )
----

_init ==
    /\ CurCmd = _TETrace[1].CurCmd
    /\ CurPtr = _TETrace[1].CurPtr
    /\ InvSet = _TETrace[1].InvSet
    /\ Chan1 = _TETrace[1].Chan1
    /\ Fluent1_0 = _TETrace[1].Fluent1_0
    /\ ShrSet = _TETrace[1].ShrSet
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ CurCmd  = _TETrace[i].CurCmd
        /\ CurCmd' = _TETrace[j].CurCmd
        /\ CurPtr  = _TETrace[i].CurPtr
        /\ CurPtr' = _TETrace[j].CurPtr
        /\ InvSet  = _TETrace[i].InvSet
        /\ InvSet' = _TETrace[j].InvSet
        /\ Chan1  = _TETrace[i].Chan1
        /\ Chan1' = _TETrace[j].Chan1
        /\ Fluent1_0  = _TETrace[i].Fluent1_0
        /\ Fluent1_0' = _TETrace[j].Fluent1_0
        /\ ShrSet  = _TETrace[i].ShrSet
        /\ ShrSet' = _TETrace[j].ShrSet

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("b_hist_TTrace_1753792334.json", _TETrace)

=============================================================================

 Note that you can extract this module `b_hist_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `b_hist_TEExpression.tla` file takes precedence 
  over the module `b_hist_TEExpression` below).

---- MODULE b_hist_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, b_hist, Naturals, TLC

expression == 
    [
        \* To hide variables of the `b_hist` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        CurCmd |-> CurCmd
        ,CurPtr |-> CurPtr
        ,InvSet |-> InvSet
        ,Chan1 |-> Chan1
        ,Fluent1_0 |-> Fluent1_0
        ,ShrSet |-> ShrSet
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_CurCmdUnchanged |-> CurCmd = CurCmd'
        
        \* Format the `CurCmd` variable as Json value.
        \* ,_CurCmdJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(CurCmd)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_CurCmdModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].CurCmd # _TETrace[s-1].CurCmd
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE b_hist_TETrace ----
\*EXTENDS IOUtils, b_hist, TLC
\*
\*trace == IODeserialize("b_hist_TTrace_1753792334.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE b_hist_TETrace ----
EXTENDS b_hist, TLC

trace == 
    <<
    ([CurCmd |-> "Empty",CurPtr |-> 1,ShrSet |-> <<FALSE, FALSE, FALSE>>,InvSet |-> <<FALSE, FALSE, FALSE>>,Fluent1_0 |-> <<FALSE, FALSE, FALSE>>,Chan1 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>]),
    ([CurCmd |-> "Empty",CurPtr |-> 1,ShrSet |-> <<FALSE, FALSE, FALSE>>,InvSet |-> <<FALSE, FALSE, FALSE>>,Fluent1_0 |-> <<FALSE, FALSE, FALSE>>,Chan1 |-> <<<<"ReqS", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>]),
    ([CurCmd |-> "ReqS",CurPtr |-> 1,ShrSet |-> <<FALSE, FALSE, FALSE>>,InvSet |-> <<FALSE, FALSE, FALSE>>,Fluent1_0 |-> <<FALSE, FALSE, FALSE>>,Chan1 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>]),
    ([CurCmd |-> "Empty",CurPtr |-> 1,ShrSet |-> <<TRUE, FALSE, FALSE>>,InvSet |-> <<FALSE, FALSE, FALSE>>,Fluent1_0 |-> <<TRUE, FALSE, FALSE>>,Chan1 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>])
    >>
----


=============================================================================

---- CONFIG b_hist_TTrace_1753792334 ----
CONSTANTS
    NODE = { 1 , 2 , 3 }
    DATA = { 1 , 2 }

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Tue Jul 29 08:32:15 EDT 2025