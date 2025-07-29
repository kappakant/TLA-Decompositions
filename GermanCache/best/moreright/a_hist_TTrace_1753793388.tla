---- MODULE a_hist_TTrace_1753793388 ----
EXTENDS a_hist, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET a_hist_TEExpression == INSTANCE a_hist_TEExpression
    IN a_hist_TEExpression!expression
----

_trace ==
    LET a_hist_TETrace == INSTANCE a_hist_TETrace
    IN a_hist_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        Chan2 = (<<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>)
        /\
        ExGntd = (TRUE)
        /\
        Chan3 = (<<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>)
        /\
        MemData = (1)
        /\
        AuxData = (1)
        /\
        Cache = (<<<<"S", 1>>, <<"E", 1>>, <<"I", 1>>>>)
    )
----

_init ==
    /\ ExGntd = _TETrace[1].ExGntd
    /\ AuxData = _TETrace[1].AuxData
    /\ MemData = _TETrace[1].MemData
    /\ Chan2 = _TETrace[1].Chan2
    /\ Chan3 = _TETrace[1].Chan3
    /\ Cache = _TETrace[1].Cache
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ ExGntd  = _TETrace[i].ExGntd
        /\ ExGntd' = _TETrace[j].ExGntd
        /\ AuxData  = _TETrace[i].AuxData
        /\ AuxData' = _TETrace[j].AuxData
        /\ MemData  = _TETrace[i].MemData
        /\ MemData' = _TETrace[j].MemData
        /\ Chan2  = _TETrace[i].Chan2
        /\ Chan2' = _TETrace[j].Chan2
        /\ Chan3  = _TETrace[i].Chan3
        /\ Chan3' = _TETrace[j].Chan3
        /\ Cache  = _TETrace[i].Cache
        /\ Cache' = _TETrace[j].Cache

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("a_hist_TTrace_1753793388.json", _TETrace)

=============================================================================

 Note that you can extract this module `a_hist_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `a_hist_TEExpression.tla` file takes precedence 
  over the module `a_hist_TEExpression` below).

---- MODULE a_hist_TEExpression ----
EXTENDS a_hist, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `a_hist` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        ExGntd |-> ExGntd
        ,AuxData |-> AuxData
        ,MemData |-> MemData
        ,Chan2 |-> Chan2
        ,Chan3 |-> Chan3
        ,Cache |-> Cache
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_ExGntdUnchanged |-> ExGntd = ExGntd'
        
        \* Format the `ExGntd` variable as Json value.
        \* ,_ExGntdJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(ExGntd)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_ExGntdModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].ExGntd # _TETrace[s-1].ExGntd
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE a_hist_TETrace ----
\*EXTENDS a_hist, IOUtils, TLC
\*
\*trace == IODeserialize("a_hist_TTrace_1753793388.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE a_hist_TETrace ----
EXTENDS a_hist, TLC

trace == 
    <<
    ([Chan2 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,ExGntd |-> FALSE,Chan3 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,MemData |-> 1,AuxData |-> 1,Cache |-> <<<<"I", 1>>, <<"I", 1>>, <<"I", 1>>>>]),
    ([Chan2 |-> <<<<"GntS", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,ExGntd |-> FALSE,Chan3 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,MemData |-> 1,AuxData |-> 1,Cache |-> <<<<"I", 1>>, <<"I", 1>>, <<"I", 1>>>>]),
    ([Chan2 |-> <<<<"GntS", 1>>, <<"GntE", 1>>, <<"Empty", 1>>>>,ExGntd |-> TRUE,Chan3 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,MemData |-> 1,AuxData |-> 1,Cache |-> <<<<"I", 1>>, <<"I", 1>>, <<"I", 1>>>>]),
    ([Chan2 |-> <<<<"GntS", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,ExGntd |-> TRUE,Chan3 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,MemData |-> 1,AuxData |-> 1,Cache |-> <<<<"I", 1>>, <<"E", 1>>, <<"I", 1>>>>]),
    ([Chan2 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,ExGntd |-> TRUE,Chan3 |-> <<<<"Empty", 1>>, <<"Empty", 1>>, <<"Empty", 1>>>>,MemData |-> 1,AuxData |-> 1,Cache |-> <<<<"S", 1>>, <<"E", 1>>, <<"I", 1>>>>])
    >>
----


=============================================================================

---- CONFIG a_hist_TTrace_1753793388 ----
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
\* Generated on Tue Jul 29 08:49:48 EDT 2025