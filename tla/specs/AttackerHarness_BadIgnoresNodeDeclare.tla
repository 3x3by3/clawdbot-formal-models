------------------------------ MODULE AttackerHarness_BadIgnoresNodeDeclare ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Negative test: buggy attacker harness where nodes.run ignores declaredCommands.
******************************************************************************)

CONSTANTS
  Tools,
  SensitiveTools,
  PolicyAllowShared,
  PolicyAllowMain,
  NodesRunTool,
  NodeCommandAllowlisted,
  NodeCommandDeclared,
  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {}
  /\ SensitiveTools \subseteq Tools
  /\ PolicyAllowShared \subseteq Tools
  /\ PolicyAllowMain \subseteq Tools
  /\ NodesRunTool \in Tools
  /\ NodeCommandAllowlisted \in BOOLEAN
  /\ NodeCommandDeclared \in BOOLEAN
  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}

VARIABLES sessionType, inbox, executed
vars == << sessionType, inbox, executed >>

\* BUG: ignores NodeCommandDeclared
Allowed(t) ==
  LET policyOk == IF sessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain
      nodesOk == IF t = NodesRunTool THEN NodeCommandAllowlisted ELSE TRUE
  IN  policyOk /\ nodesOk

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>

AttackerSend(t) ==
  /\ t \in Tools
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, t)
  /\ UNCHANGED << sessionType, executed >>

AgentStep ==
  /\ Len(inbox) > 0
  /\ LET t == Head(inbox)
     IN  /\ inbox' = Tail(inbox)
         /\ executed' = IF Allowed(t) /\ Len(executed) < MaxExecLen THEN Append(executed, t) ELSE executed
  /\ UNCHANGED << sessionType >>

Next ==
  (\E t \in Tools: AttackerSend(t))
  \/ AgentStep

Spec == Init /\ [][Next]_vars

Inv_NoSensitiveExecInShared ==
  sessionType = "shared" =>
    \A i \in 1..Len(executed): executed[i] \notin SensitiveTools

=============================================================================
