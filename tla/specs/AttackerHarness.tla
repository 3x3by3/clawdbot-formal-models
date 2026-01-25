------------------------------ MODULE AttackerHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* AttackerHarness.tla
*
* Minimal attacker-driven model (non-tautological):
*   - Attacker sends tool requests in a shared session.
*   - Agent decides whether to execute based on an explicit policy table.
*   - We check trace properties over ExecutedActions.
*
* This is deliberately small but captures the *shape* of prompt-injection risk:
* "an untrusted sender causes a forbidden tool to execute".
******************************************************************************)

CONSTANTS
  Tools,              \* finite set of tool ids (strings)
  SensitiveTools,     \* subset of Tools considered security-critical
  PolicyAllowShared,  \* subset of Tools allowed to execute in shared sessions
  PolicyAllowMain,    \* subset of Tools allowed to execute in main sessions
  MaxQueueLen,        \* bound inbox length (keeps TLC finite)
  MaxExecLen          \* bound executed length

ASSUME
  /\ Tools /= {}
  /\ SensitiveTools \subseteq Tools
  /\ PolicyAllowShared \subseteq Tools
  /\ PolicyAllowMain \subseteq Tools
  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}

VARIABLES
  sessionType,        \* "main" or "shared"
  inbox,              \* Seq(Tools) pending tool requests
  executed            \* Seq(Tools) executed tools in order

vars == << sessionType, inbox, executed >>

Allowed(t) ==
  IF sessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>

\* Attacker can request any tool any time.
AttackerSend(t) ==
  /\ t \in Tools
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, t)
  /\ UNCHANGED << sessionType, executed >>

\* Agent processes the head of the inbox.
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

\* --- Security property (non-tautological):
\* In shared sessions, the agent never executes sensitive tools.
Inv_NoSensitiveExecInShared ==
  sessionType = "shared" =>
    \A i \in 1..Len(executed): executed[i] \notin SensitiveTools

THEOREM Spec => []Inv_NoSensitiveExecInShared

=============================================================================
