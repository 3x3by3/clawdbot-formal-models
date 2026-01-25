------------------------------ MODULE AttackerHarness_NodesAllowlist ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* AttackerHarness_NodesAllowlist.tla
*
* Extends the attacker harness to derive NodeCommandAllowlisted from:
*   EffectiveAllowlist = (PlatformDefaults \cup ExtraAllow) \ Deny
*
* Mirrors clawdbot/src/gateway/node-command-policy.ts at a high level.
******************************************************************************)

CONSTANTS
  Tools,
  SensitiveTools,
  PolicyAllowShared,
  PolicyAllowMain,

  NodesRunTool,

  \* Node command policy (strings)
  NodeCommands,
  NodesRunCommand,     \* e.g. "system.run"
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,

  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {}
  /\ SensitiveTools \subseteq Tools
  /\ PolicyAllowShared \subseteq Tools
  /\ PolicyAllowMain \subseteq Tools

  /\ NodesRunTool \in Tools

  /\ NodeCommands /= {}
  /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands
  /\ ExtraAllow \subseteq NodeCommands
  /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands

  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}

VARIABLES sessionType, inbox, executed
vars == << sessionType, inbox, executed >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny

NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode

Allowed(t) ==
  LET policyOk == IF sessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain
      nodesOk == IF t = NodesRunTool THEN (NodeCommandAllowlisted /\ NodeCommandDeclared) ELSE TRUE
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
