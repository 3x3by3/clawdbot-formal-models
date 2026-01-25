------------------------------ MODULE AttackerHarness_Approvals_BadIgnoresApproval ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Negative test: buggy approvals model where nodes.run ignores approvals.
* Diff: MayExecute uses approvalOk=TRUE for nodes.run.
******************************************************************************)

CONSTANTS
  Tools,
  PolicyAllowShared,
  PolicyAllowMain,
  NodesRunTool,
  NodeCommands,
  NodesRunCommand,
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,
  ApprovalRequired,
  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {}
  /\ PolicyAllowShared \subseteq Tools
  /\ PolicyAllowMain \subseteq Tools
  /\ NodesRunTool \in Tools
  /\ NodeCommands /= {}
  /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands
  /\ ExtraAllow \subseteq NodeCommands
  /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands
  /\ ApprovalRequired \in BOOLEAN
  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}
ApprovalStates == {"none", "pending", "approved", "denied", "expired"}

VARIABLES sessionType, inbox, executed, approvalState
vars == << sessionType, inbox, executed, approvalState >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny
NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode

AllowedByPolicy(t) == IF sessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain
NodesGateOk == NodeCommandAllowlisted /\ NodeCommandDeclared

\* BUG: approvals ignored
ApprovalOk == TRUE

MayExecute(t) ==
  LET policyOk == AllowedByPolicy(t)
      nodesOk == IF t = NodesRunTool THEN NodesGateOk ELSE TRUE
      approvalOk == IF t = NodesRunTool THEN ApprovalOk ELSE TRUE
  IN  policyOk /\ nodesOk /\ approvalOk

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "pending"

AttackerSend(t) ==
  /\ t \in Tools
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, t)
  /\ UNCHANGED << sessionType, executed, approvalState >>

AgentStep ==
  /\ Len(inbox) > 0
  /\ LET t == Head(inbox)
         approvedNow == (approvalState = "approved")
     IN  /\ inbox' = Tail(inbox)
         /\ executed' =
              IF MayExecute(t) /\ Len(executed) < MaxExecLen
                THEN Append(executed, [tool |-> t, approved |-> approvedNow])
                ELSE executed
  /\ UNCHANGED << sessionType, approvalState >>

Next == (\E t \in Tools: AttackerSend(t)) \/ AgentStep

Spec == Init /\ [][Next]_vars

Inv_NoNodesRunWithoutApproval ==
  ApprovalRequired =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
