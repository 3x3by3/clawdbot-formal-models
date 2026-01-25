------------------------------ MODULE AttackerHarness_Approvals ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* AttackerHarness_Approvals.tla
*
* Adds an explicit approval lifecycle for a sensitive action (nodes.run), and
* records whether approval was present *at the time of execution*.
*
* Security property (non-tautological): whenever nodes.run is executed while
* ApprovalRequired=TRUE, it must have been executed with approvalState="approved"
* in that step.
******************************************************************************)

CONSTANTS
  Tools,
  PolicyAllowShared,
  PolicyAllowMain,

  NodesRunTool,

  \* Node command policy (strings)
  NodeCommands,
  NodesRunCommand,
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,

  \* Approval policy
  ApprovalRequired,        \* BOOLEAN

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

ApprovalOk == IF ApprovalRequired THEN approvalState = "approved" ELSE TRUE

MayExecute(t) ==
  LET policyOk == AllowedByPolicy(t)
      nodesOk == IF t = NodesRunTool THEN NodesGateOk ELSE TRUE
      approvalOk == IF t = NodesRunTool THEN ApprovalOk ELSE TRUE
  IN  policyOk /\ nodesOk /\ approvalOk

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "none"

AttackerSend(t) ==
  /\ t \in Tools
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, t)
  /\ UNCHANGED << sessionType, executed, approvalState >>

RequestApproval ==
  /\ approvalState \in {"none", "denied", "expired"}
  /\ approvalState' = "pending"
  /\ UNCHANGED << sessionType, inbox, executed >>

HumanApprove ==
  /\ approvalState = "pending"
  /\ approvalState' = "approved"
  /\ UNCHANGED << sessionType, inbox, executed >>

HumanDeny ==
  /\ approvalState = "pending"
  /\ approvalState' = "denied"
  /\ UNCHANGED << sessionType, inbox, executed >>

ExpireApproval ==
  /\ approvalState = "approved"
  /\ approvalState' = "expired"
  /\ UNCHANGED << sessionType, inbox, executed >>

\* executed entries are records: [tool |-> t, approved |-> BOOLEAN]
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

Next ==
  (\E t \in Tools: AttackerSend(t))
  \/ AgentStep
  \/ RequestApproval
  \/ HumanApprove
  \/ HumanDeny
  \/ ExpireApproval

Spec == Init /\ [][Next]_vars

Inv_NoNodesRunWithoutApproval ==
  ApprovalRequired =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
