------------------------------ MODULE ClawdbotSecurityCore ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Core definitions for Clawdbot security modeling.
*
* This module factors out the policy + invariants so scenario models can
* instantiate constants without duplicating logic.
******************************************************************************)

CONSTANTS
  Users, Sessions, Providers, Tools,
  MainSession, SharedSession,
  MemTools, ExternalTools, ElevatedTools

SessionTypes == {"main", "shared"}

VARIABLES
  owner, sessionType, sessionProvider, pendingApproval, lastAction

vars == << owner, sessionType, sessionProvider, pendingApproval, lastAction >>

ASSUME
  /\ Users /= {} /\ Sessions /= {} /\ Providers /= {} /\ Tools /= {}
  /\ MainSession \in Sessions
  /\ SharedSession \in Sessions
  /\ MainSession /= SharedSession
  /\ MemTools \subseteq Tools
  /\ ExternalTools \subseteq Tools
  /\ ElevatedTools \subseteq Tools

IsMain(s) == sessionType[s] = "main"
IsShared(s) == sessionType[s] = "shared"

NeedsApproval(t) == t \in ExternalTools \/ t \in ElevatedTools

AllowedByPolicy(s, t) ==
  IF IsShared(s) THEN
    t \notin MemTools
  ELSE
    TRUE

MayRun(s, t) ==
  /\ AllowedByPolicy(s, t)
  /\ IF NeedsApproval(t) THEN s \notin pendingApproval ELSE TRUE

Init ==
  /\ owner \in Users
  /\ sessionType \in [Sessions -> SessionTypes]
  /\ sessionProvider \in [Sessions -> Providers]
  /\ pendingApproval = {}
  /\ lastAction \in [Sessions -> [tool: Tools \cup {"none"}]]
  /\ \A s \in Sessions: lastAction[s].tool = "none"

RunTool(s, t) ==
  /\ s \in Sessions
  /\ t \in Tools
  /\ MayRun(s, t)
  /\ lastAction' = [lastAction EXCEPT ![s].tool = t]
  /\ UNCHANGED << owner, sessionType, sessionProvider, pendingApproval >>

RequestApproval(s) ==
  /\ s \in Sessions
  /\ pendingApproval' = pendingApproval \cup {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

GrantApproval(s) ==
  /\ s \in pendingApproval
  /\ pendingApproval' = pendingApproval \ {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

Next ==
  (\E s \in Sessions, t \in Tools: RunTool(s, t))
  \/ (\E s \in Sessions: RequestApproval(s))
  \/ (\E s \in Sessions: GrantApproval(s))

Spec == Init /\ [][Next]_vars

\* --- Invariants ---

Inv_NoMemoryToolInShared ==
  \A t \in MemTools: \A s \in Sessions:
    IsShared(s) => ~MayRun(s, t)

Inv_ApprovalGate ==
  \A s \in Sessions:
    s \in pendingApproval => (\A t \in Tools: NeedsApproval(t) => ~MayRun(s, t))

THEOREM Spec => []Inv_NoMemoryToolInShared
THEOREM Spec => []Inv_ApprovalGate

=============================================================================
