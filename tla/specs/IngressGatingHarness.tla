------------------------------ MODULE IngressGatingHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* IngressGatingHarness.tla
*
* Roadmap R2: Channel ingress gating, mention gating, and control-command bypass.
*
* We model the core security question:
*  In group contexts requiring mention, an attacker should not be able to bypass
*  mention gating unless the control command is authorized.
*
* State records whether the agent executed any tool.
******************************************************************************)

CONSTANTS
  IsGroup,
  RequireMention,
  CanDetectMention,
  WasMentioned,
  HasControlCommand,
  AllowTextCommands,
  CommandAuthorized

ASSUME
  /\ IsGroup \in BOOLEAN
  /\ RequireMention \in BOOLEAN
  /\ CanDetectMention \in BOOLEAN
  /\ WasMentioned \in BOOLEAN
  /\ HasControlCommand \in BOOLEAN
  /\ AllowTextCommands \in BOOLEAN
  /\ CommandAuthorized \in BOOLEAN

VARIABLES executed
vars == << executed >>

\* Intended mention bypass rule:
BypassAllowed == HasControlCommand /\ AllowTextCommands /\ CommandAuthorized

\* Effective mention requirement:
ShouldSkip ==
  IsGroup /\ RequireMention /\ CanDetectMention /\ ~WasMentioned /\ ~BypassAllowed

Init == executed = FALSE

\* Single step: either agent executes a tool or skips.
Step ==
  /\ executed' = IF ShouldSkip THEN FALSE ELSE TRUE

Spec == Init /\ [][Step]_vars

\* Property: If message should be skipped, we never execute.
\* Property: unauthorized control command must not cause execution when mention is required and absent.
Inv_UnauthCannotBypass ==
  (IsGroup /\ RequireMention /\ CanDetectMention /\ ~WasMentioned /\ HasControlCommand /\ AllowTextCommands /\ ~CommandAuthorized)
    => ~executed

=============================================================================
