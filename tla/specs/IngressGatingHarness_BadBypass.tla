------------------------------ MODULE IngressGatingHarness_BadBypass ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* BUG: bypass allowed for any control command (authorization ignored).
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

\* BUG: ignores CommandAuthorized
BypassAllowed == HasControlCommand /\ AllowTextCommands

ShouldSkip ==
  IsGroup /\ RequireMention /\ CanDetectMention /\ ~WasMentioned /\ ~BypassAllowed

Init == executed = FALSE
Step == /\ executed' = IF ShouldSkip THEN FALSE ELSE TRUE
Spec == Init /\ [][Step]_vars

\* Property: unauthorized control command must not cause execution when mention is required and absent.
Inv_UnauthCannotBypass ==
  (IsGroup /\ RequireMention /\ CanDetectMention /\ ~WasMentioned /\ HasControlCommand /\ AllowTextCommands /\ ~CommandAuthorized)
    => ~executed

=============================================================================
