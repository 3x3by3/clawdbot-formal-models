------------------------------ MODULE ToolPolicyPrecedence ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* ToolPolicyPrecedence.tla
*
* Claim (from docs): Tool filtering is monotone: once a tool is denied by an
* earlier layer, later layers cannot re-enable it.
*
* Reference:
*   clawdbot/docs/multi-agent-sandbox-tools.md (Tool Restrictions order)
*
* We model a fixed chain of N layers. Each layer has an allow-set and deny-set.
* A layer updates the currently-allowed tool set as:
*
*   allowed' = (allowed \cap Allow_i) \ Deny_i
*
* This captures "deny wins".
*
* TLC .cfg parsing is picky about function literals, so we represent
* layers as separate constants Allow1..Allow8, Deny1..Deny8.
*
* We embed this as a trivial state machine (single-state) so TLC can run with
* `INVARIANT` and return success (exit code 0) on pass.
******************************************************************************)

CONSTANTS
  Tools,
  N,
  Allow1, Allow2, Allow3, Allow4, Allow5, Allow6, Allow7, Allow8,
  Deny1,  Deny2,  Deny3,  Deny4,  Deny5,  Deny6,  Deny7,  Deny8

ASSUME
  /\ Tools /= {}
  /\ N \in 1..8

Allow(i) == CASE i=1 -> Allow1 [] i=2 -> Allow2 [] i=3 -> Allow3 [] i=4 -> Allow4 []
                  i=5 -> Allow5 [] i=6 -> Allow6 [] i=7 -> Allow7 [] i=8 -> Allow8

Deny(i)  == CASE i=1 -> Deny1  [] i=2 -> Deny2  [] i=3 -> Deny3  [] i=4 -> Deny4  []
                  i=5 -> Deny5  [] i=6 -> Deny6  [] i=7 -> Deny7  [] i=8 -> Deny8

ApplyLayer(allowed, i) == (allowed \cap Allow(i)) \ Deny(i)

RECURSIVE Fold(_)
Fold(i) == IF i = 0 THEN Tools ELSE ApplyLayer(Fold(i-1), i)

FinalAllowed == Fold(N)

Inv_DenyWins ==
  \A i \in 1..N: \A t \in Deny(i): t \notin FinalAllowed

\* --- Trivial behavior for TLC ---
VARIABLE dummy

Init == dummy = 0
Next == dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
