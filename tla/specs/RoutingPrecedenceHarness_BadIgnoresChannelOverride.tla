------------------------------ MODULE RoutingPrecedenceHarness_BadIgnoresChannelOverride ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingPrecedenceHarness_BadIgnoresChannelOverride.tla
*
* "Red" variant: buggy precedence where the global dmScope is always used,
* ignoring any per-channel override.
*
* With GlobalDmScope="main" and ChannelDmScope="per-peer", this collapses all
* DMs into the "main" session, violating Inv_NoUnlinkedCollapse.
******************************************************************************)

CONSTANTS
  Peers,
  GlobalDmScope,        \* "main" | "per-peer"
  ChannelDmScope,       \* "unset" | "main" | "per-peer"
  IdentityLinks         \* SUBSET (Peers \X Peers)

ASSUME
  /\ Peers /= {}
  /\ GlobalDmScope \in {"main","per-peer"}
  /\ ChannelDmScope \in {"unset","main","per-peer"}
  /\ IdentityLinks \subseteq (Peers \X Peers)

\* Symmetric closure of identity links
Linked(a,b) == <<a,b>> \in IdentityLinks \/ <<b,a>> \in IdentityLinks \/ a=b

\* BUG: ignores ChannelDmScope entirely.
EffectiveDmScope == GlobalDmScope

SessionKey(p) ==
  IF EffectiveDmScope = "main" THEN "main"
  ELSE
    CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

Inv_ChannelOverrideWins ==
  ChannelDmScope /= "unset" => EffectiveDmScope = ChannelDmScope

Inv_NoUnlinkedCollapse ==
  EffectiveDmScope = "per-peer" =>
    \A p1 \in Peers: \A p2 \in Peers:
      (~Linked(p1,p2)) => (SessionKey(p1) /= SessionKey(p2))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
