------------------------------ MODULE RoutingPrecedenceHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingPrecedenceHarness.tla
*
* Roadmap R3++: Routing identityLinks + dmScope + precedence.
*
* Motivation:
*   Clawdbot routing has multiple config sources that can influence how DM
*   session keys are constructed.
*
* In particular, a per-channel dmScope override (if set) should take precedence
* over a global default.
*
* This harness models:
*   - GlobalDmScope: global default ("main" | "per-peer")
*   - ChannelDmScope: optional per-channel override ("unset" | "main" | "per-peer")
*   - IdentityLinks: explicit relation allowing peers to share a session when
*     EffectiveDmScope is per-peer.
*
* Safety property:
*   Under EffectiveDmScope = per-peer, distinct unlinked peers must not collapse
*   into the same session key.
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

EffectiveDmScope ==
  IF ChannelDmScope = "unset" THEN GlobalDmScope ELSE ChannelDmScope

\* Canonical session key for a peer
SessionKey(p) ==
  IF EffectiveDmScope = "main" THEN "main"
  ELSE
    \* choose a representative for the identity-link equivalence class
    CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

\* Precedence property: per-channel override must win over global default.
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
