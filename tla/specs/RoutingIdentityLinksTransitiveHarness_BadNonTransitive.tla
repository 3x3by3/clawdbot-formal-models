------------------------------ MODULE RoutingIdentityLinksTransitiveHarness_BadNonTransitive ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksTransitiveHarness_BadNonTransitive.tla
*
* "Red" variant: identity links are treated as only direct adjacency (no
* transitive closure). This can fail to collapse A and C even when A-B and B-C
* are linked.
******************************************************************************)

CONSTANTS
  Peers,
  LinkGroups

ASSUME
  /\ Peers /= {}
  /\ LinkGroups \subseteq SUBSET Peers

\* BUG: links are non-transitive; treat each peer as linked only within the
\* first group it appears in (dropping overlaps).
FirstGroup(p) ==
  IF (\E g \in LinkGroups: p \in g) THEN
    CHOOSE g \in LinkGroups: p \in g
  ELSE
    {p}

Linked(a,b) == FirstGroup(a) = FirstGroup(b)

SessionKey(p) ==
  CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

Inv_TransitiveCollapse ==
  \A a \in Peers: \A b \in Peers: \A c \in Peers:
    ((\E g1 \in LinkGroups: a \in g1 /\ b \in g1)
     /\ (\E g2 \in LinkGroups: b \in g2 /\ c \in g2))
      => (SessionKey(a) = SessionKey(c))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
