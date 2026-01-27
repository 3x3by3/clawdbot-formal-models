------------------------------ MODULE RoutingIdentityLinksTransitiveHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksTransitiveHarness.tla
*
* Roadmap R3+++: routing identityLinks transitive closure.
*
* Motivation:
*   If identity linking is used to collapse DMs across multiple provider/user
*   identities, it should behave like an equivalence relation (at least
*   transitively): if A linked to B and B linked to C, then A and C should end
*   up in the same DM session.
*
* This harness models per-peer dmScope with identity links treated as an
* equivalence relation by using an explicit transitive closure predicate.
******************************************************************************)

CONSTANTS
  Peers,
  LinkGroups \* a set of groups, each a SUBSET of Peers

ASSUME
  /\ Peers /= {}
  /\ LinkGroups \subseteq SUBSET Peers

\* Direct link if a and b appear together in some group.
DirectLinked(a,b) == \E g \in LinkGroups: a \in g /\ b \in g

\* Transitive closure over DirectLinked via reachability.
MaxLen == Cardinality(Peers)

Reachable(a,b) ==
  \E n \in 1..MaxLen:
    \E path \in [1..n -> Peers]:
      /\ path[1] = a
      /\ path[n] = b
      /\ \A i \in 1..(n-1): DirectLinked(path[i], path[i+1])

Linked(a,b) == (a=b) \/ Reachable(a,b)

\* Canonical representative for equivalence class under Linked
SessionKey(p) ==
  CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

\* If A shares a group with B and B shares a group with C, then A and C should
\* end up with the same session key.
Inv_TransitiveCollapse ==
  \A a \in Peers: \A b \in Peers: \A c \in Peers:
    (DirectLinked(a,b) /\ DirectLinked(b,c)) => (SessionKey(a) = SessionKey(c))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
