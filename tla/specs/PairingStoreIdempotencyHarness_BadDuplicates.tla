------------------------------ MODULE PairingStoreIdempotencyHarness_BadDuplicates ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreIdempotencyHarness_BadDuplicates.tla
*
* "Red" variant: RequestPair always appends a new pending request, even if an
* unexpired request already exists for the same (channel, sender).
*
* This should violate Inv_NoDuplicateLive with a short counterexample trace.
******************************************************************************)

CONSTANTS
  Threads,
  Channels,
  Senders,
  TTL,
  MaxTime,
  MaxSteps

ASSUME
  /\ Threads /= {} /\ Channels /= {} /\ Senders /= {}
  /\ TTL \in 1..MaxTime
  /\ MaxTime \in 1..20
  /\ MaxSteps \in 1..50

Req(ch, sender, createdAt) == [ch |-> ch, sender |-> sender, createdAt |-> createdAt]

VARIABLES now, pending, step
vars == << now, pending, step >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LivePendingAt(ch, t) == { r \in pending : r.ch = ch /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ pending = {}
  /\ step = 0

(*** Buggy request: always append (new createdAt makes it a distinct element). ***)
AtomicRequestNoIdem(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ pending' = pending \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED pending

Next ==
  (\E tid \in Threads, ch \in Channels, s \in Senders: AtomicRequestNoIdem(tid, ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_NoDuplicateLive ==
  \A ch \in Channels, s \in Senders:
    Cardinality({ r \in LivePendingAt(ch, now) : r.sender = s }) <= 1

=============================================================================
