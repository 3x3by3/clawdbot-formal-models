------------------------------ MODULE PairingStoreIdempotencyHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreIdempotencyHarness.tla
*
* Models a pairing-store pending-requests table with **idempotent** RequestPair.
*
* Real-world motivation:
*   Many providers can retry webhook deliveries, or a user may spam the pairing
*   command. If the store treats each RequestPair as a new row, it can create
*   multiple *live* pending entries for the same (channel, sender), which can:
*     - inflate pending-count caps unfairly
*     - create confusing UX (multiple active codes)
*     - complicate approval flows
*
* This harness captures an intended invariant:
*   For each (channel, sender) there is at most ONE live pending request.
*
* "Green" behavior:
*   AtomicRequestIdem replaces any existing live pending request for that sender.
******************************************************************************)

CONSTANTS
  Threads,     \* finite set (for nondet interleavings)
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

LiveFor(ch, s, t) == { r \in pending : r.ch = ch /\ r.sender = s /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ pending = {}
  /\ step = 0

(*** Idempotent request: replace any existing LIVE pending request for (ch,s). ***)
AtomicRequestIdem(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ pending' = (pending \ LiveFor(ch, s, now)) \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED pending

Next ==
  (\E tid \in Threads, ch \in Channels, s \in Senders: AtomicRequestIdem(tid, ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_NoDuplicateLive ==
  \A ch \in Channels, s \in Senders:
    Cardinality({ r \in LivePendingAt(ch, now) : r.sender = s }) <= 1

=============================================================================
