------------------------------ MODULE PairingStoreConcurrentHarness_BadAtomic ------------------------------
EXTENDS PairingStoreConcurrentHarness

(******************************************************************************
* BUG: cap check is incorrectly re-evaluated at commit time using current now,
* but commit does not re-check cap (i.e., no lock).
*
* In this model, CommitRequest is identical to the base harness; the "bug" is
* simply that Begin+Commit are non-atomic.
*
* This module exists as a named target for a negative model.
******************************************************************************)

=============================================================================
