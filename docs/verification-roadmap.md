# Verification Roadmap (high-ROI security models)

This roadmap enumerates the highest value formal verification targets for Clawdbot
security, with pointers to the concrete code locations.

The intent is to produce **publishable assurance**: each item should result in
reproducible model-check runs and counterexample-guided hardening.

## R1 — DM pairing + allowlist store

**Why:** Every inbound DM surface relies on pairing/allowlist semantics.

**Targets:**
- Pairing pending TTL, per-channel rate limiting/caps, code format constraints
- Atomic promotion of approvals into persistent allowlist
- Concurrency safety (no races between approvals/expiry/new requests)

**Candidate files:**
- `clawdbot/src/pairing/pairing-store.ts`
- Docs: `clawdbot/docs/start/pairing.md`, `clawdbot/docs/gateway/security.md`

**Model:** TLA+ (concurrent requests + expiry + approval flow)

**Example properties:**
- No unapproved sender reaches an agent before approval
- Store never contains >k live requests per channel

---

## R2 — Channel ingress, mention gating, and control-command bypass

**Why:** This is the first line of defense against prompt injection in groups.

**Targets:**
- DM policy + per-sender allowlists
- mention requirements in group contexts
- conditional mention-bypass for control commands (and only when authorized)

**Candidate files:**
- `clawdbot/src/channels/mention-gating.ts`
- `clawdbot/src/channels/command-gating.ts`
- Provider-specific preflight/ACL (e.g. Discord): `clawdbot/src/discord/monitor/*`
- Web inbound access control: `clawdbot/src/web/inbound/access-control.ts`

**Model:** TLA+

**Example properties:**
- Unauthorized sender cannot trigger tool calls even if they craft messages
  resembling control commands

---

## R3 — Session routing & identity linking

**Why:** Prevents cross-user transcript leakage from session-key mixups.

**Targets:**
- session key construction rules (dmScope, per-peer isolation)
- identityLinks join semantics (only explicit links collapse sessions)

**Candidate files:**
- `clawdbot/src/routing/resolve-route.ts`
- `clawdbot/src/routing/session-key.ts`

**Model:** TLA+

**Example properties:**
- Distinct senders do not share a session unless explicitly identity-linked

---

## R4 — Gateway auth + security audit feedback loop

**Why:** Ensures unsafe network binds/auth configs are caught.

**Targets:**
- Auth gate behavior for password/token/tailscale/none
- Audit covers all unsafe bind/auth combinations we support

**Candidate files:**
- `clawdbot/src/gateway/auth.ts`
- `clawdbot/src/security/audit.ts`

**Model:** TLA+

---

## R5 — Node invocation, exec approvals, and `system.run`

**Why:** Highest-risk capability (remote device control / remote execution).

**Targets:**
- Node command allowlist/denylist by platform
- Node must declare commands (no ambient capability)
- `system.run` pipeline: invoke → approval lifecycle → execute/reject
- Timeouts / idempotency behavior

**Candidate files:**
- Tool surface: `clawdbot/src/agents/tools/nodes-tool.ts`
- Gateway allowlist: `clawdbot/src/gateway/node-command-policy.ts`
- Exec approvals: `clawdbot/src/infra/exec-approvals.ts`, `clawdbot/src/gateway/exec-approval-manager.ts`
- Node orchestration: `clawdbot/src/gateway/node-registry.ts`

**Model:** P (or PlusCal) is a good fit; start with TLA+ for policy invariants.

**Example properties:**
- `system.run` reaches a node only if allowed by policy AND approved when required
- Shared-channel attacker cannot trigger node actions indirectly

