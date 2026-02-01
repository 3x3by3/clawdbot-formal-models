# CLAUDE.md - AI Assistant Guide

This document provides comprehensive guidance for AI assistants working with the clawdbot-formal-models repository.

## Repository Overview

This repository contains **formal security verification models** for Clawdbot, a multi-agent Discord/Signal bot. The models are written primarily in **TLA+** (Temporal Logic of Actions) and verified using **TLC** (TLA+ model checker).

**Philosophy:** This is a practical **security regression suite**, not an academic exercise:
- **Green models** should pass TLC without invariant violations (representing intended secure behavior)
- **Red models** are deliberately buggy variants that should fail with counterexample traces (proving the checks catch security issues)

The goal is **publishable assurance** for security claims about Clawdbot's design.

## Directory Structure

```
clawdbot-formal-models/
├── tla/
│   ├── specs/           # TLA+ specifications (59 files)
│   └── models/          # TLC model configurations (.cfg, 78 files)
├── docs/
│   ├── formal-models.md         # How to run models, interpret results
│   ├── security-claims.md       # Enumerated security claims (C1-C6)
│   ├── verification-roadmap.md  # High-ROI verification targets (R1-R5)
│   ├── nodes-security-notes.md  # Nodes feature threat model
│   └── gateway-exposure-matrix.md # Gateway exposure test cases
├── generated/
│   ├── tool-groups.json  # Extracted from Clawdbot source
│   └── tool-groups.cfg   # Generated TLA+ config
├── scripts/
│   ├── extract-tool-groups.mjs      # Extracts tool groups from ../clawdbot
│   └── gen-tla-cfg-from-tool-groups.mjs # Generates TLA+ config
├── tools/tla/
│   └── tla2tools.jar     # Pinned TLA+ toolchain
├── bin/
│   └── tlc               # Bash wrapper for TLC execution
├── .github/workflows/
│   └── tlc.yml           # CI: runs green and negative models
├── Makefile              # 80+ targets for TLC execution
└── README.md             # Quick start guide
```

## Prerequisites

- **Java 11+** (Java 21 recommended)
- No other dependencies required; TLA+ tools are bundled in `tools/tla/`

## Key Commands

### Running Models

```bash
# Run a specific target
make <target>

# Common green models (should pass)
make gateway-exposure-v2
make pairing
make ingress-gating
make routing-isolation
make approvals-token
make nodes-pipeline

# Corresponding negative models (should fail with invariant violation)
make gateway-exposure-v2-negative
make pairing-negative
make ingress-gating-negative
make routing-isolation-negative
make approvals-token-negative
make nodes-pipeline-negative
```

### Conformance Extraction

```bash
# Extract tool groups from ../clawdbot source
node scripts/extract-tool-groups.mjs

# Alternative: use env var for clawdbot location
CLAWDBOT_REPO_DIR=/path/to/clawdbot node scripts/extract-tool-groups.mjs
```

### Direct TLC Execution

```bash
# Using the wrapper
./bin/tlc -workers auto -deadlock -config tla/models/<model>.cfg tla/specs/<Spec>.tla
```

## TLA+ File Conventions

### Naming Patterns

| Pattern | Meaning |
|---------|---------|
| `*Harness.tla` | Main specification with threat model |
| `*_Bad*.tla` | Intentionally buggy variant (red model) |
| `*_ok.cfg` | Green scenario configuration |
| `*_negative*.cfg` | Red scenario configuration (should fail) |

### Specification Structure

TLA+ specs follow this structure:
1. Module header comment (purpose, threat model)
2. `EXTENDS` standard libraries
3. `CONSTANTS` + `ASSUME` section
4. Helper operators
5. `VARIABLES` + vars tuple
6. `Init` predicate
7. Action operators
8. `Next` formula (disjunction of actions)
9. `Spec` definition (`Init /\ [][Next]_vars`)
10. Invariant/theorem definitions (`Inv_*`)

### Variable Naming

- **Constants:** UPPERCASE (`Users`, `Tools`, `Sessions`)
- **Variables:** camelCase (`inbox`, `executed`, `sessionType`)
- **Operators:** lowercase (`allowed`, `init`, `next`)
- **Invariants:** `Inv_*` prefix (`Inv_NoMemoryToolInShared`)

### Model Config Format (.cfg)

```
SPECIFICATION Spec
INVARIANT Inv_NotCompromised
CONSTANTS
  BindMode = "loopback"
  ModeConfig = "auto"
  HasToken = FALSE
```

## Security Claims Reference

Key claims modeled (see `docs/security-claims.md` for details):

| Claim | Description | Invariant |
|-------|-------------|-----------|
| C1 | Shared contexts cannot access memory tools | `Inv_NoMemoryToolInShared` |
| C2 | Approval gate blocks risky tools while pending | `Inv_ApprovalGate` |
| C3 | Tool policy precedence is monotone (deny wins) | `Inv_DenyWins` |
| C4 | Tool groups expand to documented tool sets | `Inv_GroupMemoryExact` |
| C5 | Elevated execution requires both global and agent allowlists | `Inv_ElevatedRequiresBoth` |
| C6 | `nodes.run` requires live approval when configured | `Inv_NoNodesRunWithoutApproval` |

## Verification Roadmap

High-ROI targets (see `docs/verification-roadmap.md`):

| Target | Focus Area | Key Files in Clawdbot |
|--------|------------|----------------------|
| R1 | DM pairing + allowlist store | `pairing-store.ts` |
| R2 | Channel ingress, mention gating | `mention-gating.ts`, `command-gating.ts` |
| R3 | Session routing & identity linking | `resolve-route.ts`, `session-key.ts` |
| R4 | Gateway auth + security audit | `auth.ts`, `audit.ts` |
| R5 | Node invocation, exec approvals | `nodes-tool.ts`, `node-command-policy.ts` |

## CI/CD

The GitHub Actions workflow (`.github/workflows/tlc.yml`):
- Triggers on PRs and pushes to `main`
- Runs with Java 21 (Temurin)
- Timeout: 10 minutes
- Executes green models (must pass)
- Executes negative models (must fail with invariant violation)

### Current CI Targets

**Green models run:**
- `gateway-exposure-v2`, `gateway-exposure-v2-protected`
- `nodes-pipeline`, `approvals-token`
- `pairing`, `pairing-cap`
- `ingress-gating`, `routing-isolation`

**Negative models verified:**
- Same list with `-negative` suffix

## Adding New Models

### Step 1: Create the TLA+ Specification

Create `tla/specs/YourFeatureHarness.tla`:
```tla
---- MODULE YourFeatureHarness ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Users, Channels

VARIABLES state, executed

vars == << state, executed >>

Init == state = "initial" /\ executed = {}

Action == ...

Next == Action \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv_YourProperty == ...

====
```

### Step 2: Create the Model Configuration

Create `tla/models/your_feature_ok.cfg`:
```
SPECIFICATION Spec
INVARIANT Inv_YourProperty
CONSTANTS
  Users = {"alice", "bob"}
  Channels = {"dm", "public"}
```

### Step 3: Add Makefile Target

Add to `Makefile`:
```makefile
your-feature:
	$(TLC) -workers auto -deadlock -config tla/models/your_feature_ok.cfg tla/specs/YourFeatureHarness.tla
```

### Step 4: Create Red Variant (Negative Test)

1. Create `tla/specs/YourFeatureHarness_BadVariant.tla` with intentional bug
2. Create `tla/models/your_feature_negative.cfg`
3. Add `your-feature-negative` target to Makefile

### Step 5: Update CI (if needed)

Add targets to `.github/workflows/tlc.yml` in the appropriate section.

## Common Patterns

### Attacker Harness Pattern

Most security models use an attacker harness pattern:
- Explicit adversary model (attacker sends requests)
- Agent policy (decision logic to allow/deny)
- Execution trace (actions taken)
- Invariant checks (what must not happen)

### State Space Bounding

Use constants to bound state exploration:
```tla
CONSTANTS MaxTime, MaxQueueLen, MaxEvents
```

### Conformance Testing

Models can reference constants extracted from actual Clawdbot source:
- `generated/tool-groups.json` contains tool group definitions
- Scripts handle compatibility aliasing (`group:openclaw` <-> `group:clawdbot`)

## Relationship to Clawdbot

This repo is a **sibling** to the main Clawdbot repository (`../clawdbot/`):
- One-way conformance: scripts extract constants from Clawdbot source
- Models reference code locations like `node-command-policy.ts`, `resolve-route.ts`
- Clawdbot documentation links to findings here

**Planned CI Enhancement (Mode B):** Future CI will check out both repos and verify generated artifacts match committed versions.

## Troubleshooting

### TLC Finds No States

Check that your `Init` predicate is satisfiable with the given constants.

### TLC Runs Forever

- Reduce constant set sizes
- Add state-space bounding constants
- Use `CONSTRAINT` in .cfg to limit exploration

### Java Not Found

The `bin/tlc` wrapper tries multiple Java discovery paths. Ensure Java 11+ is installed:
```bash
java -version
```

### Model Unexpectedly Passes/Fails

- Green model failing: Check for real bugs in the spec
- Red model passing: The intentional bug may not be reachable with current constants

## Quick Reference

| Task | Command |
|------|---------|
| Run all CI targets locally | `make gateway-exposure-v2 pairing ingress-gating routing-isolation` |
| Check specific claim | `make <claim-target>` (see Makefile) |
| Extract conformance data | `node scripts/extract-tool-groups.mjs` |
| View counterexample | TLC outputs trace to stdout on invariant violation |
| List all targets | `grep -E '^[a-z].*:' Makefile` |

## Documentation Files

- `docs/formal-models.md` - How to run, interpret, CI approach
- `docs/security-claims.md` - Claim inventory with invariants
- `docs/verification-roadmap.md` - R1-R5 roadmap
- `docs/nodes-security-notes.md` - NS1-NS5 nodes threat model
- `docs/gateway-exposure-matrix.md` - Gateway test matrix

## Statistics

- TLA+ Specifications: 59 files
- Model Configurations: 78 files
- Intentionally Buggy Variants: ~26 files
- Makefile Targets: 80+
- Security Claims: C1-C6+
- Roadmap Items: R1-R5
