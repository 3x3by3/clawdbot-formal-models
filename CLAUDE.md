# CLAUDE.md - AI Assistant Guide for clawdbot-formal-models

This document provides essential context for AI assistants working on this repository.

## Project Overview

**clawdbot-formal-models** is a machine-checkable security verification suite for Clawdbot (an AI agent orchestration platform). It uses **TLA+ specifications** verified by the **TLC model checker** to formally prove security properties.

**Core Philosophy**: Treat formal models as a **security regression suite**:
- **Green models**: Intended designs that should pass TLC verification (no invariant violations)
- **Red models**: Deliberately buggy variants that should fail with counterexample traces (proves checks catch real bugs)

## Repository Structure

```
clawdbot-formal-models/
├── tla/
│   ├── specs/           # TLA+ specification files (~59 files)
│   │   ├── ClawdbotSecurityCore.tla   # Core shared definitions
│   │   ├── *Harness.tla               # Green model scenarios
│   │   └── *_Bad*.tla                 # Red model (buggy) variants
│   └── models/          # TLC configuration files (~78 .cfg files)
├── api/                 # Programmatic JavaScript API
│   ├── index.mjs        # Main API implementation
│   ├── index.d.ts       # TypeScript type definitions
│   └── test.mjs         # API unit tests
├── bin/
│   └── tlc              # Bash wrapper for running TLC
├── tools/tla/
│   └── tla2tools.jar    # Vendored TLC model checker
├── scripts/             # Conformance extraction scripts
│   ├── extract-tool-groups.mjs
│   └── gen-tla-cfg-from-tool-groups.mjs
├── generated/           # Generated artifacts (e.g., tool-groups.json)
├── docs/                # Design docs and security claims
├── Makefile             # ~83 make targets for model checking
└── package.json         # Node.js package config (ES modules)
```

## Prerequisites

- **Java 11+** (Java 21 recommended) - required for TLC
- **Node.js 18+** - for API and scripts
- No installation needed - uses vendored `tla2tools.jar`

## Common Commands

### Running Models

```bash
# Run a specific model (green - should pass)
make pairing
make gateway-exposure-v2
make routing-isolation

# Run negative model (red - expected to fail with invariant violation)
make pairing-negative
make gateway-exposure-v2-negative

# Run with custom config
./bin/tlc -workers auto -config tla/models/custom.cfg tla/specs/Custom.tla
```

### API Commands

```bash
# Run API tests
npm run test:api

# List all model targets
npm run list-models

# List security domains
npm run list-domains

# Sync tool groups from Clawdbot implementation
npm run sync
```

### Key Make Targets by Domain

| Domain | Green Target | Red Target |
|--------|--------------|------------|
| Gateway | `gateway-exposure-v2` | `gateway-exposure-v2-negative` |
| Pairing | `pairing`, `pairing-cap` | `pairing-negative`, `pairing-cap-negative` |
| Ingress | `ingress-gating` | `ingress-gating-negative` |
| Routing | `routing-isolation` | `routing-isolation-negative` |
| Nodes | `nodes-pipeline` | `nodes-pipeline-negative` |
| Approvals | `approvals-token` | `approvals-token-negative` |

## Security Domains (Roadmap R1-R5)

| ID | Domain | Purpose |
|----|--------|---------|
| R1 | Pairing Store | DM allowlist semantics, rate limits |
| R2 | Ingress Gating | Channel/group mention gating |
| R3 | Routing | Session isolation, identity linking |
| R4 | Gateway Auth | Network bind/auth configuration |
| R5 | Nodes.run | Approval gates for node execution |

## Naming Conventions

### Spec Files (`tla/specs/`)
- **Green models**: `{Domain}Harness.tla` or `{Domain}HarnessV2.tla`
- **Red models**: `{Domain}Harness_Bad{Description}.tla`
- Example: `PairingStoreHarnessV2.tla` (green), `PairingStoreHarnessV2_BadExpiry.tla` (red)

### Config Files (`tla/models/`)
- Pattern: `{domain}_{variant}_{status}.cfg`
- Green: `pairing_v2_ok.cfg`, `gateway_exposure_v2_safe_loopback.cfg`
- Red: `pairing_v2_negative_badexpiry.cfg`, `gateway_exposure_v2_unsafe_lan_noauth.cfg`

### Make Targets
- Green: `pairing`, `gateway-exposure-v2`, `routing-isolation`
- Red: `pairing-negative`, `gateway-exposure-v2-negative` (append `-negative`)

### Invariants (in TLA+)
- Prefix: `Inv_`
- Examples: `Inv_NoMemoryToolInShared`, `Inv_DenyWins`, `Inv_ApprovalGate`

## TLA+ Spec Structure

A typical spec contains:

```tla
---- MODULE ExampleHarness ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Users, Sessions, Tools, ...    \* Model bounds
VARIABLES state, allowedTools, ...       \* State variables

Init == ...                              \* Initial state predicate
Next == ...                              \* Transition relation

Inv_SecurityProperty == ...              \* Invariant to verify

Spec == Init /\ [][Next]_vars            \* Temporal specification
====
```

## Working with the API

```javascript
import { runModel, listModels, generateReport } from './api/index.mjs';

// List models for a domain
const models = listModels({ domain: 'pairing', includeNegative: false });

// Run a model
const result = await runModel('pairing', { quiet: true });

// Generate report from multiple results
const results = await runGreenModels();
const report = generateReport(results);
```

Key API functions:
- `runModel(target, options?)` - Run single model
- `runGreenModels(options?)` / `runRedModels(options?)` - Run model sets
- `listModels(options?)` - Discover available targets
- `parseSpec(path)` / `parseConfig(path)` - Parse TLA+ files
- `generateReport(results)` - Summary statistics

## CI/CD

GitHub Actions workflow (`.github/workflows/tlc.yml`):
1. Runs on PRs and pushes to main
2. Sets up Java 21
3. Runs green models (must pass)
4. Runs red models (must fail with invariant violations)

Green models in CI:
- `gateway-exposure-v2`, `gateway-exposure-v2-protected`
- `nodes-pipeline`, `approvals-token`
- `pairing`, `pairing-cap`, `ingress-gating`, `routing-isolation`

## Key Patterns

### Adding a New Security Property

1. Create green spec: `tla/specs/{Domain}Harness.tla`
2. Create config: `tla/models/{domain}_ok.cfg`
3. Add make target in `Makefile`
4. Create red variant: `tla/specs/{Domain}Harness_Bad{Bug}.tla`
5. Create negative config and make target
6. Verify: green passes, red fails with expected violation

### Interpreting TLC Output

- **Success**: "Model checking completed. No error has been found."
- **Failure**: "Invariant {Name} is violated" + counterexample trace
- **States**: "X states generated, Y distinct states found"

### Common Gotchas

1. **Workers**: Pairing/routing models use `-workers 1` (deterministic), gateway models use `-workers auto`
2. **Deadlock checking**: Most models use `-deadlock` flag to check for deadlocks
3. **State explosion**: Keep CONSTANTS small (e.g., 2-3 users, 2-3 sessions)
4. **Red model verification**: A red model that passes is a bug - the invariant isn't catching the issue

## File Reference

| File | Purpose |
|------|---------|
| `Makefile` | All 83 model-check targets |
| `bin/tlc` | Java runtime detection + TLC invocation |
| `api/index.mjs` | Full API implementation (~591 lines) |
| `api/index.d.ts` | TypeScript definitions |
| `docs/security-claims.md` | Enumerated security claims (C1-C6+) |
| `docs/verification-roadmap.md` | R1-R5 verification targets |
| `docs/formal-models.md` | How to run and interpret results |

## Dependencies

- **TLC**: Vendored at `tools/tla/tla2tools.jar`
- **Node.js**: Built-in modules only (no npm dependencies)
- **Java**: System-installed, 11+ required

## Quick Reference

```bash
# Verify all critical models pass
make gateway-exposure-v2 && make pairing && make routing-isolation

# Check a red model fails correctly
make pairing-negative  # Should exit non-zero with invariant violation

# Run API tests
npm run test:api

# Sync conformance with Clawdbot
npm run sync
```
