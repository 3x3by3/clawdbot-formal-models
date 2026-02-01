# Formal Models API

Programmatic interface for running TLA+ model checking on Clawdbot security specifications.

## Quick Start

```javascript
import { runModel, listModels, generateReport } from './api/index.mjs';

// List available models
const models = listModels();
console.log(models.map(m => m.name));

// Run a single model
const result = await runModel('pairing', { quiet: true });
console.log(result.success ? 'PASS' : 'FAIL');

// Run all green models for a domain
const results = await runGreenModels({ domain: 'gateway' });
const report = generateReport(results);
console.log(`${report.summary.passed}/${report.summary.total} passed`);
```

## Installation

No installation required - the API uses only Node.js built-in modules. Requires Node.js 18+.

```bash
# Run API tests
node api/test.mjs

# Or via npm
npm run test:api
```

## API Reference

### Model Execution

#### `runModel(targetOrSpec, options?)`

Run TLC model checker on a single model.

```javascript
// Run by target name (from Makefile)
const result = await runModel('pairing');

// Run by spec path with config
const result = await runModel('tla/specs/Custom.tla', {
  config: 'tla/models/custom.cfg',
  workers: 4,
  timeout: 60000,
});
```

**Options:**
- `config` - Path to .cfg file (required if running spec directly)
- `workers` - Number of TLC workers (-1 for auto, default)
- `deadlock` - Enable deadlock checking (default: true)
- `timeout` - Timeout in ms (default: 300000)
- `quiet` - Suppress stdout streaming (default: false)

**Returns:** `ModelResult` object with:
- `success` - true if no violations
- `statesGenerated` - number of states explored
- `distinctStates` - number of unique states
- `durationMs` - execution time
- `violation` - invariant name if violated
- `counterexample` - trace if violation found
- `stdout/stderr` - raw output

#### `runModels(targets, options?)`

Run multiple models in sequence.

```javascript
const results = await runModels(['pairing', 'gateway-auth-conformance']);
```

#### `runGreenModels(options?)`

Run all non-negative (green) models.

```javascript
// All green models
const results = await runGreenModels();

// Green models for specific domain
const results = await runGreenModels({ domain: 'routing' });
```

#### `runRedModels(options?)`

Run all negative (red) models - these are expected to fail.

```javascript
const results = await runRedModels({ domain: 'pairing' });
```

### Discovery

#### `listModels(options?)`

List all available model targets from Makefile.

```javascript
// All models
const all = listModels();

// Only green models
const green = listModels({ includeNegative: false });

// Models for a domain
const pairing = listModels({ domain: 'pairing' });
```

**Returns:** Array of `ModelTarget`:
```javascript
{
  name: 'pairing',
  spec: '/path/to/PairingStoreHarnessV2.tla',
  config: '/path/to/pairing_v2_ok.cfg',
  workers: 1,
  deadlock: true,
  isNegative: false
}
```

#### `listSpecs()`

List all TLA+ specification files.

```javascript
const specs = listSpecs();
// ['/path/to/AttackerHarness.tla', '/path/to/ClawdbotSecurity.tla', ...]
```

#### `listConfigs()`

List all model configuration files.

```javascript
const configs = listConfigs();
// ['/path/to/attacker_ok.cfg', '/path/to/pairing_v2_ok.cfg', ...]
```

#### `listDomains()`

Get unique security domains from model targets.

```javascript
const domains = listDomains();
// ['approvals', 'attacker', 'elevated', 'gateway', 'groups', 'ingress', 'nodes', 'pairing', 'precedence', 'routing']
```

### Parsing

#### `parseTlcOutput(stdout, stderr, exitCode)`

Parse raw TLC output into structured data.

```javascript
const parsed = parseTlcOutput(stdout, stderr, exitCode);
// { success, statesGenerated, distinctStates, violation, counterexample, ... }
```

#### `parseModelTargets()`

Parse Makefile to extract all model targets.

```javascript
const targets = parseModelTargets();
```

#### `parseSpec(specPath)`

Parse a TLA+ specification file.

```javascript
const spec = parseSpec('tla/specs/PairingStoreHarnessV2.tla');
// { moduleName, extends, constants, variables, invariants }
```

#### `parseConfig(configPath)`

Parse a TLC configuration file.

```javascript
const config = parseConfig('tla/models/pairing_v2_ok.cfg');
// { constants, init, next, invariants, specification }
```

### Reporting

#### `validateResult(result, expectSuccess?)`

Validate a model result against expectations.

```javascript
const validation = validateResult(result);
// { passed: true, message: 'pairing: PASS', expected: true, actual: true }
```

For green models, success is expected. For negative models (`*-negative`), failure is expected.

#### `generateReport(results)`

Generate a summary report from multiple results.

```javascript
const report = generateReport(results);
console.log(report.summary);
// { total: 10, passed: 9, failed: 1, passRate: 90 }

console.log(report.stats);
// { totalStatesGenerated: 12345, totalDurationMs: 30000, averageDurationMs: 3000 }

console.log(report.failures);
// [{ passed: false, message: 'pairing: FAIL', ... }]
```

## TypeScript Support

Type definitions are included at `api/index.d.ts`:

```typescript
import { runModel, ModelResult, Report } from './api/index.mjs';

const result: ModelResult = await runModel('pairing');
```

## Examples

### CI Integration

```javascript
import { runGreenModels, generateReport } from './api/index.mjs';

const results = await runGreenModels({ quiet: true });
const report = generateReport(results);

if (report.summary.failed > 0) {
  console.error('Failures:');
  for (const f of report.failures) {
    console.error(`  ${f.message}`);
  }
  process.exit(1);
}

console.log(`All ${report.summary.total} models passed`);
```

### Exploring a Spec

```javascript
import { parseSpec, parseConfig, listModels } from './api/index.mjs';

const models = listModels({ domain: 'pairing' });
for (const model of models) {
  const spec = parseSpec(model.spec);
  const config = parseConfig(model.config);

  console.log(`${model.name}:`);
  console.log(`  Module: ${spec.moduleName}`);
  console.log(`  Invariants checked: ${config.invariants.join(', ')}`);
}
```

### Running with Custom Options

```javascript
import { runModel } from './api/index.mjs';

// Fast check with reduced workers
const result = await runModel('routing-isolation', {
  workers: 1,
  timeout: 60000,
  quiet: true,
});

if (!result.success) {
  console.log('Violation:', result.violation);
  console.log('Counterexample:', result.counterexample);
}
```
