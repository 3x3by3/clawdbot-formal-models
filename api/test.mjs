#!/usr/bin/env node

/**
 * Simple test suite for the Formal Models API
 * Run with: node api/test.mjs
 */

import api from './index.mjs';

const tests = [];
let passed = 0;
let failed = 0;

function test(name, fn) {
  tests.push({ name, fn });
}

function assert(condition, message) {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, got ${actual}`);
  }
}

// Discovery tests

test('listModels returns array', () => {
  const models = api.listModels();
  assert(Array.isArray(models), 'Should return array');
  assert(models.length > 0, 'Should have models');
});

test('listModels filters by domain', () => {
  const pairingModels = api.listModels({ domain: 'pairing' });
  assert(pairingModels.length > 0, 'Should have pairing models');
  assert(
    pairingModels.every((m) => m.name.startsWith('pairing')),
    'All should start with pairing'
  );
});

test('listModels excludes negative when requested', () => {
  const greenOnly = api.listModels({ includeNegative: false });
  assert(
    greenOnly.every((m) => !m.isNegative),
    'Should not include negative models'
  );
});

test('listSpecs returns TLA files', () => {
  const specs = api.listSpecs();
  assert(Array.isArray(specs), 'Should return array');
  assert(specs.length > 0, 'Should have specs');
  assert(
    specs.every((s) => s.endsWith('.tla')),
    'All should be .tla files'
  );
});

test('listConfigs returns CFG files', () => {
  const configs = api.listConfigs();
  assert(Array.isArray(configs), 'Should return array');
  assert(configs.length > 0, 'Should have configs');
  assert(
    configs.every((c) => c.endsWith('.cfg')),
    'All should be .cfg files'
  );
});

test('listDomains returns strings', () => {
  const domains = api.listDomains();
  assert(Array.isArray(domains), 'Should return array');
  assert(domains.length > 0, 'Should have domains');
  assert(domains.includes('pairing'), 'Should include pairing domain');
  assert(domains.includes('gateway'), 'Should include gateway domain');
});

// Parsing tests

test('parseModelTargets extracts targets', () => {
  const targets = api.parseModelTargets();
  assert(Array.isArray(targets), 'Should return array');

  const pairing = targets.find((t) => t.name === 'pairing');
  assert(pairing, 'Should have pairing target');
  assert(pairing.spec.endsWith('.tla'), 'Spec should be .tla');
  assert(pairing.config.endsWith('.cfg'), 'Config should be .cfg');
  assertEqual(pairing.workers, 1, 'Pairing uses 1 worker');
  assertEqual(pairing.deadlock, true, 'Pairing checks deadlock');
  assertEqual(pairing.isNegative, false, 'Pairing is not negative');
});

test('parseTlcOutput parses success', () => {
  const stdout = `
TLC2 Version 2.18
1234 states generated, 567 distinct states found
Model checking completed.
  `;
  const result = api.parseTlcOutput(stdout, '', 0);

  assertEqual(result.success, true, 'Should be success');
  assertEqual(result.statesGenerated, 1234, 'Should parse states generated');
  assertEqual(result.distinctStates, 567, 'Should parse distinct states');
  assertEqual(result.violation, null, 'Should have no violation');
});

test('parseTlcOutput parses violation', () => {
  const stdout = `
TLC2 Version 2.18
Error: Invariant SecurityInvariant is violated
Error: The behavior up to this point is:
State 1: <Init>
State 2: <AttackerActs>
  `;
  const result = api.parseTlcOutput(stdout, '', 1);

  assertEqual(result.success, false, 'Should be failure');
  assertEqual(result.violation, 'SecurityInvariant', 'Should parse violation');
});

test('parseSpec extracts module info', () => {
  const specs = api.listSpecs();
  const spec = api.parseSpec(specs[0]);

  assert(spec.moduleName, 'Should have module name');
  assert(spec.path, 'Should have path');
  assert(Array.isArray(spec.extends), 'Should have extends array');
  assert(Array.isArray(spec.constants), 'Should have constants array');
  assert(Array.isArray(spec.variables), 'Should have variables array');
});

test('parseConfig extracts config info', () => {
  const configs = api.listConfigs();
  const config = api.parseConfig(configs[0]);

  assert(config.path, 'Should have path');
  assert(typeof config.constants === 'object', 'Should have constants object');
});

// Validation tests

test('validateResult handles green model success', () => {
  const result = {
    success: true,
    target: 'pairing',
    violation: null,
  };
  const validation = api.validateResult(result);

  assertEqual(validation.passed, true, 'Green success should pass');
  assertEqual(validation.expected, true, 'Expected success');
  assertEqual(validation.actual, true, 'Actual success');
});

test('validateResult handles green model failure', () => {
  const result = {
    success: false,
    target: 'pairing',
    violation: 'SomeInvariant',
  };
  const validation = api.validateResult(result);

  assertEqual(validation.passed, false, 'Green failure should not pass');
});

test('validateResult handles red model success', () => {
  const result = {
    success: true,
    target: 'pairing-negative',
    violation: null,
  };
  const validation = api.validateResult(result);

  assertEqual(validation.passed, false, 'Red success should not pass');
  assertEqual(validation.expected, false, 'Expected failure');
});

test('validateResult handles red model failure', () => {
  const result = {
    success: false,
    target: 'pairing-negative',
    violation: 'SomeInvariant',
  };
  const validation = api.validateResult(result);

  assertEqual(validation.passed, true, 'Red failure should pass');
});

// Report tests

test('generateReport creates summary', () => {
  const results = [
    { success: true, target: 'pairing', statesGenerated: 100, durationMs: 1000 },
    { success: false, target: 'pairing-negative', statesGenerated: 50, durationMs: 500 },
  ];
  const report = api.generateReport(results);

  assertEqual(report.summary.total, 2, 'Should count total');
  assertEqual(report.summary.passed, 2, 'Both should pass expectations');
  assertEqual(report.stats.totalStatesGenerated, 150, 'Should sum states');
  assertEqual(report.stats.totalDurationMs, 1500, 'Should sum duration');
});

// Run tests

async function runTests() {
  console.log('Running API tests...\n');

  for (const { name, fn } of tests) {
    try {
      await fn();
      console.log(`  \u2713 ${name}`);
      passed++;
    } catch (err) {
      console.log(`  \u2717 ${name}`);
      console.log(`    ${err.message}`);
      failed++;
    }
  }

  console.log(`\n${passed} passed, ${failed} failed`);
  process.exit(failed > 0 ? 1 : 0);
}

runTests();
