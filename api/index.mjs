/**
 * Clawdbot Formal Models - Code API
 *
 * Programmatic interface for running TLA+ model checking,
 * parsing results, and discovering available models.
 *
 * @example
 * import { runModel, listModels, parseResult } from './api/index.mjs';
 *
 * const result = await runModel('pairing');
 * console.log(result.success); // true if no violations
 */

import { spawn } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT_DIR = path.resolve(__dirname, '..');
const TLC_BIN = path.join(ROOT_DIR, 'bin', 'tlc');
const SPECS_DIR = path.join(ROOT_DIR, 'tla', 'specs');
const MODELS_DIR = path.join(ROOT_DIR, 'tla', 'models');
const MAKEFILE_PATH = path.join(ROOT_DIR, 'Makefile');

/**
 * Result of a TLC model check run
 * @typedef {Object} ModelResult
 * @property {boolean} success - True if no invariant violations found
 * @property {string} target - The make target that was run
 * @property {string} spec - Path to the TLA+ spec file
 * @property {string} config - Path to the .cfg model file
 * @property {number} exitCode - TLC process exit code
 * @property {number} statesGenerated - Number of states generated
 * @property {number} distinctStates - Number of distinct states
 * @property {number} durationMs - Execution time in milliseconds
 * @property {string} stdout - Raw stdout output
 * @property {string} stderr - Raw stderr output
 * @property {string|null} violation - Invariant violation message if any
 * @property {string[]|null} counterexample - Counterexample trace if violation found
 * @property {Object} metadata - Additional parsed metadata
 */

/**
 * Model target definition parsed from Makefile
 * @typedef {Object} ModelTarget
 * @property {string} name - Target name (e.g., 'pairing')
 * @property {string} spec - TLA+ spec file path
 * @property {string} config - Model config file path
 * @property {number} workers - Number of TLC workers
 * @property {boolean} deadlock - Whether deadlock checking is enabled
 * @property {boolean} isNegative - Whether this is a negative (red) test
 */

/**
 * Parse TLC output to extract structured results
 * @param {string} stdout - Raw TLC stdout
 * @param {string} stderr - Raw TLC stderr
 * @param {number} exitCode - TLC exit code
 * @returns {Object} Parsed result data
 */
export function parseTlcOutput(stdout, stderr, exitCode) {
  const result = {
    success: exitCode === 0,
    statesGenerated: 0,
    distinctStates: 0,
    violation: null,
    counterexample: null,
    warnings: [],
    errors: [],
    metadata: {},
  };

  // Parse state counts
  const statesMatch = stdout.match(/(\d+)\s+states?\s+generated[^,]*,\s*(\d+)\s+distinct/i);
  if (statesMatch) {
    result.statesGenerated = parseInt(statesMatch[1], 10);
    result.distinctStates = parseInt(statesMatch[2], 10);
  }

  // Parse finish status
  const finishedMatch = stdout.match(/Model checking completed\./i);
  result.metadata.completed = !!finishedMatch;

  // Parse invariant violation
  const violationMatch = stdout.match(/Error:\s*Invariant\s+(\w+)\s+is\s+violated/i);
  if (violationMatch) {
    result.success = false;
    result.violation = violationMatch[1];
  }

  // Also check for assertion violations
  const assertionMatch = stdout.match(/Error:\s*The\s+following\s+assertion\s+is\s+violated/i);
  if (assertionMatch) {
    result.success = false;
    result.violation = result.violation || 'Assertion violated';
  }

  // Parse counterexample trace
  const traceStart = stdout.indexOf('Error: The behavior up to this point is:');
  if (traceStart !== -1) {
    const traceSection = stdout.slice(traceStart);
    const stateMatches = traceSection.match(/State\s+\d+:\s*<[^>]+>/g);
    if (stateMatches) {
      result.counterexample = stateMatches;
    }
  }

  // Parse warnings
  const warningMatches = stdout.matchAll(/Warning:\s*(.+)/gi);
  for (const match of warningMatches) {
    result.warnings.push(match[1].trim());
  }

  // Parse errors from stderr
  if (stderr) {
    const errorLines = stderr.split('\n').filter((line) => line.trim());
    result.errors = errorLines;
  }

  // Parse TLC version
  const versionMatch = stdout.match(/TLC2\s+Version\s+([\d.]+)/i);
  if (versionMatch) {
    result.metadata.tlcVersion = versionMatch[1];
  }

  // Parse running time
  const timeMatch = stdout.match(/Finished\s+in\s+(\d+)ms/i);
  if (timeMatch) {
    result.metadata.reportedDurationMs = parseInt(timeMatch[1], 10);
  }

  return result;
}

/**
 * Parse Makefile to extract all model targets
 * @returns {ModelTarget[]} Array of model targets
 */
export function parseModelTargets() {
  const makefile = fs.readFileSync(MAKEFILE_PATH, 'utf8');
  const targets = [];

  // Match target definitions like:
  // pairing:
  //   $(TLC) -workers 1 -deadlock -config tla/models/pairing_v2_ok.cfg tla/specs/PairingStoreHarnessV2.tla
  const targetPattern = /^([a-z][a-z0-9_-]*):\s*\n\s*\$\(TLC\)\s+(.+)/gim;
  let match;

  while ((match = targetPattern.exec(makefile)) !== null) {
    const name = match[1];
    const command = match[2];

    // Skip the generic 'tlc' target
    if (name === 'tlc') continue;

    // Parse command options
    const workersMatch = command.match(/-workers\s+(\w+)/);
    const workers = workersMatch
      ? workersMatch[1] === 'auto'
        ? -1
        : parseInt(workersMatch[1], 10)
      : -1;

    const deadlock = command.includes('-deadlock');

    const configMatch = command.match(/-config\s+(\S+)/);
    const config = configMatch ? configMatch[1] : null;

    const specMatch = command.match(/(\S+\.tla)\s*$/);
    const spec = specMatch ? specMatch[1] : null;

    if (config && spec) {
      targets.push({
        name,
        spec: path.join(ROOT_DIR, spec),
        config: path.join(ROOT_DIR, config),
        workers,
        deadlock,
        isNegative: name.includes('-negative'),
      });
    }
  }

  return targets;
}

/**
 * List all available model targets
 * @param {Object} options - Filter options
 * @param {boolean} [options.includeNegative=true] - Include negative (red) tests
 * @param {string} [options.domain] - Filter by security domain (e.g., 'pairing', 'gateway')
 * @returns {ModelTarget[]} Array of model targets
 */
export function listModels(options = {}) {
  const { includeNegative = true, domain } = options;
  let targets = parseModelTargets();

  if (!includeNegative) {
    targets = targets.filter((t) => !t.isNegative);
  }

  if (domain) {
    const domainLower = domain.toLowerCase();
    targets = targets.filter((t) => t.name.startsWith(domainLower));
  }

  return targets;
}

/**
 * List all TLA+ spec files
 * @returns {string[]} Array of spec file paths
 */
export function listSpecs() {
  const files = fs.readdirSync(SPECS_DIR);
  return files
    .filter((f) => f.endsWith('.tla'))
    .map((f) => path.join(SPECS_DIR, f))
    .sort();
}

/**
 * List all model configuration files
 * @returns {string[]} Array of config file paths
 */
export function listConfigs() {
  const files = fs.readdirSync(MODELS_DIR);
  return files
    .filter((f) => f.endsWith('.cfg'))
    .map((f) => path.join(MODELS_DIR, f))
    .sort();
}

/**
 * Get security domains from model targets
 * @returns {string[]} Array of unique domain names
 */
export function listDomains() {
  const targets = parseModelTargets();
  const domains = new Set();

  for (const target of targets) {
    // Extract domain from target name (e.g., 'pairing-cap-negative' -> 'pairing')
    const baseName = target.name.replace(/-negative$/, '');
    const domain = baseName.split('-')[0];
    domains.add(domain);
  }

  return Array.from(domains).sort();
}

/**
 * Run TLC model checker
 * @param {string} targetOrSpec - Make target name OR path to TLA+ spec
 * @param {Object} options - Run options
 * @param {string} [options.config] - Path to .cfg file (required if targetOrSpec is a spec path)
 * @param {number} [options.workers] - Number of TLC workers (-1 for auto)
 * @param {boolean} [options.deadlock=true] - Enable deadlock checking
 * @param {number} [options.timeout=300000] - Timeout in milliseconds (default 5 min)
 * @param {boolean} [options.quiet=false] - Suppress stdout streaming
 * @returns {Promise<ModelResult>} Model check result
 */
export async function runModel(targetOrSpec, options = {}) {
  const startTime = Date.now();

  // Determine if this is a target name or a spec path
  let spec, config, workers, deadlock;

  if (targetOrSpec.endsWith('.tla')) {
    // Direct spec path
    spec = path.resolve(targetOrSpec);
    config = options.config ? path.resolve(options.config) : null;
    workers = options.workers ?? -1;
    deadlock = options.deadlock ?? true;

    if (!config) {
      throw new Error('config option is required when running a spec directly');
    }
  } else {
    // Target name - look it up
    const targets = parseModelTargets();
    const target = targets.find((t) => t.name === targetOrSpec);

    if (!target) {
      const available = targets.map((t) => t.name).join(', ');
      throw new Error(`Unknown target: ${targetOrSpec}. Available: ${available}`);
    }

    spec = target.spec;
    config = target.config;
    workers = options.workers ?? target.workers;
    deadlock = options.deadlock ?? target.deadlock;
  }

  // Build TLC arguments
  const args = [];

  if (workers === -1) {
    args.push('-workers', 'auto');
  } else {
    args.push('-workers', String(workers));
  }

  if (deadlock) {
    args.push('-deadlock');
  }

  args.push('-config', config);
  args.push(spec);

  // Run TLC
  const timeout = options.timeout ?? 300000;
  const quiet = options.quiet ?? false;

  return new Promise((resolve, reject) => {
    const proc = spawn(TLC_BIN, args, {
      cwd: ROOT_DIR,
      timeout,
    });

    let stdout = '';
    let stderr = '';

    proc.stdout.on('data', (data) => {
      const chunk = data.toString();
      stdout += chunk;
      if (!quiet) {
        process.stdout.write(chunk);
      }
    });

    proc.stderr.on('data', (data) => {
      const chunk = data.toString();
      stderr += chunk;
      if (!quiet) {
        process.stderr.write(chunk);
      }
    });

    proc.on('close', (exitCode) => {
      const durationMs = Date.now() - startTime;
      const parsed = parseTlcOutput(stdout, stderr, exitCode ?? 0);

      resolve({
        success: parsed.success,
        target: targetOrSpec,
        spec,
        config,
        exitCode: exitCode ?? 0,
        statesGenerated: parsed.statesGenerated,
        distinctStates: parsed.distinctStates,
        durationMs,
        stdout,
        stderr,
        violation: parsed.violation,
        counterexample: parsed.counterexample,
        metadata: parsed.metadata,
      });
    });

    proc.on('error', (err) => {
      reject(new Error(`Failed to spawn TLC: ${err.message}`));
    });
  });
}

/**
 * Run multiple models in sequence
 * @param {string[]} targets - Array of target names
 * @param {Object} options - Run options (same as runModel)
 * @returns {Promise<ModelResult[]>} Array of results
 */
export async function runModels(targets, options = {}) {
  const results = [];

  for (const target of targets) {
    const result = await runModel(target, options);
    results.push(result);
  }

  return results;
}

/**
 * Run all green (non-negative) models
 * @param {Object} options - Run options
 * @param {string} [options.domain] - Filter by domain
 * @returns {Promise<ModelResult[]>} Array of results
 */
export async function runGreenModels(options = {}) {
  const targets = listModels({ includeNegative: false, domain: options.domain });
  return runModels(
    targets.map((t) => t.name),
    options
  );
}

/**
 * Run all red (negative) models - these should fail
 * @param {Object} options - Run options
 * @param {string} [options.domain] - Filter by domain
 * @returns {Promise<ModelResult[]>} Array of results
 */
export async function runRedModels(options = {}) {
  let targets = listModels({ includeNegative: true, domain: options.domain });
  targets = targets.filter((t) => t.isNegative);
  return runModels(
    targets.map((t) => t.name),
    options
  );
}

/**
 * Validate that a model result matches expectations
 * @param {ModelResult} result - Model check result
 * @param {boolean} expectSuccess - Whether success is expected
 * @returns {Object} Validation result
 */
export function validateResult(result, expectSuccess) {
  const isNegative = result.target.includes('-negative');
  const expectedSuccess = expectSuccess ?? !isNegative;

  const passed = result.success === expectedSuccess;
  const message = passed
    ? `${result.target}: PASS`
    : `${result.target}: FAIL (expected ${expectedSuccess ? 'success' : 'failure'}, got ${result.success ? 'success' : 'failure'})`;

  return {
    passed,
    message,
    expected: expectedSuccess,
    actual: result.success,
    target: result.target,
    violation: result.violation,
  };
}

/**
 * Generate a summary report from multiple model results
 * @param {ModelResult[]} results - Array of model results
 * @returns {Object} Summary report
 */
export function generateReport(results) {
  const validations = results.map((r) => validateResult(r));

  const passed = validations.filter((v) => v.passed).length;
  const failed = validations.filter((v) => !v.passed).length;

  const totalStates = results.reduce((sum, r) => sum + r.statesGenerated, 0);
  const totalDuration = results.reduce((sum, r) => sum + r.durationMs, 0);

  return {
    summary: {
      total: results.length,
      passed,
      failed,
      passRate: results.length > 0 ? (passed / results.length) * 100 : 0,
    },
    stats: {
      totalStatesGenerated: totalStates,
      totalDurationMs: totalDuration,
      averageDurationMs: results.length > 0 ? totalDuration / results.length : 0,
    },
    results: validations,
    failures: validations.filter((v) => !v.passed),
  };
}

/**
 * Read and parse a TLA+ spec file
 * @param {string} specPath - Path to TLA+ spec
 * @returns {Object} Parsed spec info
 */
export function parseSpec(specPath) {
  const content = fs.readFileSync(specPath, 'utf8');

  // Extract module name
  const moduleMatch = content.match(/----\s*MODULE\s+(\w+)\s*----/);
  const moduleName = moduleMatch ? moduleMatch[1] : path.basename(specPath, '.tla');

  // Extract EXTENDS
  const extendsMatch = content.match(/EXTENDS\s+([^\n]+)/);
  const extends_ = extendsMatch
    ? extendsMatch[1].split(',').map((s) => s.trim())
    : [];

  // Extract CONSTANTS
  const constantsMatch = content.match(/CONSTANTS?\s+([^\n]+(?:\n\s+[^\n]+)*)/);
  const constants = constantsMatch
    ? constantsMatch[1]
        .split(/[,\n]/)
        .map((s) => s.trim())
        .filter(Boolean)
    : [];

  // Extract VARIABLES
  const variablesMatch = content.match(/VARIABLES?\s+([^\n]+(?:\n\s+[^\n]+)*)/);
  const variables = variablesMatch
    ? variablesMatch[1]
        .split(/[,\n]/)
        .map((s) => s.trim())
        .filter(Boolean)
    : [];

  // Extract invariants (definitions ending with Inv or Invariant)
  const invariantMatches = content.matchAll(/^(\w+(?:Inv|Invariant))\s*==/gm);
  const invariants = Array.from(invariantMatches, (m) => m[1]);

  return {
    path: specPath,
    moduleName,
    extends: extends_,
    constants,
    variables,
    invariants,
  };
}

/**
 * Read and parse a TLC config file
 * @param {string} configPath - Path to .cfg file
 * @returns {Object} Parsed config info
 */
export function parseConfig(configPath) {
  const content = fs.readFileSync(configPath, 'utf8');

  // Extract CONSTANTS section
  const constantsMatch = content.match(/CONSTANTS?\s*\n([\s\S]*?)(?=\n(?:INIT|NEXT|INVARIANT|PROPERTY|SPECIFICATION|\*|$))/i);
  const constantsSection = constantsMatch ? constantsMatch[1] : '';

  const constants = {};
  const constLines = constantsSection.split('\n');
  for (const line of constLines) {
    const match = line.match(/^\s*(\w+)\s*=\s*(.+)\s*$/);
    if (match) {
      constants[match[1]] = match[2].trim();
    }
  }

  // Extract INIT
  const initMatch = content.match(/INIT\s+(\w+)/i);
  const init = initMatch ? initMatch[1] : null;

  // Extract NEXT
  const nextMatch = content.match(/NEXT\s+(\w+)/i);
  const next = nextMatch ? nextMatch[1] : null;

  // Extract INVARIANT(S)
  const invariantMatches = content.matchAll(/INVARIANTS?\s+(\w+)/gi);
  const invariants = Array.from(invariantMatches, (m) => m[1]);

  // Extract SPECIFICATION
  const specMatch = content.match(/SPECIFICATION\s+(\w+)/i);
  const specification = specMatch ? specMatch[1] : null;

  return {
    path: configPath,
    constants,
    init,
    next,
    invariants,
    specification,
  };
}

// Default export for convenience
export default {
  // Model execution
  runModel,
  runModels,
  runGreenModels,
  runRedModels,

  // Discovery
  listModels,
  listSpecs,
  listConfigs,
  listDomains,

  // Parsing
  parseTlcOutput,
  parseModelTargets,
  parseSpec,
  parseConfig,

  // Reporting
  validateResult,
  generateReport,
};
