/**
 * Clawdbot Formal Models - TypeScript Type Definitions
 */

/**
 * Result of a TLC model check run
 */
export interface ModelResult {
  /** True if no invariant violations found */
  success: boolean;
  /** The make target that was run */
  target: string;
  /** Path to the TLA+ spec file */
  spec: string;
  /** Path to the .cfg model file */
  config: string;
  /** TLC process exit code */
  exitCode: number;
  /** Number of states generated */
  statesGenerated: number;
  /** Number of distinct states */
  distinctStates: number;
  /** Execution time in milliseconds */
  durationMs: number;
  /** Raw stdout output */
  stdout: string;
  /** Raw stderr output */
  stderr: string;
  /** Invariant violation message if any */
  violation: string | null;
  /** Counterexample trace if violation found */
  counterexample: string[] | null;
  /** Additional parsed metadata */
  metadata: ModelMetadata;
}

/**
 * Additional metadata parsed from TLC output
 */
export interface ModelMetadata {
  /** TLC version string */
  tlcVersion?: string;
  /** Whether model checking completed */
  completed?: boolean;
  /** Reported duration from TLC */
  reportedDurationMs?: number;
}

/**
 * Model target definition parsed from Makefile
 */
export interface ModelTarget {
  /** Target name (e.g., 'pairing') */
  name: string;
  /** TLA+ spec file path */
  spec: string;
  /** Model config file path */
  config: string;
  /** Number of TLC workers (-1 for auto) */
  workers: number;
  /** Whether deadlock checking is enabled */
  deadlock: boolean;
  /** Whether this is a negative (red) test */
  isNegative: boolean;
}

/**
 * Parsed TLC output
 */
export interface ParsedTlcOutput {
  /** True if no violations */
  success: boolean;
  /** Number of states generated */
  statesGenerated: number;
  /** Number of distinct states */
  distinctStates: number;
  /** Invariant violation message if any */
  violation: string | null;
  /** Counterexample trace if found */
  counterexample: string[] | null;
  /** Warnings from TLC */
  warnings: string[];
  /** Errors from stderr */
  errors: string[];
  /** Additional metadata */
  metadata: ModelMetadata;
}

/**
 * Options for listing models
 */
export interface ListModelsOptions {
  /** Include negative (red) tests (default: true) */
  includeNegative?: boolean;
  /** Filter by security domain (e.g., 'pairing', 'gateway') */
  domain?: string;
}

/**
 * Options for running a model
 */
export interface RunModelOptions {
  /** Path to .cfg file (required if running spec directly) */
  config?: string;
  /** Number of TLC workers (-1 for auto) */
  workers?: number;
  /** Enable deadlock checking (default: true) */
  deadlock?: boolean;
  /** Timeout in milliseconds (default: 300000) */
  timeout?: number;
  /** Suppress stdout streaming (default: false) */
  quiet?: boolean;
}

/**
 * Options for running multiple models
 */
export interface RunModelsOptions extends RunModelOptions {
  /** Filter by security domain */
  domain?: string;
}

/**
 * Validation result for a model check
 */
export interface ValidationResult {
  /** Whether the result matches expectations */
  passed: boolean;
  /** Human-readable message */
  message: string;
  /** Expected success value */
  expected: boolean;
  /** Actual success value */
  actual: boolean;
  /** Target name */
  target: string;
  /** Invariant violation if any */
  violation: string | null;
}

/**
 * Summary report from multiple model runs
 */
export interface Report {
  /** Summary statistics */
  summary: {
    /** Total number of models run */
    total: number;
    /** Number of passed models */
    passed: number;
    /** Number of failed models */
    failed: number;
    /** Pass rate as percentage */
    passRate: number;
  };
  /** Aggregate statistics */
  stats: {
    /** Total states generated across all models */
    totalStatesGenerated: number;
    /** Total duration in milliseconds */
    totalDurationMs: number;
    /** Average duration per model */
    averageDurationMs: number;
  };
  /** All validation results */
  results: ValidationResult[];
  /** Only failed validations */
  failures: ValidationResult[];
}

/**
 * Parsed TLA+ spec information
 */
export interface ParsedSpec {
  /** Path to spec file */
  path: string;
  /** Module name */
  moduleName: string;
  /** Extended modules */
  extends: string[];
  /** Declared constants */
  constants: string[];
  /** Declared variables */
  variables: string[];
  /** Invariant definitions */
  invariants: string[];
}

/**
 * Parsed TLC config information
 */
export interface ParsedConfig {
  /** Path to config file */
  path: string;
  /** Constant assignments */
  constants: Record<string, string>;
  /** Init predicate name */
  init: string | null;
  /** Next predicate name */
  next: string | null;
  /** Invariant names */
  invariants: string[];
  /** Specification name */
  specification: string | null;
}

// Model execution functions

/**
 * Run TLC model checker
 */
export function runModel(
  targetOrSpec: string,
  options?: RunModelOptions
): Promise<ModelResult>;

/**
 * Run multiple models in sequence
 */
export function runModels(
  targets: string[],
  options?: RunModelOptions
): Promise<ModelResult[]>;

/**
 * Run all green (non-negative) models
 */
export function runGreenModels(options?: RunModelsOptions): Promise<ModelResult[]>;

/**
 * Run all red (negative) models - these should fail
 */
export function runRedModels(options?: RunModelsOptions): Promise<ModelResult[]>;

// Discovery functions

/**
 * List all available model targets
 */
export function listModels(options?: ListModelsOptions): ModelTarget[];

/**
 * List all TLA+ spec files
 */
export function listSpecs(): string[];

/**
 * List all model configuration files
 */
export function listConfigs(): string[];

/**
 * Get security domains from model targets
 */
export function listDomains(): string[];

// Parsing functions

/**
 * Parse TLC output to extract structured results
 */
export function parseTlcOutput(
  stdout: string,
  stderr: string,
  exitCode: number
): ParsedTlcOutput;

/**
 * Parse Makefile to extract all model targets
 */
export function parseModelTargets(): ModelTarget[];

/**
 * Read and parse a TLA+ spec file
 */
export function parseSpec(specPath: string): ParsedSpec;

/**
 * Read and parse a TLC config file
 */
export function parseConfig(configPath: string): ParsedConfig;

// Reporting functions

/**
 * Validate that a model result matches expectations
 */
export function validateResult(
  result: ModelResult,
  expectSuccess?: boolean
): ValidationResult;

/**
 * Generate a summary report from multiple model results
 */
export function generateReport(results: ModelResult[]): Report;

// Default export
declare const api: {
  runModel: typeof runModel;
  runModels: typeof runModels;
  runGreenModels: typeof runGreenModels;
  runRedModels: typeof runRedModels;
  listModels: typeof listModels;
  listSpecs: typeof listSpecs;
  listConfigs: typeof listConfigs;
  listDomains: typeof listDomains;
  parseTlcOutput: typeof parseTlcOutput;
  parseModelTargets: typeof parseModelTargets;
  parseSpec: typeof parseSpec;
  parseConfig: typeof parseConfig;
  validateResult: typeof validateResult;
  generateReport: typeof generateReport;
};

export default api;
