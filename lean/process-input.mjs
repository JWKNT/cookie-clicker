import { spawnSync } from 'node:child_process';
import { closeSync, mkdtempSync, openSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

/** Feed the complete fixture through a regular file with a definite EOF.
 * A sampled macOS audit stalled in Lean's readToEnd on the spawnSync input pipe.
 * This changes only transport: the executable, bytes, output and exit status
 * remain the checker's inputs and results. No retry hides a failed comparison.
 */
export function spawnSyncWithFileInput(command, args = [], options = {}) {
  if (options.input === undefined) return spawnSync(command, args, options);
  if (options.stdio !== undefined) throw new TypeError('Fixture input requires default output pipes');
  const { input, ...childOptions } = options;
  const directory = mkdtempSync(join(tmpdir(), 'cookie-lean-input-'));
  let descriptor;
  try {
    const path = join(directory, 'input');
    writeFileSync(path, input, { encoding: options.encoding ?? 'utf8' });
    descriptor = openSync(path, 'r');
    return spawnSync(command, args, { ...childOptions, stdio: [descriptor, 'pipe', 'pipe'] });
  } finally {
    if (descriptor !== undefined) closeSync(descriptor);
    rmSync(directory, { recursive: true, force: true });
  }
}
