import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256;
const CALLS_MAX = 64;
const MEMORY_WORDS = 256;
const STEP_LIMIT = 1_000_000;
const OUTPUT_MAX = 65_536;

// Opcode table: imm | (pops << 4) | (pushes << 8)
const META: Record<number, number> = {
  0: 0, 1: 0x101, 2: 0x104, 3: 0x010, 4: 0x210, 5: 0x220, 6: 0x320, 7: 0x330,
  0x10: 0x120, 0x11: 0x120, 0x12: 0x120, 0x13: 0x120, 0x14: 0x120, 0x15: 0x120, 0x16: 0x120,
  0x17: 0x110, 0x18: 0x120, 0x19: 0x120, 0x1a: 0x120, 0x1b: 0x110, 0x1c: 0x120, 0x1d: 0x120,
  0x1e: 0x120, 0x20: 0x120, 0x21: 0x120, 0x22: 0x120, 0x30: 0x002, 0x31: 0x012, 0x32: 0x012,
  0x33: 0x002, 0x34: 0, 0x40: 0x110, 0x41: 0x020, 0x50: 0x010, 0x51: 0x010, 0x52: 0x100, 0x53: 0x010
};

const enc = new TextEncoder();

function run(p: Uint8Array, input: Uint8Array): { stdout: Uint8Array; exit: number } {
  const n = p.length;
  const D = new Int32Array(STACK_MAX);
  let sp = 0;
  const C = new Int32Array(CALLS_MAX);
  let csp = 0;
  const M = new Int32Array(MEMORY_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;

  const done = (exit: number) => ({ stdout: out.subarray(0, olen), exit });
  const trap = (code: number) => done(code);

  for (;;) {
    if (steps === STEP_LIMIT) return trap(10);
    if (pc < 0 || pc >= n) return trap(9);

    const b = p[pc];
    const meta = META[b];
    if (meta === undefined) return trap(5);

    const imm = meta & 0xf;
    const pops = (meta >> 4) & 0xf;
    const pushes = (meta >> 8) & 0xf;
    if (pc + imm >= n) return trap(9);

    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return trap(2);
    if (sp - pops + pushes > STACK_MAX) return trap(3);

    pc = next;
    switch (b) {
      case 0x00:
        return done(0);
      case 0x01:
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const v2 = D[sp - 1];
        const v1 = D[sp - 2];
        let r = 0;
        if (b === 0x10) r = (v1 + v2) | 0;
        else if (b === 0x11) r = (v1 - v2) | 0;
        else if (b === 0x12) r = Math.imul(v1, v2);
        else if (b === 0x13) {
          if (!v2) return trap(4);
          r = v1 === -2147483648 && v2 === -1 ? v1 : (v1 / v2) | 0;
        } else if (b === 0x14) {
          if (!v2) return trap(4);
          r = v2 === -1 ? 0 : (v1 % v2) | 0;
        } else if (b === 0x15) {
          if (!v2) return trap(4);
          r = Math.floor((v1 >>> 0) / (v2 >>> 0)) | 0;
        } else if (b === 0x16) {
          if (!v2) return trap(4);
          r = (v1 >>> 0) % (v2 >>> 0) | 0;
        } else if (b === 0x18) r = v1 & v2;
        else if (b === 0x19) r = v1 | v2;
        else if (b === 0x1a) r = v1 ^ v2;
        else if (b === 0x1c) r = v1 << (v2 & 31);
        else if (b === 0x1d) r = v1 >> (v2 & 31);
        else if (b === 0x1e) r = (v1 >>> (v2 & 31)) | 0;
        else if (b === 0x20) r = v1 === v2 ? 1 : 0;
        else if (b === 0x21) r = v1 < v2 ? 1 : 0;
        else if (b === 0x22) r = (v1 >>> 0) < (v2 >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (b !== 0x30) {
          const v = D[--sp];
          take = b === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALLS_MAX) return trap(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return trap(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEMORY_WORDS) return trap(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const val = D[sp - 2];
        if (addr < 0 || addr >= MEMORY_WORDS) return trap(6);
        sp -= 2;
        M[addr] = val;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > OUTPUT_MAX) return trap(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUTPUT_MAX) return trap(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53:
        return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    readFileSync(join(I, id, 'program.bin')),
    readFileSync(join(I, id, 'input.bin'))
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.stdout);
  writeFileSync(join(O, id, 'exit.txt'), `${r.exit}\n`);
}
