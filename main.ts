// Tiny stack VM for make.fun's ISA (kit's ISA.md): runs every program in
// /input/<id>/ and writes /output/<id>/stdout.bin + exit.txt. Plain JS in a
// .ts file; only node:fs and node:path are used.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, pops, pushes]; a byte no opcode names traps 5.
const INFO = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSHES = new Int8Array(256);
for (const [op, imm, pops, pushes] of INFO) { IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes; }

// Runs one program on its input bytes; returns bytes written and exit code.
// A trap's code is the exit code, and output written before it is kept.
function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const finish = (code: number) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return finish(5);
    if (pc + imm >= n) return finish(9);
    steps++;
    const next = pc + 1 + imm;
    const pops = POPS[op];
    if (sp < pops) return finish(2);
    if (sp - pops + PUSHES[op] > 256) return finish(3);
    pc = next;
    switch (op) {
      case 0x00: return finish(0);
      case 0x01: stack[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02: stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break;
      case 0x05: { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; break; }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break;
      case 0x07: { const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a; break; }
      case 0x17: stack[sp - 1] = -stack[sp - 1] | 0; break;
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1], a = stack[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; stack[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) { const v = stack[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return finish(7);
        calls[cp++] = next; pc = prog[next - 2] | (prog[next - 1] << 8); break;
      case 0x34:
        if (cp === 0) return finish(8);
        pc = calls[--cp]; break;
      case 0x40: { const addr = stack[sp - 1]; if (addr < 0 || addr > 255) return finish(6); stack[sp - 1] = mem[addr]; break; }
      case 0x41: { const addr = stack[sp - 1]; if (addr < 0 || addr > 255) return finish(6); const v = stack[sp - 2]; sp -= 2; mem[addr] = v; break; }
      case 0x50: {
        const text = String(stack[sp - 1]);
        if (olen + text.length > 65536) return finish(11);
        sp--;
        for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = stack[--sp] & 255; break;
      case 0x52: stack[sp++] = ipos < input.length ? input[ipos++] : -1; break;
      case 0x53: return finish(stack[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const prog = new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin')));
  const input = new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin')));
  const r = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${r.code}\n`);
}
