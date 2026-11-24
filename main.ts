// tiny-stack-vm: a small interpreter for make.fun's tiny stack ISA, v1.
// One run answers every instance under /input/<id>/: program.bin and
// input.bin in, stdout.bin and exit.txt out. 32-bit wrapping integers,
// a 256-value stack, a 64-deep call stack, 256 words of memory, at most
// 1,000,000 steps and 65,536 output bytes. Ten traps, each with its own
// exit code; a trap keeps the output written before it.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const STACK_MAX = 256;
const CALL_MAX = 64;
const MEM_WORDS = 256;
const STEP_MAX = 1_000_000;
const OUT_MAX = 65_536;
// [immediate bytes, popped, pushed] per opcode; null for unknown. 0x1f is no opcode.
function info(op: number): [number, number, number] | null {
  if (op === 0x00 || op === 0x34) return [0, 0, 0];
  if (op === 0x01) return [1, 0, 1];
  if (op === 0x02) return [4, 0, 1];
  if (op === 0x03) return [0, 1, 0];
  if (op === 0x04) return [0, 1, 2];
  if (op === 0x05) return [0, 2, 2];
  if (op === 0x06) return [0, 2, 3];
  if (op === 0x07) return [0, 3, 3];
  if (op === 0x17 || op === 0x1b) return [0, 1, 1];
  if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b && op !== 0x1f) return [0, 2, 1];
  if (op === 0x30 || op === 0x33) return [2, 0, 0];
  if (op === 0x31 || op === 0x32) return [2, 1, 0];
  if (op === 0x40) return [0, 1, 1];
  if (op === 0x41) return [0, 2, 0];
  if (op === 0x50 || op === 0x51 || op === 0x53) return [0, 1, 0];
  if (op === 0x52) return [0, 0, 1];
  return null;
}
function run(prog: Uint8Array, inp: Uint8Array): { out: number[]; code: number } {
  const st = new Int32Array(STACK_MAX);
  const cs = new Int32Array(CALL_MAX);
  const mem = new Int32Array(MEM_WORDS);
  const out: number[] = [];
  let sp = 0, cp = 0, pc = 0, ip = 0, steps = 0;
  const trap = (code: number) => ({ out, code });
  for (;;) {
    if (steps >= STEP_MAX) return trap(10);
    if (pc < 0 || pc >= prog.length) return trap(9);
    const op = prog[pc]!;
    const spec = info(op);
    if (spec === null) return trap(5);
    const [imm, pops, pushes] = spec;
    if (pc + imm >= prog.length) return trap(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return trap(2);
    if (sp - pops + pushes > STACK_MAX) return trap(3);
    pc = next;
    switch (op) {
      case 0x00: return { out, code: 0 };
      case 0x01: st[sp++] = (prog[next - 1]! << 24) >> 24; break;
      case 0x02: st[sp++] = prog[next - 4]! | (prog[next - 3]! << 8) | (prog[next - 2]! << 16) | (prog[next - 1]! << 24); break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]!; sp++; break;
      case 0x05: { const t = st[sp - 1]!; st[sp - 1] = st[sp - 2]!; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]!; sp++; break;
      case 0x07: { const a = st[sp - 3]!; st[sp - 3] = st[sp - 2]!; st[sp - 2] = st[sp - 1]!; st[sp - 1] = a; break; }
      case 0x17: st[sp - 1] = -st[sp - 1]! | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]!; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1]!, a = st[sp - 2]!;
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return trap(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return trap(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return trap(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return trap(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; st[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2]! | (prog[next - 1]! << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = st[--sp]!; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp >= CALL_MAX) return trap(7);
        cs[cp++] = next; pc = prog[next - 2]! | (prog[next - 1]! << 8); break;
      case 0x34:
        if (cp === 0) return trap(8);
        pc = cs[--cp]!; break;
      case 0x40: { const addr = st[sp - 1]!; if (addr < 0 || addr >= MEM_WORDS) return trap(6); st[sp - 1] = mem[addr]!; break; }
      case 0x41: { const addr = st[sp - 1]!, v = st[sp - 2]!; if (addr < 0 || addr >= MEM_WORDS) return trap(6); sp -= 2; mem[addr] = v; break; }
      case 0x50: {
        const text = String(st[sp - 1]!);
        if (out.length + text.length > OUT_MAX) return trap(11);
        sp--;
        for (let i = 0; i < text.length; i++) out.push(text.charCodeAt(i));
        break;
      }
      case 0x51:
        if (out.length + 1 > OUT_MAX) return trap(11);
        out.push(st[--sp]! & 255); break;
      case 0x52: st[sp++] = ip < inp.length ? inp[ip++]! : -1; break;
      case 0x53: return { out, code: st[--sp]! & 255 };
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const prog = new Uint8Array(readFileSync(join(dir, 'program.bin')));
  const inp = new Uint8Array(existsSync(join(dir, 'input.bin')) ? readFileSync(join(dir, 'input.bin')) : []);
  const r = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Uint8Array.from(r.out));
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
