// tiny-stack-vm-01 entry: interpreter of make.fun's tiny stack ISA (ISA.md), following the reference VM's rules
// exactly — 32-bit wrapping, signed/unsigned divides, every trap code, step/output limits, trapped output kept.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const SM = 256, CM = 64, MW = 256, SL = 1e6, OM = 65536;

function run(p: Uint8Array, inp: Uint8Array) {
  const D = new Int32Array(SM), C = new Int32Array(CM), M = new Int32Array(MW);
  const o = new Uint8Array(OM);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const n = p.length;
  const fin = (exit: number) => ({ stdout: o.subarray(0, ol), exit });
  const tr = (c: number) => fin(c);
  // imm bytes, pops, pushes per opcode; -1 pops/pushes = computed per op
  const T = new Int16Array(256).fill(-99);
  const set = (b: number, i: number, po: number, pu: number) => { T[b] = i * 100 + po * 10 + pu; };
  set(0x00, 0, 0, 0); set(0x01, 1, 0, 1); set(0x02, 4, 0, 1); set(0x03, 0, 1, 0); set(0x04, 0, 1, 2);
  set(0x05, 0, 2, 2); set(0x06, 0, 2, 3); set(0x07, 0, 3, 3);
  for (const b of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) set(b, 0, 2, 1);
  set(0x17, 0, 1, 1); set(0x1b, 0, 1, 1);
  set(0x30, 2, 0, 0); set(0x31, 2, 1, 0); set(0x32, 2, 1, 0); set(0x33, 2, 0, 0); set(0x34, 0, 0, 0);
  set(0x40, 0, 1, 1); set(0x41, 0, 2, 0); set(0x50, 0, 1, 0); set(0x51, 0, 1, 0);
  set(0x52, 0, 0, 1); set(0x53, 0, 1, 0);
  for (;;) {
    if (st === SL) return tr(10);
    if (pc < 0 || pc >= n) return tr(9);
    const t = T[p[pc]];
    if (t === -99) return tr(5);
    const imm = (t / 100) | 0, po = ((t / 10) | 0) % 10, pu = t % 10;
    if (pc + imm >= n) return tr(9);
    st++;
    const nx = pc + 1 + imm;
    if (sp < po) return tr(2);
    if (sp - po + pu > SM) return tr(3);
    const op = p[pc];
    pc = nx;
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === CM) return tr(7);
        C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:
        if (cp === 0) return tr(8);
        pc = C[--cp]; break;
      case 0x40: {
        const ad = D[sp - 1];
        if (ad < 0 || ad >= MW) return tr(6);
        D[sp - 1] = M[ad]; break;
      }
      case 0x41: {
        const ad = D[sp - 1], v = D[sp - 2];
        if (ad < 0 || ad >= MW) return tr(6);
        sp -= 2; M[ad] = v; break;
      }
      case 0x50: {
        const b = Buffer.from(String(D[sp - 1]), 'utf8');
        if (ol + b.length > OM) return tr(11);
        sp--; o.set(b, ol); ol += b.length; break;
      }
      case 0x51:
        if (ol + 1 > OM) return tr(11);
        o[ol++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return fin(D[--sp] & 255);
      default: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return tr(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14:
            if (b === 0) return tr(4);
            r = b === -1 ? 0 : a % b | 0; break;
          case 0x15:
            if (b === 0) return tr(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16:
            if (b === 0) return tr(4);
            r = (a >>> 0) % (b >>> 0) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = a >>> 0 < b >>> 0 ? 1 : 0; break;
          default: return tr(5);
        }
        sp -= 2; D[sp++] = r; break;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  mkdirSync(join(O, id), { recursive: true });
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  writeFileSync(join(O, id, 'stdout.bin'), r.stdout);
  writeFileSync(join(O, id, 'exit.txt'), r.exit + '\n');
}
