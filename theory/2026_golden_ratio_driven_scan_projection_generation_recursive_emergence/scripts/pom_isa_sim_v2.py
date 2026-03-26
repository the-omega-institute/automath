#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
POM ISA reference simulator (latest, experiment-ready).

This script is an experiment-layer ISA/microcode simulator aligned with the paper's
cost decomposition and signature philosophy:

  Σ(I)  ~  (projection-word + kernel choice + fiber choice)
  and the projection-gate part is made auditable by explicit counters.

Key experiment hooks:
  - PROJ_CHI: explicit P_χ projection gate (k_χ counter) for τ_mix scaling studies.
  - ZDIVMOD: two true-microcode routes for the order gate P_≤:
      * ZDIVMOD_LD  : binary long division (k_≤ grows ~ linearly in quotient bits)
      * ZDIVMOD_REC : fixed-point reciprocal Newton iteration (k_≤ ~ constant; growth moved into D_U)
  - --mulmode {const,log,serial}: multiplication-depth model for ZMUL / REC microcode.
  - support: RESCALE↓/gauge support budget via G_m accumulation (WGAUGE/WREM).
  - capbits: cap stored Z magnitudes for long programs without changing gate counters;
             D_U uses a logical bit-size proxy tracked separately from capped values.

32-bit encoding:
  R: opcode(6) | rd(5) | rs1(5) | rs2(5) | imm11(11)
  I: opcode(6) | rd(5) | rs1(5) | imm16(16)
  J: opcode(6) | imm26(26)

Run:
  python3 pom_isa_sim_v2.py --demo --capbits 32 --mulmode log
  python3 pom_isa_sim_v2.py --bench-div --bits-a 1024 --bits-b 256 --iters 120 --mulmode log
  python3 pom_isa_sim_v2.py --gauge --m 10 --trials 20000
  python3 pom_isa_sim_v2.py --workload --len 6000 --seed 7 --capbits 32 --divmode mixed
"""

from __future__ import annotations

import argparse
import dataclasses
import math
import random
import re
import sys
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


U32_MASK = 0xFFFF_FFFF


# =========================
# Fibonacci / Zeckendorf
# =========================


def _fib_up_to_index(n: int) -> List[int]:
    """Return [F0, F1, ..., Fn] with F0=0,F1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    fibs = [0, 1]
    while len(fibs) <= n:
        fibs.append(fibs[-1] + fibs[-2])
    return fibs


def _fib_weights(m: int) -> List[int]:
    """Return weights for positions k=1..m: (F_{k+1}) = (F2..F_{m+1})."""
    if m < 0:
        raise ValueError("m must be >= 0")
    fibs = _fib_up_to_index(m + 1)
    return fibs[2 : (m + 2)]


def zeckendorf_bits_nonneg(n: int) -> List[int]:
    """Greedy Zeckendorf bits for n>=0 (low-to-high, weights F2,F3,...)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return []
    fibs = [1, 2]  # F2, F3
    while fibs[-1] <= n:
        fibs.append(fibs[-1] + fibs[-2])
    if fibs[-1] > n:
        fibs.pop()
    bits = [0] * len(fibs)
    rem = n
    i = len(fibs) - 1
    while rem > 0 and i >= 0:
        if fibs[i] <= rem:
            bits[i] = 1
            rem -= fibs[i]
            i -= 2
        else:
            i -= 1
    return bits


def _pack_bits(bits: Sequence[int], m: int) -> int:
    x = 0
    for i in range(min(m, len(bits))):
        if bits[i] & 1:
            x |= 1 << i
    return x


def fold_infty_int(x: int) -> int:
    """Fold_∞ as P_Z. Truth layer keeps integer value; cost counted via k_Z."""
    return int(x)


def window_N(omega_bits: int, m: int) -> int:
    """N(ω)=Σ ω_k F_{k+1} for packed bits ω (low-to-high)."""
    weights = _fib_weights(m)
    s = 0
    for i, w in enumerate(weights):
        if (omega_bits >> i) & 1:
            s += w
    return s


def fold_m_bits(omega_bits: int, m: int) -> int:
    """Fold_m(ω)=π_m(Z(N(ω))) as packed m-bit Zeckendorf-legal output."""
    N = window_N(omega_bits, m)
    zb = zeckendorf_bits_nonneg(N)
    if len(zb) < m:
        zb = list(zb) + [0] * (m - len(zb))
    return _pack_bits(zb[:m], m=m)


def fold_m_int(omega_bits: int, m: int) -> int:
    """Embed Fold_m output back to ℤ via Σ bit_k F_{k+1}."""
    fb = fold_m_bits(omega_bits, m)
    weights = _fib_weights(m)
    s = 0
    for i, w in enumerate(weights):
        if (fb >> i) & 1:
            s += w
    return s


def rem_mplus1_to_m_bits(omega_bits_mplus1: int, m: int) -> int:
    """rem_{m+1→m}(ω)=π_{m+1→m}(Fold_{m+1}(ω))."""
    folded = fold_m_bits(omega_bits_mplus1, m + 1)
    return folded & ((1 << m) - 1) if m > 0 else 0


def trunc_mplus1_to_m_bits(omega_bits_mplus1: int, m: int) -> int:
    """r_{m+1→m}(ω): naive truncation of top bit."""
    return omega_bits_mplus1 & ((1 << m) - 1) if m > 0 else 0


def gauge_Gm(omega_bits_mplus1: int, m: int) -> int:
    """G_m(ω)=|r ⊕ rem|_0 (Hamming weight)."""
    r = trunc_mplus1_to_m_bits(omega_bits_mplus1, m)
    rem = rem_mplus1_to_m_bits(omega_bits_mplus1, m)
    return int((r ^ rem).bit_count())


# =========================
# Prime vectors (P regs)
# =========================


@dataclass
class PrimeVector:
    sign: int  # -1,0,+1
    exps: Dict[int, int]  # prime -> exponent (>=0)

    def copy(self) -> "PrimeVector":
        return PrimeVector(sign=int(self.sign), exps=dict(self.exps))


def _factorize_abs(n: int) -> Dict[int, int]:
    x = abs(int(n))
    exps: Dict[int, int] = {}
    if x in (0, 1):
        return exps
    p = 2
    while p * p <= x:
        while x % p == 0:
            exps[p] = exps.get(p, 0) + 1
            x //= p
        p = 3 if p == 2 else p + 2
    if x > 1:
        exps[x] = exps.get(x, 0) + 1
    return exps


def primevec_from_int(z: int) -> PrimeVector:
    z = int(z)
    if z == 0:
        return PrimeVector(sign=0, exps={})
    sign = -1 if z < 0 else 1
    return PrimeVector(sign=sign, exps=_factorize_abs(z))


def int_from_primevec(pv: PrimeVector) -> int:
    if pv.sign == 0:
        return 0
    x = 1
    for p, e in sorted(pv.exps.items()):
        if e <= 0:
            continue
        x *= int(p) ** int(e)
    return int(pv.sign) * x


def primevec_mul(a: PrimeVector, b: PrimeVector) -> PrimeVector:
    if a.sign == 0 or b.sign == 0:
        return PrimeVector(sign=0, exps={})
    out = a.copy()
    out.sign = int(a.sign) * int(b.sign)
    for p, e in b.exps.items():
        out.exps[p] = int(out.exps.get(p, 0)) + int(e)
    return out


def primevec_div_checked(a: PrimeVector, b: PrimeVector) -> PrimeVector:
    if b.sign == 0:
        raise ZeroDivisionError("PDIV by zero prime-vector (represents 0)")
    if a.sign == 0:
        return PrimeVector(sign=0, exps={})
    out = a.copy()
    out.sign = int(a.sign) * int(b.sign)
    for p, e in b.exps.items():
        cur = int(out.exps.get(p, 0))
        ne = cur - int(e)
        if ne < 0:
            raise ValueError(f"PDIV underflow at prime {p}: {cur} - {int(e)} < 0")
        if ne == 0:
            out.exps.pop(p, None)
        else:
            out.exps[p] = ne
    return out


# =========================
# ISA: encoding / decoding
# =========================


class Opcode:
    # Core control
    NOP = 0
    HALT = 1
    # Z-visible
    ZLI = 2
    ZMOV = 3
    ZFOLD = 4
    ZADD = 5
    ZSUB = 6
    ZMUL = 7
    ZDIVQ = 8
    ZDIVR = 9
    # W micro-visible
    WSETM = 10
    WLI = 11
    WFOLD = 12
    WREM = 13
    WTRUNC = 14
    WGAUGE = 15
    # P optional
    Z2P = 16
    P2Z = 17
    PMUL = 18
    PDIV = 19
    # v2: explicit P_chi hook + divmod routes
    PROJ_CHI = 20
    ZDIVMOD_LD = 21
    ZDIVMOD_REC = 22


@dataclass(frozen=True)
class Decoded:
    opcode: int
    rd: int = 0
    rs1: int = 0
    rs2: int = 0
    imm: int = 0
    fmt: str = "R"


def _u32(x: int) -> int:
    return int(x) & U32_MASK


def enc_R(op: int, rd: int, rs1: int, rs2: int, imm11: int = 0) -> int:
    return _u32(((op & 0x3F) << 26) | ((rd & 0x1F) << 21) | ((rs1 & 0x1F) << 16) | ((rs2 & 0x1F) << 11) | (imm11 & 0x7FF))


def enc_I(op: int, rd: int, rs1: int, imm16: int) -> int:
    return _u32(((op & 0x3F) << 26) | ((rd & 0x1F) << 21) | ((rs1 & 0x1F) << 16) | (imm16 & 0xFFFF))


def _sign_extend(x: int, bits: int) -> int:
    m = 1 << (bits - 1)
    x &= (1 << bits) - 1
    return (x ^ m) - m


_OP_FMT: Dict[int, str] = {
    Opcode.NOP: "R",
    Opcode.HALT: "R",
    Opcode.ZLI: "I",
    Opcode.ZMOV: "R",
    Opcode.ZFOLD: "R",
    Opcode.ZADD: "R",
    Opcode.ZSUB: "R",
    Opcode.ZMUL: "R",
    Opcode.ZDIVQ: "R",
    Opcode.ZDIVR: "R",
    Opcode.WSETM: "I",
    Opcode.WLI: "I",
    Opcode.WFOLD: "I",
    Opcode.WREM: "I",
    Opcode.WTRUNC: "I",
    Opcode.WGAUGE: "I",
    Opcode.Z2P: "R",
    Opcode.P2Z: "R",
    Opcode.PMUL: "R",
    Opcode.PDIV: "R",
    Opcode.PROJ_CHI: "I",
    Opcode.ZDIVMOD_LD: "R",
    Opcode.ZDIVMOD_REC: "R",
}


def decode(word: int) -> Decoded:
    w = _u32(word)
    op = (w >> 26) & 0x3F
    fmt = _OP_FMT.get(op, "R")
    rd = (w >> 21) & 0x1F
    rs1 = (w >> 16) & 0x1F
    if fmt == "I":
        imm16 = w & 0xFFFF
        imm = _sign_extend(imm16, 16)
        return Decoded(opcode=op, rd=rd, rs1=rs1, imm=imm, fmt="I")
    rs2 = (w >> 11) & 0x1F
    imm11 = w & 0x7FF
    return Decoded(opcode=op, rd=rd, rs1=rs1, rs2=rs2, imm=imm11, fmt="R")


# =========================
# Assembler (typed registers)
# =========================


_REG_RE = re.compile(r"^([ZWP])(\d+)$", re.IGNORECASE)


def _parse_reg(tok: str) -> Tuple[str, int]:
    m = _REG_RE.match(tok.strip())
    if not m:
        raise ValueError(f"Bad register {tok!r}. Use Z0..Z31, W0..W31, P0..P31.")
    kind = m.group(1).upper()
    idx = int(m.group(2))
    if not (0 <= idx <= 31):
        raise ValueError("Register index out of range (0..31)")
    return kind, idx


def _parse_imm(tok: str) -> int:
    s = tok.strip().lower()
    if s.startswith("0x"):
        return int(s, 16)
    if s.startswith("-0x"):
        return -int(s[1:], 16)
    return int(s, 10)


@dataclass(frozen=True)
class AsmInst:
    name: str
    args: Tuple[str, ...]


def parse_asm_lines(lines: Iterable[str]) -> List[AsmInst]:
    out: List[AsmInst] = []
    for raw in lines:
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        line = line.replace(",", " ")
        parts = [p for p in line.split() if p]
        if not parts:
            continue
        out.append(AsmInst(name=parts[0].upper(), args=tuple(parts[1:])))
    return out


def assemble(insts: Sequence[AsmInst]) -> List[int]:
    mc: List[int] = []
    for ins in insts:
        op = ins.name
        a = ins.args

        def need(n: int) -> None:
            if len(a) != n:
                raise ValueError(f"{op}: expected {n} args, got {len(a)}: {a}")

        if op == "NOP":
            mc.append(enc_R(Opcode.NOP, 0, 0, 0, 0))
            continue
        if op in ("HALT", "HLT"):
            mc.append(enc_R(Opcode.HALT, 0, 0, 0, 0))
            continue

        # Z core
        if op == "ZLI":
            need(2)
            k_rd, rd = _parse_reg(a[0])
            if k_rd != "Z":
                raise ValueError("ZLI: rd must be a Z register")
            imm = _parse_imm(a[1])
            mc.append(enc_I(Opcode.ZLI, rd, 0, imm))
            continue
        if op == "ZMOV":
            need(2)
            k_rd, rd = _parse_reg(a[0])
            k_rs, rs = _parse_reg(a[1])
            if k_rd != "Z" or k_rs != "Z":
                raise ValueError("ZMOV: operands must be Z registers")
            mc.append(enc_R(Opcode.ZMOV, rd, rs, 0, 0))
            continue
        if op == "ZFOLD":
            need(2)
            k_rd, rd = _parse_reg(a[0])
            k_rs, rs = _parse_reg(a[1])
            if k_rd != "Z" or k_rs != "Z":
                raise ValueError("ZFOLD: operands must be Z registers")
            mc.append(enc_R(Opcode.ZFOLD, rd, rs, 0, 0))
            continue
        if op in ("ZADD", "ZSUB", "ZMUL", "ZDIVQ", "ZDIVR"):
            need(3)
            k_rd, rd = _parse_reg(a[0])
            k_ra, ra = _parse_reg(a[1])
            k_rb, rb = _parse_reg(a[2])
            if k_rd != "Z" or k_ra != "Z" or k_rb != "Z":
                raise ValueError(f"{op}: operands must be Z registers")
            opc = {"ZADD": Opcode.ZADD, "ZSUB": Opcode.ZSUB, "ZMUL": Opcode.ZMUL, "ZDIVQ": Opcode.ZDIVQ, "ZDIVR": Opcode.ZDIVR}[op]
            mc.append(enc_R(opc, rd, ra, rb, 0))
            continue

        if op in ("ZDIVMOD_LD", "ZDIVMOD_REC"):
            need(4)
            k_rq, rq = _parse_reg(a[0])
            k_rr, rr = _parse_reg(a[1])
            k_ra, ra = _parse_reg(a[2])
            k_rb, rb = _parse_reg(a[3])
            if k_rq != "Z" or k_rr != "Z" or k_ra != "Z" or k_rb != "Z":
                raise ValueError(f"{op}: all operands must be Z registers")
            opc = Opcode.ZDIVMOD_LD if op == "ZDIVMOD_LD" else Opcode.ZDIVMOD_REC
            # Encode rr into imm11 low bits (5-bit index).
            mc.append(enc_R(opc, rq, ra, rb, imm11=int(rr) & 0x1F))
            continue

        # W micro
        if op == "WSETM":
            need(2)
            k_wd, wd = _parse_reg(a[0])
            if k_wd != "W":
                raise ValueError("WSETM: Wd must be a W register")
            mval = _parse_imm(a[1])
            mc.append(enc_I(Opcode.WSETM, wd, 0, mval))
            continue
        if op == "WLI":
            need(2)
            k_wd, wd = _parse_reg(a[0])
            if k_wd != "W":
                raise ValueError("WLI: Wd must be a W register")
            imm = _parse_imm(a[1])
            mc.append(enc_I(Opcode.WLI, wd, 0, imm))
            continue
        if op in ("WFOLD", "WREM", "WTRUNC", "WGAUGE"):
            need(3)
            k_d, d = _parse_reg(a[0])
            k_s, s = _parse_reg(a[1])
            mval = _parse_imm(a[2])
            opc = {"WFOLD": Opcode.WFOLD, "WREM": Opcode.WREM, "WTRUNC": Opcode.WTRUNC, "WGAUGE": Opcode.WGAUGE}[op]
            if op == "WFOLD":
                if k_d != "Z" or k_s != "W":
                    raise ValueError("WFOLD: signature is WFOLD Zd, Ws, m")
            elif op in ("WREM", "WTRUNC"):
                if k_d != "W" or k_s != "W":
                    raise ValueError(f"{op}: signature is {op} Wd, Ws, m")
            else:
                if k_d != "Z" or k_s != "W":
                    raise ValueError("WGAUGE: signature is WGAUGE Zd, Ws, m")
            mc.append(enc_I(opc, d, s, mval))
            continue

        # P optional
        if op == "Z2P":
            need(2)
            k_pd, pd = _parse_reg(a[0])
            k_za, za = _parse_reg(a[1])
            if k_pd != "P" or k_za != "Z":
                raise ValueError("Z2P: signature is Z2P Pd, Za")
            mc.append(enc_R(Opcode.Z2P, pd, za, 0, 0))
            continue
        if op == "P2Z":
            need(2)
            k_zd, zd = _parse_reg(a[0])
            k_pa, pa = _parse_reg(a[1])
            if k_zd != "Z" or k_pa != "P":
                raise ValueError("P2Z: signature is P2Z Zd, Pa")
            mc.append(enc_R(Opcode.P2Z, zd, pa, 0, 0))
            continue
        if op in ("PMUL", "PDIV"):
            need(3)
            k_pd, pd = _parse_reg(a[0])
            k_pa, pa = _parse_reg(a[1])
            k_pb, pb = _parse_reg(a[2])
            if k_pd != "P" or k_pa != "P" or k_pb != "P":
                raise ValueError(f"{op}: operands must be P registers")
            mc.append(enc_R(Opcode.PMUL if op == "PMUL" else Opcode.PDIV, pd, pa, pb, 0))
            continue

        # v2 cost hooks
        if op in ("PROJ_CHI", "PROJCHI"):
            if len(a) == 0:
                mc.append(enc_I(Opcode.PROJ_CHI, 0, 0, 0))
            elif len(a) == 1:
                mc.append(enc_I(Opcode.PROJ_CHI, 0, 0, _parse_imm(a[0])))
            else:
                raise ValueError("PROJ_CHI: expected 0 or 1 args (optional imm)")
            continue

        raise ValueError(f"Unknown instruction {op!r}")
    return mc


# =========================
# CPU state / execution
# =========================


@dataclass
class Window:
    bits: int = 0
    m: int = 0

    def masked_bits(self) -> int:
        if self.m <= 0:
            return 0
        return int(self.bits) & ((1 << int(self.m)) - 1)


@dataclass
class Counters:
    k_Z: int = 0
    k_le: int = 0
    k_chi: int = 0
    D_U: int = 0
    support: int = 0
    n_max_bits: int = 0  # logical size proxy for reporting


def _cap_signed(x: int, capbits: Optional[int]) -> int:
    if capbits is None:
        return int(x)
    b = int(capbits)
    if b <= 0:
        return 0
    mod = 1 << b
    half = 1 << (b - 1)
    y = int(x) % mod
    if y >= half:
        y -= mod
    return int(y)


def _mul_depth_proxy(mode: str, nbits_a: int, nbits_b: int) -> int:
    """Multiplication linearization depth proxy.

    mode:
      - const : O(1)
      - log   : O(log n)
      - serial: O(n)
    """
    n = max(int(nbits_a), int(nbits_b), 1)
    if mode == "const":
        return 1
    if mode == "serial":
        return n
    # default: log
    return max(1, int(math.ceil(math.log2(n))))


# 8-bit reciprocal seed table for normalized mantissas in [1,2).
# Index v in [128..255] (interpreted as v/128) -> approx (1/(v/128)) scaled by 2^16.
_RECIP8_Y_INV_Q16: List[int] = [0 for _ in range(256)]
for _v in range(128, 256):
    _RECIP8_Y_INV_Q16[_v] = int(((1 << 23) + (_v // 2)) // _v)  # round(2^23 / v)


def _divmod_ld_unsigned(a: int, b: int, qbits: int, ctr: Counters) -> Tuple[int, int]:
    """Binary long division microcode (unsigned).

    - Counts one P_≤ call per quotient bit decision (k_le).
    - Counts one U-step per quotient bit decision (D_U) as a simple depth proxy.
    """
    if a < 0 or b <= 0:
        raise ValueError("_divmod_ld_unsigned expects a>=0, b>0")
    q = 0
    r = int(a)
    for i in range(int(qbits), -1, -1):
        ctr.k_le += 1
        ctr.D_U += 1
        bi = int(b) << int(i)
        if r >= bi:
            r -= bi
            q |= 1 << int(i)
    return int(q), int(r)


def _divmod_ld_signed(a: int, ab: int, b: int, bb: int, ctr: Counters) -> Tuple[int, int]:
    """Binary long division microcode (signed, Python-style floor divmod semantics)."""
    if b == 0:
        raise ZeroDivisionError("DIV by zero")
    A = abs(int(a))
    B = abs(int(b))
    qbits = max(0, int(ab) - int(bb))

    q0, r0 = _divmod_ld_unsigned(int(A), int(B), qbits=qbits, ctr=ctr)

    if b > 0:
        if a >= 0:
            return int(q0), int(r0)
        if r0 == 0:
            return -int(q0), 0
        # a = (-q0-1)*B + (B-r0)
        return -int(q0) - 1, int(B) - int(r0)

    # b < 0: remainder must be <= 0
    if a <= 0:
        return int(q0), -int(r0)
    if r0 == 0:
        return -int(q0), 0
    return -int(q0) - 1, -int(B) + int(r0)


def _recip_seed_Qp(b: int, bb: int, p: int) -> int:
    """Seed X0 ≈ 2^p / b using a constant-time 8-bit mantissa table."""
    if b <= 0:
        raise ValueError("_recip_seed_Qp expects b>0")
    m = max(int(bb), 1)
    if m >= 8:
        top8 = int(b) >> int(m - 8)
    else:
        top8 = int(b) << int(8 - m)
    top8 &= 0xFF
    if top8 < 128:
        top8 = 128
    inv_y_Q16 = int(_RECIP8_Y_INV_Q16[int(top8)])
    # inv_y_Q16 ~ (1/y)*2^16, with y=b/2^{m-1}; thus 2^p/b = 2^{p-(m-1)}*(1/y).
    shift = int(p) - (int(m) - 1) - 16
    if shift >= 0:
        return int(inv_y_Q16) << int(shift)
    return int(inv_y_Q16) >> int(-shift)


def _divmod_rec_unsigned(
    a: int,
    ab: int,
    b: int,
    bb: int,
    ctr: Counters,
    *,
    mulmode: str,
    extra_precision: int = 32,
) -> Tuple[int, int]:
    """Fixed-point reciprocal Newton microcode (unsigned).

    Goal: exact (q,r) with k_le ~ O(1) via constant-time interval correction.
    Growth is moved into D_U via multiplication-depth proxies.
    """
    if a < 0 or b <= 0:
        raise ValueError("_divmod_rec_unsigned expects a>=0, b>0")

    m = max(int(bb), 1)
    # Use dividend-scale precision so q-estimate error stays O(1) after multiplying by a.
    p = max(int(ab), int(bb), 1) + int(extra_precision)

    # iterations: conservative seed (~8 correct bits from 8-bit mantissa table), then double each step
    need_bits = max(1, int(p))
    ratio = max(1.0, float(need_bits) / 8.0)
    iters = max(1, int(math.ceil(math.log2(ratio))) + 1)

    X = _recip_seed_Qp(int(b), bb=int(bb), p=p)
    if X <= 0:
        X = 1

    for _ in range(int(iters)):
        # b*X
        ctr.D_U += _mul_depth_proxy(mulmode, m, max(1, int(X).bit_length()))
        bX = int(b) * int(X)
        # X*(2^{p+1} - bX) >> p
        M = (1 << (int(p) + 1)) - int(bX)
        ctr.D_U += _mul_depth_proxy(mulmode, max(1, int(X).bit_length()), max(1, int(M).bit_length()))
        X = (int(X) * int(M)) >> int(p)
        if X <= 0:
            X = 1

    # q ≈ floor(a * (2^p/b) / 2^p)
    ctr.D_U += _mul_depth_proxy(mulmode, int(ab), max(1, int(X).bit_length()))
    q = (int(a) * int(X)) >> int(p)
    r = int(a) - int(q) * int(b)

    # Constant-time interval correction (P_≤ calls).
    for _ in range(16):
        ctr.k_le += 1
        if r < 0:
            r += int(b)
            q -= 1
            continue
        ctr.k_le += 1
        if r >= int(b):
            r -= int(b)
            q += 1
            continue
        break

    if not (0 <= int(r) < int(b)):
        # Safety net: fall back to exact long-division microcode (still gate-auditable).
        qbits = max(0, int(ab) - int(bb))
        q, r = _divmod_ld_unsigned(int(a), int(b), qbits=qbits, ctr=ctr)
    return int(q), int(r)


def _divmod_rec_signed(a: int, ab: int, b: int, bb: int, ctr: Counters, *, mulmode: str) -> Tuple[int, int]:
    """Fixed-point reciprocal Newton microcode (signed, Python-style floor divmod semantics)."""
    if b == 0:
        raise ZeroDivisionError("DIV by zero")
    A = abs(int(a))
    B = abs(int(b))
    q0, r0 = _divmod_rec_unsigned(int(A), int(ab), int(B), int(bb), ctr, mulmode=mulmode)

    if b > 0:
        if a >= 0:
            return int(q0), int(r0)
        if r0 == 0:
            return -int(q0), 0
        return -int(q0) - 1, int(B) - int(r0)

    # b < 0: remainder must be <= 0
    if a <= 0:
        return int(q0), -int(r0)
    if r0 == 0:
        return -int(q0), 0
    return -int(q0) - 1, -int(B) + int(r0)


@dataclass
class CPU:
    Z: List[int]
    Z_bits: List[int]  # logical bit-size proxy (independent of cap)
    W: List[Window]
    P: List[PrimeVector]
    capbits: Optional[int] = None
    mulmode: str = "log"
    pc: int = 0
    halted: bool = False
    ctr: Counters = dataclasses.field(default_factory=Counters)

    @staticmethod
    def fresh(*, capbits: Optional[int] = None, mulmode: str = "log") -> "CPU":
        return CPU(
            Z=[0 for _ in range(32)],
            Z_bits=[0 for _ in range(32)],
            W=[Window() for _ in range(32)],
            P=[PrimeVector(sign=0, exps={}) for _ in range(32)],
            capbits=capbits,
            mulmode=str(mulmode),
        )

    def _touch_nbits(self, *nbits: int) -> None:
        for b in nbits:
            if int(b) > self.ctr.n_max_bits:
                self.ctr.n_max_bits = int(b)

    def _write_Z(self, rd: int, value: int, nbits: int, *, do_fold: bool) -> None:
        if do_fold:
            self.ctr.k_Z += 1
            value = fold_infty_int(value)
        self.Z[int(rd)] = _cap_signed(int(value), self.capbits)
        self.Z_bits[int(rd)] = max(0, int(nbits))
        self._touch_nbits(int(nbits))

    def _read_Z(self, r: int) -> Tuple[int, int]:
        return int(self.Z[int(r)]), int(self.Z_bits[int(r)])

    def _write_W(self, wd: int, bits: int, m: int) -> None:
        self.W[int(wd)].m = int(m)
        if m <= 0:
            self.W[int(wd)].bits = 0
        else:
            self.W[int(wd)].bits = int(bits) & ((1 << int(m)) - 1)

    def step(self, word: int) -> None:
        if self.halted:
            return
        ins = decode(word)
        op = ins.opcode

        if op == Opcode.NOP:
            self.pc += 1
            return
        if op == Opcode.HALT:
            self.halted = True
            return

        # ---- Z ----
        if op == Opcode.ZLI:
            imm = int(ins.imm)
            nbits = abs(int(imm)).bit_length()
            self._write_Z(ins.rd, imm, nbits, do_fold=True)
            self.pc += 1
            return
        if op == Opcode.ZMOV:
            v, b = self._read_Z(ins.rs1)
            self._write_Z(ins.rd, v, b, do_fold=False)
            self.pc += 1
            return
        if op == Opcode.ZFOLD:
            v, b = self._read_Z(ins.rs1)
            self._write_Z(ins.rd, v, b, do_fold=True)
            self.pc += 1
            return

        if op in (Opcode.ZADD, Opcode.ZSUB, Opcode.ZMUL, Opcode.ZDIVQ, Opcode.ZDIVR):
            a, ab = self._read_Z(ins.rs1)
            b, bb = self._read_Z(ins.rs2)
            if op == Opcode.ZADD:
                self._write_Z(ins.rd, a + b, max(ab, bb) + 1, do_fold=True)
            elif op == Opcode.ZSUB:
                self._write_Z(ins.rd, a - b, max(ab, bb) + 1, do_fold=True)
            elif op == Opcode.ZMUL:
                # D_U proxy: multiplication linearization depth model.
                self.ctr.D_U += _mul_depth_proxy(str(self.mulmode), int(ab), int(bb))
                self._write_Z(ins.rd, a * b, int(ab) + int(bb), do_fold=True)
            elif op == Opcode.ZDIVQ:
                self.ctr.k_le += 1
                if b == 0:
                    raise ZeroDivisionError("ZDIVQ by zero")
                q = a // b
                qb = max(1, int(ab) - int(bb) + 1)
                self._write_Z(ins.rd, q, qb, do_fold=True)
            elif op == Opcode.ZDIVR:
                self.ctr.k_le += 1
                if b == 0:
                    raise ZeroDivisionError("ZDIVR by zero")
                r = a % b
                rb = max(0, min(int(ab), int(bb)))
                self._write_Z(ins.rd, r, rb, do_fold=True)
            self.pc += 1
            return

        if op in (Opcode.ZDIVMOD_LD, Opcode.ZDIVMOD_REC):
            a, ab = self._read_Z(ins.rs1)
            b, bb = self._read_Z(ins.rs2)
            if b == 0:
                raise ZeroDivisionError("ZDIVMOD by zero")
            if op == Opcode.ZDIVMOD_LD:
                q, r = _divmod_ld_signed(a, ab, b, bb, self.ctr)
            else:
                q, r = _divmod_rec_signed(a, ab, b, bb, self.ctr, mulmode=str(self.mulmode))
            qb = max(1, int(ab) - int(bb) + 1)
            rb = max(0, min(int(ab), int(bb)))

            rr = int(ins.imm) & 0x1F  # remainder register index packed in imm11
            self._write_Z(ins.rd, q, qb, do_fold=True)
            self._write_Z(rr, r, rb, do_fold=True)
            self.pc += 1
            return

        # ---- W ----
        if op == Opcode.WSETM:
            m = int(ins.imm)
            if m < 0:
                raise ValueError("WSETM m must be >= 0")
            cur = self.W[int(ins.rd)]
            cur.m = m
            cur.bits = cur.masked_bits()
            self.pc += 1
            return
        if op == Opcode.WLI:
            imm_u16 = int(ins.imm) & 0xFFFF
            cur = self.W[int(ins.rd)]
            self._write_W(ins.rd, imm_u16, m=int(cur.m))
            self.pc += 1
            return
        if op == Opcode.WFOLD:
            m = int(ins.imm)
            if m < 0:
                raise ValueError("WFOLD m must be >= 0")
            omega = int(self.W[int(ins.rs1)].bits) & ((1 << m) - 1) if m > 0 else 0
            val = fold_m_int(omega, m)
            self._write_Z(ins.rd, val, max(0, int(val).bit_length()), do_fold=True)
            self.pc += 1
            return
        if op in (Opcode.WREM, Opcode.WTRUNC, Opcode.WGAUGE):
            m = int(ins.imm)
            if m < 0:
                raise ValueError("W* m must be >= 0")
            omega = int(self.W[int(ins.rs1)].bits) & ((1 << (m + 1)) - 1) if (m + 1) > 0 else 0
            if op == Opcode.WTRUNC:
                self._write_W(ins.rd, trunc_mplus1_to_m_bits(omega, m), m=m)
            elif op == Opcode.WREM:
                g = gauge_Gm(omega, m)
                self.ctr.support += int(g)
                self._write_W(ins.rd, rem_mplus1_to_m_bits(omega, m), m=m)
            else:
                g = gauge_Gm(omega, m)
                self.ctr.support += int(g)
                self._write_Z(ins.rd, int(g), max(0, int(g).bit_length()), do_fold=False)
            self.pc += 1
            return

        # ---- P ----
        if op == Opcode.Z2P:
            a, _ab = self._read_Z(ins.rs1)
            self.P[int(ins.rd)] = primevec_from_int(a)
            self.pc += 1
            return
        if op == Opcode.P2Z:
            pv = self.P[int(ins.rs1)]
            val = int_from_primevec(pv)
            self._write_Z(ins.rd, val, abs(int(val)).bit_length(), do_fold=True)
            self.pc += 1
            return
        if op == Opcode.PMUL:
            self.P[int(ins.rd)] = primevec_mul(self.P[int(ins.rs1)], self.P[int(ins.rs2)])
            self.pc += 1
            return
        if op == Opcode.PDIV:
            self.ctr.k_le += 1
            self.P[int(ins.rd)] = primevec_div_checked(self.P[int(ins.rs1)], self.P[int(ins.rs2)])
            self.pc += 1
            return

        # ---- P_χ projection hook ----
        if op == Opcode.PROJ_CHI:
            self.ctr.k_chi += 1
            self.pc += 1
            return

        raise ValueError(f"Unknown opcode {op} at pc={self.pc}")


def run_program(cpu: CPU, prog: Sequence[int], *, step_cap: int = 2_000_000) -> CPU:
    steps = 0
    while not cpu.halted:
        if not (0 <= cpu.pc < len(prog)):
            raise IndexError(f"PC out of range: pc={cpu.pc} len={len(prog)}")
        cpu.step(prog[cpu.pc])
        steps += 1
        if steps > step_cap:
            raise RuntimeError("step cap exceeded")
    return cpu


# =========================
# CLI experiments
# =========================


def _cost_total(
    ctr: Counters,
    *,
    deltaZ: float,
    Tle: float,
    tauMix: float,
    wSup: float,
) -> Tuple[float, Dict[str, float]]:
    cZ = float(ctr.k_Z) * float(deltaZ)
    cLe = float(ctr.k_le) * float(Tle)
    cChi = float(ctr.k_chi) * float(tauMix)
    cDU = float(ctr.D_U)
    cSup = float(ctr.support) * float(wSup)
    T = cZ + cLe + cChi + cDU + cSup
    return T, {"kZ*deltaZ": cZ, "kLe*Tle": cLe, "kChi*tauMix": cChi, "D_U": cDU, "wSup*support": cSup}


def cmd_demo(*, capbits: Optional[int], mulmode: str, deltaZ: float, Tle: float, tauMix: float, wSup: float) -> None:
    asm = [
        "ZLI Z1, 123",
        "ZLI Z2, 77",
        "ZADD Z3, Z1, Z2",
        "ZMUL Z4, Z1, Z2",
        "ZDIVMOD_LD Z5, Z6, Z1, Z2",
        "ZDIVMOD_REC Z7, Z8, Z1, Z2",
        "HALT",
    ]
    prog = assemble(parse_asm_lines(asm))
    cpu = CPU.fresh(capbits=capbits, mulmode=str(mulmode))
    run_program(cpu, prog)
    print(f"[demo] Z1=123  Z2=77  mulmode={mulmode}", flush=True)
    print(f"[demo] Z3=Z1+Z2 => {cpu.Z[3]} (expect 200)", flush=True)
    print(f"[demo] Z4=Z1*Z2 => {cpu.Z[4]} (expect 9471)", flush=True)
    print(f"[demo] LD : Z5=Z1//Z2 => {cpu.Z[5]} (expect 1)", flush=True)
    print(f"[demo] LD : Z6=Z1%Z2  => {cpu.Z[6]} (expect 46)", flush=True)
    print(f"[demo] REC: Z7=Z1//Z2 => {cpu.Z[7]} (expect 1)", flush=True)
    print(f"[demo] REC: Z8=Z1%Z2  => {cpu.Z[8]} (expect 46)", flush=True)
    T, parts = _cost_total(cpu.ctr, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    print(
        f"[demo] counters: k_Z={cpu.ctr.k_Z} k_le={cpu.ctr.k_le} k_chi={cpu.ctr.k_chi} D_U={cpu.ctr.D_U} support={cpu.ctr.support} n_bits~{cpu.ctr.n_max_bits}",
        flush=True,
    )
    print(f"[demo] cost: T~{T:.6g} parts={{{', '.join(f'{k}={v:.6g}' for k,v in parts.items())}}}", flush=True)


def cmd_gauge(*, m: int, trials: int, seed: int) -> None:
    if m < 0:
        raise ValueError("--m must be >= 0")
    if trials <= 0:
        raise ValueError("--trials must be positive")
    rng = random.Random(int(seed))
    tot = 0
    mx = 0
    for _ in range(int(trials)):
        omega = rng.getrandbits(m + 1) if (m + 1) > 0 else 0
        g = gauge_Gm(omega, m)
        tot += g
        mx = max(mx, g)
    avg = tot / float(trials)
    ratio = (avg / float(m)) if m > 0 else 0.0
    print(
        f"[gauge] m={m} trials={trials} E[G_m]~{avg:.6g}  E[G_m]/m~{ratio:.6g}  max_seen={mx}  G_max=m={m}",
        flush=True,
    )


def cmd_chi_bench(
    *,
    n_calls: int,
    deltaZ: float,
    Tle: float,
    tauMix: float,
    wSup: float,
) -> None:
    if n_calls < 0:
        raise ValueError("--chi-bench must be >= 0")
    asm: List[str] = []
    for _ in range(int(n_calls)):
        asm.append("PROJ_CHI")
    asm.append("HALT")
    prog = assemble(parse_asm_lines(asm))
    cpu = CPU.fresh(capbits=None)
    run_program(cpu, prog)
    T, parts = _cost_total(cpu.ctr, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    print(f"[chi-bench] n_calls={n_calls}", flush=True)
    print(
        f"[chi-bench] counters: k_Z={cpu.ctr.k_Z} k_le={cpu.ctr.k_le} k_chi={cpu.ctr.k_chi} D_U={cpu.ctr.D_U} support={cpu.ctr.support}",
        flush=True,
    )
    print(f"[chi-bench] cost: T~{T:.6g} parts={parts}", flush=True)


def cmd_support_bench(
    *,
    iters: int,
    m_support: int,
    seed: int,
    capbits: Optional[int],
    mulmode: str,
    deltaZ: float,
    Tle: float,
    tauMix: float,
    wSup: float,
) -> None:
    if iters <= 0:
        raise ValueError("--support-bench must be positive")
    if m_support < 0:
        raise ValueError("--m-support must be >= 0")
    rng = random.Random(int(seed))

    # Keep Z1,Z2 constant and overwrite Z3 each iteration to keep D_U stable.
    asm: List[str] = [
        "ZLI Z1, 123",
        "ZLI Z2, 77",
        f"WSETM W0, {m_support+1}",
        "WLI W0, 0",
    ]
    for _ in range(int(iters)):
        asm.append("ZMUL Z3, Z1, Z2")
        payload = rng.randrange(0, 1 << 16)
        asm.append(f"WLI W0, {payload}")
        asm.append(f"WGAUGE Z0, W0, {m_support}")
    asm.append("HALT")

    prog = assemble(parse_asm_lines(asm))
    cpu = CPU.fresh(capbits=capbits, mulmode=str(mulmode))
    run_program(cpu, prog)
    T, parts = _cost_total(cpu.ctr, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    print(f"[support-bench] iters={iters} m={m_support} seed={seed} capbits={capbits} mulmode={mulmode}", flush=True)
    print(
        f"[support-bench] counters: k_Z={cpu.ctr.k_Z} k_le={cpu.ctr.k_le} k_chi={cpu.ctr.k_chi} D_U={cpu.ctr.D_U} support={cpu.ctr.support}",
        flush=True,
    )
    print(f"[support-bench] cost: T~{T:.6g} parts={parts}", flush=True)


def _rand_reg(rng: random.Random) -> int:
    return int(rng.randrange(0, 32))


def _rand_reg_excluding(rng: random.Random, banned: Sequence[int]) -> int:
    banned_set = set(int(x) for x in banned)
    while True:
        r = int(rng.randrange(0, 32))
        if r not in banned_set:
            return r


def _rand_reg_range(rng: random.Random, lo: int, hi_excl: int) -> int:
    lo = int(lo)
    hi_excl = int(hi_excl)
    if not (0 <= lo < hi_excl <= 32):
        raise ValueError("bad register range")
    return int(rng.randrange(lo, hi_excl))


def _workload_program_asm(
    *,
    length: int,
    seed: int,
    divmode: str,
    capbits: Optional[int],
    with_support: bool,
    m_support: int,
) -> List[str]:
    rng = random.Random(int(seed))
    lines: List[str] = []

    # Seed a few Z regs with small nonzero values and keep them *constant*:
    # We never write to Z1..Z8 in the workload generator, and use them as safe divisors.
    const_regs = list(range(1, 9))
    for r in const_regs:
        imm = rng.randrange(1, 500)
        lines.append(f"ZLI Z{r}, {imm}")

    if with_support:
        # Prepare a single window register used for repeated WGAUGE calls.
        lines.append(f"WSETM W0, {m_support+1}")
        lines.append("WLI W0, 0")  # will be overwritten by random WLI payloads

    # Operation mix (tunable but deterministic given seed).
    p_div = 0.22
    p_mul = 0.20
    p_add = 0.25
    p_chi = 0.02
    p_support = 0.10 if with_support else 0.0

    for _ in range(int(length)):
        r = rng.random()
        if r < p_chi:
            lines.append("PROJ_CHI")
            continue
        if with_support and (r < p_chi + p_support):
            # Randomize the raw window low-16 payload and gauge at fixed m_support.
            payload = rng.randrange(0, 1 << 16)
            lines.append(f"WLI W0, {payload}")
            lines.append(f"WGAUGE Z0, W0, {m_support}")
            continue
        if r < p_chi + p_support + p_div:
            rq = _rand_reg_range(rng, 9, 32)
            rr = _rand_reg_range(rng, 9, 32)
            ra = _rand_reg(rng)
            # Divisor: only use constant nonzero regs to avoid division-by-zero faults.
            rb = int(rng.choice(const_regs))
            if divmode == "ld":
                op = "ZDIVMOD_LD"
            elif divmode == "rec":
                op = "ZDIVMOD_REC"
            else:
                op = "ZDIVMOD_REC" if (rng.random() < 0.5) else "ZDIVMOD_LD"
            lines.append(f"{op} Z{rq}, Z{rr}, Z{ra}, Z{rb}")
            continue
        if r < p_chi + p_support + p_div + p_mul:
            rd = _rand_reg_range(rng, 9, 32)
            ra = _rand_reg(rng)
            rb = _rand_reg(rng)
            lines.append(f"ZMUL Z{rd}, Z{ra}, Z{rb}")
            continue
        if r < p_chi + p_support + p_div + p_mul + p_add:
            rd = _rand_reg_range(rng, 9, 32)
            ra = _rand_reg(rng)
            rb = _rand_reg(rng)
            lines.append(f"ZADD Z{rd}, Z{ra}, Z{rb}")
            continue
        # default: subtraction (keeps values moving)
        rd = _rand_reg_range(rng, 9, 32)
        ra = _rand_reg(rng)
        rb = _rand_reg(rng)
        lines.append(f"ZSUB Z{rd}, Z{ra}, Z{rb}")

    lines.append("HALT")
    return lines


def cmd_workload(
    *,
    length: int,
    seed: int,
    divmode: str,
    capbits: Optional[int],
    with_support: bool,
    m_support: int,
    mulmode: str,
    deltaZ: float,
    Tle: float,
    tauMix: float,
    wSup: float,
) -> None:
    asm = _workload_program_asm(
        length=length,
        seed=seed,
        divmode=divmode,
        capbits=capbits,
        with_support=with_support,
        m_support=m_support,
    )
    prog = assemble(parse_asm_lines(asm))
    cpu = CPU.fresh(capbits=capbits, mulmode=str(mulmode))
    run_program(cpu, prog)
    T, parts = _cost_total(cpu.ctr, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    print(
        f"[workload] len={length} seed={seed} divmode={divmode} capbits={capbits} mulmode={mulmode} support_mode={with_support}",
        flush=True,
    )
    print(
        f"[workload] counters: k_Z={cpu.ctr.k_Z} k_le={cpu.ctr.k_le} k_chi={cpu.ctr.k_chi} D_U={cpu.ctr.D_U} support={cpu.ctr.support} n_bits~{cpu.ctr.n_max_bits}",
        flush=True,
    )
    print(f"[workload] cost: T~{T:.6g}", flush=True)
    print(f"[workload] parts: {parts}", flush=True)


def _rand_int_exact_bits(rng: random.Random, bits: int) -> int:
    bits = int(bits)
    if bits <= 0:
        return 0
    x = int(rng.getrandbits(bits))
    x |= 1 << (bits - 1)
    return int(x)


def cmd_bench_div(
    *,
    bits_a: int,
    bits_b: int,
    iters: int,
    seed: int,
    mulmode: str,
    deltaZ: float,
    Tle: float,
    tauMix: float,
    wSup: float,
) -> None:
    bits_a = int(bits_a)
    bits_b = int(bits_b)
    iters = int(iters)
    if bits_a <= 0 or bits_b <= 0:
        raise ValueError("--bits-a/--bits-b must be positive")
    if iters <= 0:
        raise ValueError("--iters must be positive")
    rng = random.Random(int(seed))

    tot_ld = Counters()
    tot_rec = Counters()

    w_ld = enc_R(Opcode.ZDIVMOD_LD, 5, 1, 2, imm11=6)
    w_rec = enc_R(Opcode.ZDIVMOD_REC, 5, 1, 2, imm11=6)

    for _ in range(int(iters)):
        a = _rand_int_exact_bits(rng, bits_a)
        b = _rand_int_exact_bits(rng, bits_b)
        if b == 0:
            b = 1

        # LD
        cpu = CPU.fresh(capbits=None, mulmode=str(mulmode))
        cpu.Z[1], cpu.Z_bits[1] = int(a), int(bits_a)
        cpu.Z[2], cpu.Z_bits[2] = int(b), int(bits_b)
        cpu._touch_nbits(int(bits_a), int(bits_b))
        cpu.step(w_ld)
        q, r = int(cpu.Z[5]), int(cpu.Z[6])
        if not (0 <= r < b and a == q * b + r):
            raise AssertionError("LD divmod invariant failed")
        tot_ld.k_Z += int(cpu.ctr.k_Z)
        tot_ld.k_le += int(cpu.ctr.k_le)
        tot_ld.k_chi += int(cpu.ctr.k_chi)
        tot_ld.D_U += int(cpu.ctr.D_U)
        tot_ld.support += int(cpu.ctr.support)
        tot_ld.n_max_bits = max(int(tot_ld.n_max_bits), int(cpu.ctr.n_max_bits))

        # REC
        cpu = CPU.fresh(capbits=None, mulmode=str(mulmode))
        cpu.Z[1], cpu.Z_bits[1] = int(a), int(bits_a)
        cpu.Z[2], cpu.Z_bits[2] = int(b), int(bits_b)
        cpu._touch_nbits(int(bits_a), int(bits_b))
        cpu.step(w_rec)
        q, r = int(cpu.Z[5]), int(cpu.Z[6])
        if not (0 <= r < b and a == q * b + r):
            raise AssertionError("REC divmod invariant failed")
        tot_rec.k_Z += int(cpu.ctr.k_Z)
        tot_rec.k_le += int(cpu.ctr.k_le)
        tot_rec.k_chi += int(cpu.ctr.k_chi)
        tot_rec.D_U += int(cpu.ctr.D_U)
        tot_rec.support += int(cpu.ctr.support)
        tot_rec.n_max_bits = max(int(tot_rec.n_max_bits), int(cpu.ctr.n_max_bits))

    T_ld, parts_ld = _cost_total(tot_ld, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    T_rec, parts_rec = _cost_total(tot_rec, deltaZ=deltaZ, Tle=Tle, tauMix=tauMix, wSup=wSup)
    parts_ld_avg = {k: float(v) / float(iters) for k, v in parts_ld.items()}
    parts_rec_avg = {k: float(v) / float(iters) for k, v in parts_rec.items()}

    print(f"[bench-div] bits-a={bits_a} bits-b={bits_b} iters={iters} seed={seed} mulmode={mulmode}", flush=True)
    print(
        f"[bench-div][LD ] avg counters: k_Z={tot_ld.k_Z/iters:.3g} k_le={tot_ld.k_le/iters:.3g} k_chi={tot_ld.k_chi/iters:.3g} D_U={tot_ld.D_U/iters:.3g} support={tot_ld.support/iters:.3g}",
        flush=True,
    )
    print(f"[bench-div][LD ] avg cost: T~{(T_ld/iters):.6g} parts={parts_ld_avg}", flush=True)
    print(
        f"[bench-div][REC] avg counters: k_Z={tot_rec.k_Z/iters:.3g} k_le={tot_rec.k_le/iters:.3g} k_chi={tot_rec.k_chi/iters:.3g} D_U={tot_rec.D_U/iters:.3g} support={tot_rec.support/iters:.3g}",
        flush=True,
    )
    print(f"[bench-div][REC] avg cost: T~{(T_rec/iters):.6g} parts={parts_rec_avg}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="POM ISA simulator (projection-gate counters + experiment harness).")
    ap.add_argument("--demo", action="store_true", help="Run a small arithmetic demo.")
    ap.add_argument("--gauge", action="store_true", help="Monte Carlo audit for G_m/m.")
    ap.add_argument("--workload", action="store_true", help="Run a random workload and print cost decomposition.")
    ap.add_argument("--bench-div", action="store_true", help="Benchmark LD vs REC DIVMOD microcode on random inputs.")
    ap.add_argument("--chi-bench", type=int, default=0, help="Call PROJ_CHI N times and print cost decomposition.")
    ap.add_argument(
        "--support-bench",
        type=int,
        default=0,
        help="Run N iterations of (ZMUL + WGAUGE) to study support vs other terms.",
    )
    ap.add_argument("--len", type=int, default=6000, help="Workload length (instructions).")
    ap.add_argument("--seed", type=int, default=7, help="RNG seed.")
    ap.add_argument("--bits-a", type=int, default=1024, help="Dividend bit-length for --bench-div.")
    ap.add_argument("--bits-b", type=int, default=256, help="Divisor bit-length for --bench-div.")
    ap.add_argument("--iters", type=int, default=120, help="Iterations for --bench-div.")
    ap.add_argument("--divmode", choices=["mixed", "ld", "rec"], default="mixed", help="DIVMOD route selection mode.")
    ap.add_argument("--capbits", type=int, default=0, help="Cap stored |Z| to signed capbits (0 disables).")
    ap.add_argument("--mulmode", choices=["const", "log", "serial"], default="log", help="Multiplication depth model.")
    ap.add_argument("--with-support", action="store_true", help="Include WGAUGE-based support accumulation in workload.")
    ap.add_argument("--m-support", type=int, default=15, help="m used by WGAUGE in support mode.")
    ap.add_argument("--m", type=int, default=10, help="m for --gauge.")
    ap.add_argument("--trials", type=int, default=20000, help="Trials for --gauge.")
    ap.add_argument("--deltaZ", type=float, default=3.0, help="δ_Z scale in cost model.")
    ap.add_argument("--Tle", type=float, default=10.0, help="T_≤ scale in cost model.")
    ap.add_argument("--tauMix", type=float, default=20.0, help="τ_mix scale in cost model (per PROJ_CHI).")
    ap.add_argument("--wSup", type=float, default=1.0, help="Weight for support term (per touched bit).")
    args = ap.parse_args()

    capbits = int(args.capbits)
    cap = None if capbits <= 0 else capbits
    mulmode = str(args.mulmode)

    if int(args.chi_bench) > 0:
        cmd_chi_bench(
            n_calls=int(args.chi_bench),
            deltaZ=float(args.deltaZ),
            Tle=float(args.Tle),
            tauMix=float(args.tauMix),
            wSup=float(args.wSup),
        )
        return

    if int(args.support_bench) > 0:
        cmd_support_bench(
            iters=int(args.support_bench),
            m_support=int(args.m_support),
            seed=int(args.seed),
            capbits=cap,
            mulmode=mulmode,
            deltaZ=float(args.deltaZ),
            Tle=float(args.Tle),
            tauMix=float(args.tauMix),
            wSup=float(args.wSup),
        )
        return

    if args.demo:
        cmd_demo(
            capbits=cap,
            mulmode=mulmode,
            deltaZ=float(args.deltaZ),
            Tle=float(args.Tle),
            tauMix=float(args.tauMix),
            wSup=float(args.wSup),
        )
        return
    if args.gauge:
        cmd_gauge(m=int(args.m), trials=int(args.trials), seed=int(args.seed))
        return
    if args.bench_div:
        cmd_bench_div(
            bits_a=int(args.bits_a),
            bits_b=int(args.bits_b),
            iters=int(args.iters),
            seed=int(args.seed),
            mulmode=mulmode,
            deltaZ=float(args.deltaZ),
            Tle=float(args.Tle),
            tauMix=float(args.tauMix),
            wSup=float(args.wSup),
        )
        return
    if args.workload:
        cmd_workload(
            length=int(args.len),
            seed=int(args.seed),
            divmode=str(args.divmode),
            capbits=cap,
            with_support=bool(args.with_support),
            m_support=int(args.m_support),
            mulmode=mulmode,
            deltaZ=float(args.deltaZ),
            Tle=float(args.Tle),
            tauMix=float(args.tauMix),
            wSup=float(args.wSup),
        )
        return

    ap.print_help(sys.stderr)
    raise SystemExit(2)


if __name__ == "__main__":
    main()

