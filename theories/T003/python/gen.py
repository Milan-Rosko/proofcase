#!/usr/bin/env python3

"""
Single-file constructor for the universal cubic artifact (JSON monomial list).

This version uses a two-stage pipeline:
Stage 1 (TeX-level): build polynomial constraints P(...)=0, including selector
activation sel*Q where Q is quadratic checker logic.

Stage 2 (channelization): decompose each polynomial P into P = A - B and emit
equation channels A = B with subtraction-free nonnegative sides.
Aggregation consumes equation channels directly.

The semantic compiler emits a bounded proof-constraint system C_{n,t} for
Hilbert-style checking (K/S/EFQ + MP + target), then aggregates it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

# Expression core

@dataclass(frozen=True)
class BaseExpr:
    op: str
    args: Tuple["BaseExpr", ...]
    value: int | str | None
    deg: int

    def __iter__(self):
        return iter(self.args)

    def __repr__(self) -> str:
        if self.op == "const":
            return f"Const({self.value})"
        if self.op == "var":
            return f"Var({self.value})"
        joined = ", ".join(repr(a) for a in self.args)
        return f"{self.op.capitalize()}({joined})"


def Const(c: int) -> BaseExpr:
    return BaseExpr("const", (), int(c), 0)


def Var(name: str) -> BaseExpr:
    return BaseExpr("var", (), str(name), 1)


def Add(a: BaseExpr, b: BaseExpr) -> BaseExpr:
    return BaseExpr("add", (a, b), None, max(a.deg, b.deg))


def Sub(a: BaseExpr, b: BaseExpr) -> BaseExpr:
    return BaseExpr("sub", (a, b), None, max(a.deg, b.deg))


def Mul(a: BaseExpr, b: BaseExpr) -> BaseExpr:
    return BaseExpr("mul", (a, b), None, a.deg + b.deg)


def add_many(xs: Sequence[BaseExpr]) -> BaseExpr:
    if not xs:
        return Const(0)
    acc = xs[0]
    for x in xs[1:]:
        acc = Add(acc, x)
    return acc


def linear_combination(terms: Iterable[Tuple[int, BaseExpr]]) -> BaseExpr:
    """Build Σ coeff_i * term_i."""
    acc: BaseExpr | None = None
    for coeff, term in terms:
        term_expr = term if coeff == 1 else Mul(Const(coeff), term)
        acc = term_expr if acc is None else Add(acc, term_expr)
    return Const(0) if acc is None else acc


def assert_degree_le(expr: BaseExpr, bound: int = 3) -> None:
    if expr.deg > bound:
        raise ValueError(f"degree {expr.deg} exceeds bound {bound}: {expr!r}")


def _assert_sub_free_nonneg(expr: BaseExpr) -> None:
    stack = [expr]
    while stack:
        e = stack.pop()
        if e.op == "sub":
            raise ValueError(f"subtraction is not allowed in equation channels: {e!r}")
        if e.op == "const" and int(e.value) < 0:  # type: ignore[arg-type]
            raise ValueError(f"negative constant is not allowed in equation channels: {e!r}")
        stack.extend(e.args)


def _var_name(expr: BaseExpr) -> str | None:
    if expr.op == "var":
        return str(expr.value)
    return None


@dataclass(frozen=True)
class Equation:
    lhs: BaseExpr
    rhs: BaseExpr


@dataclass(frozen=True)
class PolyConstraint:
    poly: BaseExpr
    tag: str
    selector: str | None = None
    source_degree: int | None = None



def Eq(lhs: BaseExpr, rhs: BaseExpr) -> Equation:
    _assert_sub_free_nonneg(lhs)
    _assert_sub_free_nonneg(rhs)
    assert_degree_le(lhs, 3)
    assert_degree_le(rhs, 3)
    return Equation(lhs=lhs, rhs=rhs)


def EqZ(lhs: BaseExpr, rhs: BaseExpr) -> BaseExpr:
    d = Sub(lhs, rhs)
    return Mul(d, d)


def BoolZ(b: BaseExpr) -> BaseExpr:
    return Mul(b, Sub(Const(1), b))

# Hilbert syntax + checker (semantic reference)

@dataclass(frozen=True)
class Form:
    tag: str
    a: "Form | None" = None
    b: "Form | None" = None


BOT = Form("bot")


def Imp(a: Form, b: Form) -> Form:
    return Form("imp", a, b)


def _match_k(phi: Form) -> bool:
    if phi.tag != "imp" or phi.a is None or phi.b is None:
        return False
    X = phi.a
    rhs = phi.b
    return rhs.tag == "imp" and rhs.a is not None and rhs.b is not None and rhs.b == X


def _match_s(phi: Form) -> bool:
    # (A -> (B -> C)) -> ((A -> B) -> (A -> C))
    if phi.tag != "imp" or phi.a is None or phi.b is None:
        return False
    left = phi.a
    right = phi.b
    if left.tag != "imp" or left.a is None or left.b is None:
        return False
    A = left.a
    left_tail = left.b
    if left_tail.tag != "imp" or left_tail.a is None or left_tail.b is None:
        return False
    B = left_tail.a
    C = left_tail.b

    if right.tag != "imp" or right.a is None or right.b is None:
        return False
    r1 = right.a
    r2 = right.b
    if r1.tag != "imp" or r1.a is None or r1.b is None:
        return False
    if r2.tag != "imp" or r2.a is None or r2.b is None:
        return False
    return r1.a == A and r1.b == B and r2.a == A and r2.b == C


def _match_efq(phi: Form) -> bool:
    # Bot -> X
    return phi.tag == "imp" and phi.a == BOT


def is_axiom(phi: Form) -> bool:
    return _match_k(phi) or _match_s(phi) or _match_efq(phi)


def check_proof(pf: Sequence[Form], goal: Form) -> bool:
    if not pf:
        return False
    for i, phi in enumerate(pf):
        if is_axiom(phi):
            continue
        ok_mp = False
        for k in range(i):
            psi = pf[k]
            if psi.tag != "imp" or psi.a is None or psi.b is None:
                continue
            if psi.b != phi:
                continue
            for j in range(i):
                if pf[j] == psi.a:
                    ok_mp = True
                    break
            if ok_mp:
                break
        if not ok_mp:
            return False
    return pf[-1] == goal

# Coding + bounded pairing (representation-level semantics)

def _fib_weights(width: int) -> List[int]:
    """Return [F2, F3, ..., F_{width+1}] with F2=1, F3=2."""
    if width <= 0:
        return []
    out = [1]
    if width == 1:
        return out
    out.append(2)
    for _ in range(2, width):
        out.append(out[-1] + out[-2])
    return out


def _max_zeck(width: int) -> int:
    if width <= 0:
        return 0
    f = [0, 1]
    for _ in range(width + 2):
        f.append(f[-1] + f[-2])
    return f[width + 2] - 1


def zeck_encode(n: int, width: int) -> List[int]:
    if n < 0:
        raise ValueError("zeck_encode expects nonnegative n")
    if n > _max_zeck(width):
        raise ValueError(f"n={n} is out of range for zeck width={width}")

    ws = _fib_weights(width)
    ds = [0] * width
    rem = n
    for i in range(width - 1, -1, -1):
        w = ws[i]
        if w <= rem:
            if i + 1 < width and ds[i + 1] == 1:
                continue
            ds[i] = 1
            rem -= w
    if rem != 0:
        raise ValueError(f"failed Zeckendorf encoding for n={n}, width={width}")
    return ds


def zeck_decode(ds: Sequence[int]) -> int:
    ws = _fib_weights(len(ds))
    acc = 0
    for d, w in zip(ds, ws):
        acc += int(d) * w
    return acc


def zeck_is_admissible(ds: Sequence[int]) -> bool:
    for d in ds:
        if d not in (0, 1):
            return False
    return all(not (ds[i] == 1 and ds[i + 1] == 1) for i in range(len(ds) - 1))


def pair_value(x: int, y: int, width: int) -> int:
    """
    Bounded carryless pairing over Zeck digits.

    Gap-4 carryless mapping over Zeck digits:
      z[4*i] = x[i], z[4*i+2] = y[i], all other z-digits = 0.
    width is the output-digit width (must be divisible by 4).
    """
    if width < 4 or width % 4 != 0:
        raise ValueError("pair_value requires width divisible by 4 and >= 4")
    lane = width // 4
    dx = zeck_encode(x, lane)
    dy = zeck_encode(y, lane)
    dz = [0] * width
    for i in range(lane):
        dz[4 * i] = dx[i]
        dz[4 * i + 2] = dy[i]
    if not zeck_is_admissible(dz):
        raise ValueError("internal error: gap-4 pairing produced non-admissible Zeckendorf digits")
    return zeck_decode(dz)


def unpair_value(z: int, width: int) -> tuple[int, int]:
    if width < 4 or width % 4 != 0:
        raise ValueError("unpair_value requires width divisible by 4 and >= 4")
    lane = width // 4
    dz = zeck_encode(z, width)
    dx = [dz[4 * i] for i in range(lane)]
    dy = [dz[4 * i + 2] for i in range(lane)]
    return zeck_decode(dx), zeck_decode(dy)


def enc_form(phi: Form, width: int) -> int:
    if phi.tag == "bot":
        return 0
    if phi.tag != "imp" or phi.a is None or phi.b is None:
        raise ValueError(f"malformed form: {phi!r}")
    return 1 + pair_value(enc_form(phi.a, width), enc_form(phi.b, width), width)


def code_list(xs: Sequence[int], width: int) -> int:
    acc = 0
    for x in reversed(xs):
        acc = 1 + pair_value(int(x), acc, width)
    return acc


def code_pf(pf: Sequence[Form], width: int) -> int:
    return code_list([enc_form(phi, width) for phi in pf], width)


def code_of_concrete(pf: Sequence[Form], goal: Form, width: int) -> int:
    return pair_value(code_pf(pf, width), enc_form(goal, width), width)


def decode_form(code: int, width: int, fuel: int) -> Form:
    if fuel <= 0 or code == 0:
        return BOT
    pred = code - 1
    if pred < 0:
        return BOT
    a, b = unpair_value(pred, width)
    return Imp(decode_form(a, width, fuel - 1), decode_form(b, width, fuel - 1))


def decode_list(code: int, width: int, fuel: int) -> List[int]:
    out: List[int] = []
    cur = code
    steps = 0
    while cur != 0 and steps < fuel:
        pred = cur - 1
        if pred < 0:
            break
        x, rest = unpair_value(pred, width)
        out.append(x)
        cur = rest
        steps += 1
    return out

# Constraint compiler for C_{n,t}

class ConstraintCompiler:
    def __init__(self, n_lines: int, digit_width: int, allow_nonadjacent_digits: bool = False):
        if n_lines <= 0:
            raise ValueError("n_lines must be positive")
        if digit_width < 4 or digit_width % 4 != 0:
            raise ValueError("digit_width must be divisible by 4 and >= 4")
        self.n_lines = n_lines
        self.digit_width = digit_width
        self.allow_nonadjacent_digits = allow_nonadjacent_digits
        self.equations: List[Equation] = []
        self.poly_constraints: List[PolyConstraint] = []
        self.has_degree3_poly: bool = False
        self.has_selector_times_quadratic: bool = False
        self._repr_cache: Dict[tuple[str, int], List[BaseExpr]] = {}
        self._repr_emit_count: Dict[tuple[str, int], int] = {}
        self._succ_heads: set[str] = set()
        self._succ_preds: set[str] = set()
        self.pair_links: List[tuple[str, str, str, int]] = []

    def _add_eq(self, lhs: BaseExpr, rhs: BaseExpr) -> None:
        self.equations.append(Eq(lhs, rhs))

    def _add_poly(
        self,
        poly: BaseExpr,
        tag: str,
        selector: str | None = None,
        source_degree: int | None = None,
    ) -> None:
        assert_degree_le(poly, 3)
        self.poly_constraints.append(
            PolyConstraint(
                poly=poly,
                tag=tag,
                selector=selector,
                source_degree=source_degree,
            )
        )
        if poly.deg == 3:
            self.has_degree3_poly = True
        if selector is not None and source_degree == 2 and poly.deg == 3:
            self.has_selector_times_quadratic = True

    def _bool(self, name: str) -> BaseExpr:
        b = Var(name)
        self._add_poly(BoolZ(b), tag=f"bool:{name}")
        return b

    def _gate(self, sel: BaseExpr, eqs: Sequence[Equation]) -> None:
        sel_name = _var_name(sel)
        for idx, e in enumerate(eqs):
            q = EqZ(e.lhs, e.rhs)
            activated = Mul(sel, q)
            self._add_poly(
                activated,
                tag=f"gate[{idx}]",
                selector=sel_name,
                source_degree=q.deg,
            )

    def _ensure_zeck_repr(self, v: BaseExpr, width: int) -> List[BaseExpr]:
        if v.op != "var":
            raise ValueError("Zeckendorf representation is supported only for variables")
        key = (str(v.value), width)
        if key in self._repr_cache:
            return self._repr_cache[key]

        eq_before = len(self.equations)
        digits = [Var(f"d_{v.value}_{width}_{i}") for i in range(width)]
        ws = _fib_weights(width)

        for d in digits:
            self._add_eq(d, Mul(d, d))
        if not self.allow_nonadjacent_digits:
            for i in range(width - 1):
                self._add_eq(Mul(digits[i], digits[i + 1]), Const(0))

        weighted = [Mul(Const(ws[i]), digits[i]) for i in range(width)]
        self._add_eq(v, add_many(weighted))

        self._repr_cache[key] = digits
        expected = width + (0 if self.allow_nonadjacent_digits else (width - 1)) + 1
        emitted = len(self.equations) - eq_before
        if emitted != expected:
            raise AssertionError(
                f"invalid Zeckendorf representation emission for {key}: "
                f"expected {expected} constraints, got {emitted}"
            )
        self._repr_emit_count[key] = emitted
        return digits

    def _pair_relation(self, z: BaseExpr, x: BaseExpr, y: BaseExpr, width: int) -> List[Equation]:
        """
        Gap-4 carryless pair relation over Zeck digits:
          z[4*i]   = x[i]
          z[4*i+2] = y[i]
          z[4*i+1] = 0
          z[4*i+3] = 0
        where x/y are represented at lane width width/4 and z at width.
        """
        if width % 4 != 0 or width < 4:
            raise ValueError("pair relation width must be divisible by 4 and >= 4")
        lane = width // 4

        dx = self._ensure_zeck_repr(x, lane)
        dy = self._ensure_zeck_repr(y, lane)
        dz = self._ensure_zeck_repr(z, width)
        if z.op == "var" and x.op == "var" and y.op == "var":
            self.pair_links.append((str(z.value), str(x.value), str(y.value), width))

        out: List[Equation] = []
        for i in range(lane):
            out.append(Eq(dz[4 * i], dx[i]))
            out.append(Eq(dz[4 * i + 2], dy[i]))
            out.append(Eq(dz[4 * i + 1], Const(0)))
            out.append(Eq(dz[4 * i + 3], Const(0)))
        return out

    def _succ_eq(self, head: BaseExpr, pred: BaseExpr, width: int) -> Equation:
        head_name = _var_name(head)
        pred_name = _var_name(pred)
        if head_name is None or pred_name is None:
            raise ValueError("successor equations must be between variables")
        _ = width
        self._succ_heads.add(head_name)
        self._succ_preds.add(pred_name)
        return Eq(head, Add(Const(1), pred))

    def _imp_decompose(self, f: BaseExpr, prefix: str, width: int) -> tuple[BaseExpr, BaseExpr, List[Equation]]:
        # f = 1 + pair(A,B)
        A = Var(f"{prefix}_A")
        B = Var(f"{prefix}_B")
        pred = Var(f"{prefix}_pred")
        eqs: List[Equation] = [self._succ_eq(f, pred, width)]
        eqs.extend(self._pair_relation(pred, A, B, width))
        return A, B, eqs

    def _schema_k(self, f: BaseExpr, prefix: str, width: int) -> List[Equation]:
        # X -> (Y -> X)
        X, rhs, eq0 = self._imp_decompose(f, f"{prefix}_k0", width)
        Y, X2, eq1 = self._imp_decompose(rhs, f"{prefix}_k1", width)
        del Y
        return eq0 + eq1 + [Eq(X, X2)]

    def _schema_efq(self, f: BaseExpr, prefix: str, width: int) -> List[Equation]:
        # Bot -> X
        A, _B, eq0 = self._imp_decompose(f, f"{prefix}_e0", width)
        return eq0 + [Eq(A, Const(0))]

    def _schema_s(self, f: BaseExpr, prefix: str, width: int) -> List[Equation]:
        # (A -> (B -> C)) -> ((A -> B) -> (A -> C))
        L, R, eq0 = self._imp_decompose(f, f"{prefix}_s0", width)
        A0, BC, eq1 = self._imp_decompose(L, f"{prefix}_s1", width)
        B0, C0, eq2 = self._imp_decompose(BC, f"{prefix}_s2", width)

        R1, R2, eq3 = self._imp_decompose(R, f"{prefix}_s3", width)
        A1, B1, eq4 = self._imp_decompose(R1, f"{prefix}_s4", width)
        A2, C1, eq5 = self._imp_decompose(R2, f"{prefix}_s5", width)

        return eq0 + eq1 + eq2 + eq3 + eq4 + eq5 + [
            Eq(A0, A1),
            Eq(A1, A2),
            Eq(B0, B1),
            Eq(C0, C1),
        ]

    def _compile_axiom_family(self, i: int, f_i: BaseExpr, a_i: BaseExpr) -> None:
        sel_k = self._bool(f"selK_{i}")
        sel_s = self._bool(f"selS_{i}")
        sel_e = self._bool(f"selE_{i}")

        # Tightening: schema selectors must be inactive unless axiom branch is active.
        self._add_eq(sel_k, Mul(a_i, sel_k))
        self._add_eq(sel_s, Mul(a_i, sel_s))
        self._add_eq(sel_e, Mul(a_i, sel_e))

        self._add_eq(Mul(a_i, add_many([sel_k, sel_s, sel_e])), a_i)

        self._gate(sel_k, self._schema_k(f_i, f"l{i}", self.digit_width))
        self._gate(sel_s, self._schema_s(f_i, f"l{i}", self.digit_width))
        self._gate(sel_e, self._schema_efq(f_i, f"l{i}", self.digit_width))

    def _compile_mp_family(self, i: int, f_lines: Sequence[BaseExpr], m_i: BaseExpr) -> None:
        if i == 0:
            self._add_eq(m_i, Const(0))
            return

        selectors_all: List[BaseExpr] = []
        for j in range(i):
            imp_j_i = Var(f"imp_{i}_{j}")
            pred = Var(f"imp_{i}_{j}_pred")
            imp_eqs: List[Equation] = [Eq(imp_j_i, Add(Const(1), pred))]
            imp_eqs.extend(self._pair_relation(pred, f_lines[j], f_lines[i], self.digit_width))

            selectors_j: List[BaseExpr] = []
            for k in range(i):
                s = self._bool(f"mp_{i}_{j}_{k}")
                selectors_j.append(s)
                selectors_all.append(s)
                self._gate(s, [Eq(f_lines[k], imp_j_i)])

            # Share implication construction across k for fixed (i,j).
            sel_j = add_many(selectors_j)
            self._gate(sel_j, imp_eqs)

        self._add_eq(Mul(m_i, add_many(selectors_all)), m_i)

    def emit(self) -> List[Equation]:
        # Public / headline variables
        u = Var("trace_code")
        t = Var("goal_code")
        p = Var("proof_code")

        # u = pair(p,t)
        for e in self._pair_relation(u, p, t, self.digit_width):
            self.equations.append(e)

        # List extraction chain
        f_lines = [Var(f"f_{i}") for i in range(self.n_lines)]
        tails = [Var(f"tail_{i}") for i in range(self.n_lines + 1)]

        self._add_eq(tails[0], p)
        for i in range(self.n_lines):
            pred = Var(f"tail_pred_{i}")
            self.equations.append(self._succ_eq(tails[i], pred, self.digit_width))
            for e in self._pair_relation(pred, f_lines[i], tails[i + 1], self.digit_width):
                self.equations.append(e)
        self._add_eq(tails[self.n_lines], Const(0))

        # Line validation: each line is axiom or MP
        for i in range(self.n_lines):
            a_i = self._bool(f"a_{i}")
            m_i = self._bool(f"m_{i}")
            self._add_eq(add_many([a_i, m_i]), Const(1))

            self._compile_axiom_family(i, f_lines[i], a_i)
            self._compile_mp_family(i, f_lines, m_i)

        # Target match
        self._add_eq(f_lines[-1], t)

        # Hard invariant: each registered Zeck-representation was emitted exactly once.
        if len(self._repr_emit_count) != len(self._repr_cache):
            raise AssertionError("representation emission bookkeeping mismatch")
        # Any variable used as a successor head/pred must be representation-bound:
        # either directly Zeck-represented or alias-equal to such a variable.
        repr_vars = {name for (name, _width) in self._repr_cache.keys()}
        alias_graph: Dict[str, set[str]] = {}
        for e in self.equations:
            a = _var_name(e.lhs)
            b = _var_name(e.rhs)
            if a is None or b is None:
                continue
            if a not in alias_graph:
                alias_graph[a] = set()
            if b not in alias_graph:
                alias_graph[b] = set()
            alias_graph[a].add(b)
            alias_graph[b].add(a)

        bound_vars = set(repr_vars)
        stack = list(repr_vars)
        while stack:
            v = stack.pop()
            for nb in alias_graph.get(v, ()):
                if nb in bound_vars:
                    continue
                bound_vars.add(nb)
                stack.append(nb)

        for name in sorted(self._succ_heads | self._succ_preds):
            if name not in bound_vars:
                raise AssertionError(
                    f"successor variable {name} is not representation-bound in _repr_cache"
                )

        if not self.has_selector_times_quadratic:
            raise AssertionError(
                "no activated selector*quadratic constraint found; TeX activation layer missing"
            )
        if not self.has_degree3_poly:
            raise AssertionError(
                "polynomial stage emitted no degree-3 constraints; expected selector-activated quadratics"
            )

        poly_channels = [_poly_to_equation_channel(pc.poly) for pc in self.poly_constraints]
        return self.equations + poly_channels


def _collect_vars_rec(expr: BaseExpr, acc: set[str]) -> None:
    if expr.op == "var":
        acc.add(str(expr.value))
        return
    for a in expr.args:
        _collect_vars_rec(a, acc)


def emit_cubic_system(
    n_lines: int,
    digit_width: int,
    allow_nonadjacent_digits: bool = False,
) -> Dict[str, int | List[Equation]]:
    cc = ConstraintCompiler(
        n_lines=n_lines,
        digit_width=digit_width,
        allow_nonadjacent_digits=allow_nonadjacent_digits,
    )
    constraints = cc.emit()

    max_deg = 0
    var_names: set[str] = set()
    for e in constraints:
        max_deg = max(max_deg, e.lhs.deg, e.rhs.deg)
        _collect_vars_rec(e.lhs, var_names)
        _collect_vars_rec(e.rhs, var_names)

    return {
        "constraints": constraints,
        "num_constraints": len(constraints),
        "num_vars": len(var_names),
        "max_deg": max_deg,
        "has_degree_3_pre": cc.has_degree3_poly,
        "activated_selector_quadratic_exists": cc.has_selector_times_quadratic,
        "poly_constraint_count": len(cc.poly_constraints),
    }


def assert_equation_channels_well_formed(constraints: Sequence[Equation]) -> None:
    for idx, e in enumerate(constraints):
        try:
            _assert_sub_free_nonneg(e.lhs)
            _assert_sub_free_nonneg(e.rhs)
            assert_degree_le(e.lhs, 3)
            assert_degree_le(e.rhs, 3)
        except Exception as ex:
            raise ValueError(f"malformed equation channel at index {idx}: {ex}") from ex


def eval_expr(expr: BaseExpr, env: Dict[str, int]) -> int:
    if expr.op == "const":
        return int(expr.value)  # type: ignore[arg-type]
    if expr.op == "var":
        return int(env.get(str(expr.value), 0))
    if expr.op == "add":
        return eval_expr(expr.args[0], env) + eval_expr(expr.args[1], env)
    if expr.op == "mul":
        return eval_expr(expr.args[0], env) * eval_expr(expr.args[1], env)
    if expr.op == "sub":
        return eval_expr(expr.args[0], env) - eval_expr(expr.args[1], env)
    raise ValueError(f"unknown op: {expr.op}")


def check_equations(eqs: Sequence[Equation], env: Dict[str, int]) -> List[Tuple[int, int, int]]:
    bad: List[Tuple[int, int, int]] = []
    for idx, e in enumerate(eqs):
        lv = eval_expr(e.lhs, env)
        rv = eval_expr(e.rhs, env)
        if lv != rv:
            bad.append((idx, lv, rv))
    return bad


def _min_width_for_instance(pf: Sequence[Form], goal: Form, start: int = 16, limit: int = 2048) -> int:
    for width in range(max(4, start + ((4 - start % 4) % 4)), limit + 1, 4):
        try:
            _ = code_of_concrete(pf, goal, width)
            return width
        except ValueError:
            pass
    raise AssertionError(f"failed to find representable width up to {limit}")


def _expr_var_names(expr: BaseExpr) -> List[str]:
    names: set[str] = set()
    _collect_vars_rec(expr, names)
    return sorted(names)


def _schema_name(phi: Form) -> str | None:
    if _match_k(phi):
        return "K"
    if _match_s(phi):
        return "S"
    if _match_efq(phi):
        return "E"
    return None


def _mp_witness(pf: Sequence[Form], i: int) -> tuple[int, int] | None:
    tgt = pf[i]
    for k in range(i):
        psi = pf[k]
        if psi.tag != "imp" or psi.a is None or psi.b is None:
            continue
        if psi.b != tgt:
            continue
        for j in range(i):
            if pf[j] == psi.a:
                return j, k
    return None


def _set_var(env: Dict[str, int], name: str, value: int) -> None:
    env[name] = int(value)


def _assign_imp_from_codes(env: Dict[str, int], prefix: str, a_code: int, b_code: int, width: int) -> None:
    pred = pair_value(a_code, b_code, width)
    _set_var(env, f"{prefix}_A", a_code)
    _set_var(env, f"{prefix}_B", b_code)
    _set_var(env, f"{prefix}_pred", pred)


def _collect_equation_vars(eqs: Sequence[Equation]) -> List[str]:
    names: set[str] = set()
    for e in eqs:
        _collect_vars_rec(e.lhs, names)
        _collect_vars_rec(e.rhs, names)
    return sorted(names)


def _four_squares_decompose(n: int) -> tuple[int, int, int, int]:
    if n < 0:
        raise ValueError(f"cannot decompose negative value as four squares: {n}")
    lim_a = int(n ** 0.5)
    for a in range(lim_a + 1):
        ra = n - a * a
        lim_b = int(ra ** 0.5)
        for b in range(lim_b + 1):
            rb = ra - b * b
            lim_c = int(rb ** 0.5)
            for c in range(lim_c + 1):
                rd = rb - c * c
                d = int(rd ** 0.5)
                if d * d == rd:
                    return a, b, c, d
    raise ValueError(f"failed four-square decomposition for n={n}")


def build_witness(
    pf: Sequence[Form],
    goal: Form,
    digit_width: int,
    validate: bool = True,
    allow_nonadjacent_digits: bool = False,
) -> Dict[str, int]:
    """
    Deterministic witness constructor for the bounded C_{n,t} system.
    """
    if not pf:
        raise ValueError("pf must be non-empty")
    if not check_proof(pf, goal):
        raise ValueError("input proof is not accepted by semantic checker")

    n_lines = len(pf)
    cc = ConstraintCompiler(
        n_lines=n_lines,
        digit_width=digit_width,
        allow_nonadjacent_digits=allow_nonadjacent_digits,
    )
    eqs = cc.emit()

    env: Dict[str, int] = {name: 0 for name in _collect_equation_vars(eqs)}
    f_codes = [enc_form(phi, digit_width) for phi in pf]
    t_code = enc_form(goal, digit_width)
    p_code = code_list(f_codes, digit_width)
    u_code = pair_value(p_code, t_code, digit_width)

    _set_var(env, "goal_code", t_code)
    _set_var(env, "proof_code", p_code)
    _set_var(env, "trace_code", u_code)

    tails = [0] * (n_lines + 1)
    tails[-1] = 0
    for i in range(n_lines - 1, -1, -1):
        tails[i] = 1 + pair_value(f_codes[i], tails[i + 1], digit_width)
    for i in range(n_lines):
        _set_var(env, f"f_{i}", f_codes[i])
        _set_var(env, f"tail_{i}", tails[i])
        _set_var(env, f"tail_pred_{i}", tails[i] - 1)
    _set_var(env, f"tail_{n_lines}", 0)

    for i, phi in enumerate(pf):
        schema = _schema_name(phi)
        if schema is not None:
            _set_var(env, f"a_{i}", 1)
            _set_var(env, f"m_{i}", 0)
            _set_var(env, f"selK_{i}", 1 if schema == "K" else 0)
            _set_var(env, f"selS_{i}", 1 if schema == "S" else 0)
            _set_var(env, f"selE_{i}", 1 if schema == "E" else 0)

            if schema == "K":
                if phi.tag != "imp" or phi.a is None or phi.b is None or phi.b.tag != "imp" or phi.b.a is None or phi.b.b is None:
                    raise ValueError(f"malformed K-line at {i}")
                x = phi.a
                y = phi.b.a
                rhs = phi.b
                _assign_imp_from_codes(env, f"l{i}_k0", enc_form(x, digit_width), enc_form(rhs, digit_width), digit_width)
                _assign_imp_from_codes(env, f"l{i}_k1", enc_form(y, digit_width), enc_form(x, digit_width), digit_width)
            elif schema == "S":
                if (
                    phi.tag != "imp" or phi.a is None or phi.b is None
                    or phi.a.tag != "imp" or phi.a.a is None or phi.a.b is None
                    or phi.a.b.tag != "imp" or phi.a.b.a is None or phi.a.b.b is None
                    or phi.b.tag != "imp" or phi.b.a is None or phi.b.b is None
                    or phi.b.a.tag != "imp" or phi.b.a.a is None or phi.b.a.b is None
                    or phi.b.b.tag != "imp" or phi.b.b.a is None or phi.b.b.b is None
                ):
                    raise ValueError(f"malformed S-line at {i}")
                a0 = phi.a.a
                b0 = phi.a.b.a
                c0 = phi.a.b.b
                r1 = phi.b.a
                r2 = phi.b.b
                _assign_imp_from_codes(env, f"l{i}_s0", enc_form(phi.a, digit_width), enc_form(phi.b, digit_width), digit_width)
                _assign_imp_from_codes(env, f"l{i}_s1", enc_form(a0, digit_width), enc_form(phi.a.b, digit_width), digit_width)
                _assign_imp_from_codes(env, f"l{i}_s2", enc_form(b0, digit_width), enc_form(c0, digit_width), digit_width)
                _assign_imp_from_codes(env, f"l{i}_s3", enc_form(r1, digit_width), enc_form(r2, digit_width), digit_width)
                _assign_imp_from_codes(env, f"l{i}_s4", enc_form(r1.a, digit_width), enc_form(r1.b, digit_width), digit_width)  # type: ignore[arg-type]
                _assign_imp_from_codes(env, f"l{i}_s5", enc_form(r2.a, digit_width), enc_form(r2.b, digit_width), digit_width)  # type: ignore[arg-type]
            else:
                if phi.tag != "imp" or phi.a is None or phi.b is None:
                    raise ValueError(f"malformed EFQ-line at {i}")
                _assign_imp_from_codes(env, f"l{i}_e0", enc_form(phi.a, digit_width), enc_form(phi.b, digit_width), digit_width)
        else:
            w = _mp_witness(pf, i)
            if w is None:
                raise ValueError(f"failed to find MP witness for line {i}")
            j_star, k_star = w
            _set_var(env, f"a_{i}", 0)
            _set_var(env, f"m_{i}", 1)
            _set_var(env, f"selK_{i}", 0)
            _set_var(env, f"selS_{i}", 0)
            _set_var(env, f"selE_{i}", 0)

            for j in range(i):
                imp = 1 + pair_value(f_codes[j], f_codes[i], digit_width)
                _set_var(env, f"imp_{i}_{j}", imp)
                _set_var(env, f"imp_{i}_{j}_pred", imp - 1)
                for k in range(i):
                    _set_var(env, f"mp_{i}_{j}_{k}", 1 if (j == j_star and k == k_star) else 0)

    # Fill representational digits from assigned values, then enforce pair-link equalities directly at the digit level.

    digit_values: Dict[tuple[str, int], List[int]] = {}
    for (var_name, width), _digits in cc._repr_cache.items():
        value = env.get(var_name, 0)
        if value < 0:
            raise ValueError(f"negative value for representational variable {var_name}: {value}")
        digit_values[(var_name, width)] = zeck_encode(value, width)

    for _ in range(3):
        for z_name, x_name, y_name, width in cc.pair_links:
            lane = width // 4
            dx = digit_values[(x_name, lane)]
            dy = digit_values[(y_name, lane)]
            dz = digit_values[(z_name, width)]
            for i in range(lane):
                dz[4 * i] = dx[i]
                dz[4 * i + 2] = dy[i]
                dz[4 * i + 1] = 0
                dz[4 * i + 3] = 0

    value_by_var: Dict[str, int] = {}
    for (var_name, width), ds in digit_values.items():
        if not allow_nonadjacent_digits and not zeck_is_admissible(ds):
            raise ValueError(f"nonadmissible Zeckendorf digits for {var_name}/{width}")
        v = zeck_decode(ds)
        if var_name in value_by_var and value_by_var[var_name] != v:
            raise ValueError(
                f"inconsistent representational value for {var_name}: "
                f"{value_by_var[var_name]} vs {v}"
            )
        value_by_var[var_name] = v
    for var_name, v in value_by_var.items():
        _set_var(env, var_name, v)
    for (var_name, width), ds in digit_values.items():
        for idx, d in enumerate(ds):
            _set_var(env, f"d_{var_name}_{width}_{idx}", d)

    if validate:
        bad = check_equations(eqs, env)
        if bad:
            i, lv, rv = bad[0]
            raise ValueError(f"pre-aggregation witness failed at eq#{i}: lhs={lv}, rhs={rv}")

    return env

# Aggregation

def _four_squares_capacity(var: BaseExpr, base: int, slack_prefix: str) -> List[Equation]:
    # base - 1 = var + s1^2 + s2^2 + s3^2 + s4^2
    s_vars = [Var(f"{slack_prefix}_{i}") for i in range(4)]
    rhs = add_many(
        [
            var,
            Mul(s_vars[0], s_vars[0]),
            Mul(s_vars[1], s_vars[1]),
            Mul(s_vars[2], s_vars[2]),
            Mul(s_vars[3], s_vars[3]),
        ]
    )
    return [Eq(Const(base - 1), rhs)]


def _legacy_weights(count: int, base: int) -> List[int]:
    weights: List[int] = []
    power = 1
    for _ in range(count):
        weights.append(power)
        power *= base
    return weights


def _hierarchical_weights(count: int, inner_base: int, outer_base: int, block_size: int) -> List[int]:
    if block_size <= 0:
        raise ValueError("block_size must be positive")

    inner_pows: List[int] = [1]
    for _ in range(1, block_size):
        inner_pows.append(inner_pows[-1] * inner_base)

    weights: List[int] = []
    outer_pow = 1
    for idx in range(count):
        if idx > 0 and idx % block_size == 0:
            outer_pow *= outer_base
        offset = idx % block_size
        weights.append(outer_pow * inner_pows[offset])
    return weights


def aggregate(
    constraints: List[Equation],
    base: int = 5,
    mode: str = "hierarchical",
    block_size: int = 32,
    outer_base: int | None = None,
) -> tuple[BaseExpr, List[Equation]]:
    """Aggregate equation channels into one polynomial U plus capacity equations."""
    if base < 2:
        raise ValueError("base must be >= 2")
    if mode not in {"legacy", "hierarchical"}:
        raise ValueError(f"Unknown aggregation mode: {mode}")
    if mode == "hierarchical" and block_size <= 0:
        raise ValueError("block_size must be positive in hierarchical mode")

    if outer_base is None:
        outer_base = base + 2
    if outer_base < 2:
        raise ValueError("outer_base must be >= 2")

    capacity: List[Equation] = []
    for idx, e in enumerate(constraints):
        capacity.extend(_four_squares_capacity(e.lhs, base, f"a{idx}"))
        capacity.extend(_four_squares_capacity(e.rhs, base, f"b{idx}"))

    all_eqs = constraints + capacity
    if mode == "legacy":
        weights = _legacy_weights(len(all_eqs), base)
    else:
        weights = _hierarchical_weights(
            len(all_eqs),
            inner_base=base,
            outer_base=outer_base,
            block_size=block_size,
        )

    left_terms: List[Tuple[int, BaseExpr]] = []
    right_terms: List[Tuple[int, BaseExpr]] = []
    for w, e in zip(weights, all_eqs):
        left_terms.append((w, e.lhs))
        right_terms.append((w, e.rhs))

    # Important:
    # - Equation channels are nonnegative/sub-free by construction.
    # - Final aggregated polynomial is over Z and may contain subtraction.
    left_poly = linear_combination(left_terms)
    right_poly = linear_combination(right_terms)
    U = Sub(left_poly, right_poly)
    assert_degree_le(U, 3)
    return U, capacity

# Compiler

@dataclass
class CompileResult:
    base: int
    channel_count: int
    aggregation_mode: str
    aggregation_block_size: int | None
    aggregation_outer_base: int | None
    encoding: str
    pairing_layout: str
    successor: str
    debug_nonadjacency_disabled: bool
    n_lines: int
    digit_width: int
    max_repr_lane: int
    max_repr_full: int
    max_degree: int
    has_degree_3: bool
    count_degree_3_monomials: int
    monomials: List[Tuple[int, Tuple[Tuple[int, int], ...]]]
    var_order: List[str]
    public_vars: Dict[str, int]
    max_coeff_digits: int
    hash: str
    json_size_bytes: int


def _collect_vars(expr: BaseExpr, acc: List[str]) -> None:
    stack = [expr]
    while stack:
        e = stack.pop()
        if e.op == "var":
            acc.append(str(e.value))
        stack.extend(e.args)


def _resolve_var_order(
    all_vars: Sequence[str],
    public_var_map: Sequence[Tuple[str, str]],
    reserve_public_slots: bool,
) -> tuple[List[str], Dict[str, int]]:
    sorted_vars = sorted(set(all_vars))
    ordered_public_var_names: List[str] = []
    for _, var_name in public_var_map:
        if var_name not in ordered_public_var_names:
            ordered_public_var_names.append(var_name)

    if reserve_public_slots:
        tail_vars = [v for v in sorted_vars if v not in ordered_public_var_names]
        var_order = ordered_public_var_names + tail_vars
    else:
        missing = [var_name for _, var_name in public_var_map if var_name not in sorted_vars]
        if missing:
            raise ValueError(
                "Public variable(s) missing from compiled polynomial; "
                "use --reserve-public-slots if you want to reserve indices anyway: "
                + ", ".join(missing)
            )
        var_order = sorted_vars

    var_index = {v: i for i, v in enumerate(var_order)}
    public_vars = {pub: var_index[var_name] for pub, var_name in public_var_map}
    return var_order, public_vars


def _parse_public_vars(spec: str) -> List[Tuple[str, str]]:
    entries = [tok.strip() for tok in spec.split(",") if tok.strip()]
    out: List[Tuple[str, str]] = []
    seen_public: set[str] = set()
    for entry in entries:
        if ":" in entry:
            public_name, var_name = [p.strip() for p in entry.split(":", 1)]
        else:
            public_name, var_name = entry, entry
        if not public_name or not var_name:
            raise ValueError(f"Invalid public-vars entry: {entry!r}")
        if public_name in seen_public:
            raise ValueError(f"Duplicate public variable key: {public_name}")
        seen_public.add(public_name)
        out.append((public_name, var_name))
    return out


def _monomials(expr: BaseExpr) -> Dict[Tuple[Tuple[str, int], ...], int]:
    """Expand expr into monomials map: key->coeff, key is tuple of (var,exp)."""

    def add_poly(p: Dict[Tuple[Tuple[str, int], ...], int], q: Dict[Tuple[Tuple[str, int], ...], int], sign: int = 1):
        for k, v in q.items():
            p[k] = p.get(k, 0) + sign * v
        return p

    def mul_poly(pa: Dict[Tuple[Tuple[str, int], ...], int], pb: Dict[Tuple[Tuple[str, int], ...], int]):
        out: Dict[Tuple[Tuple[str, int], ...], int] = {}
        for ka, va in pa.items():
            for kb, vb in pb.items():
                coeff = va * vb
                if coeff == 0:
                    continue
                exps: Dict[str, int] = {}
                for v, e in ka:
                    exps[v] = exps.get(v, 0) + e
                for v, e in kb:
                    exps[v] = exps.get(v, 0) + e
                key = tuple(sorted((v, e) for v, e in exps.items() if e))
                out[key] = out.get(key, 0) + coeff
        return out

    stack: List[Tuple[BaseExpr, bool]] = [(expr, False)]
    memo: Dict[int, Dict[Tuple[Tuple[str, int], ...], int]] = {}

    while stack:
        node, done = stack.pop()
        if id(node) in memo:
            continue
        if not done:
            stack.append((node, True))
            for a in node.args:
                stack.append((a, False))
            continue

        if node.op == "const":
            memo[id(node)] = {(): int(node.value)}  # type: ignore[arg-type]
        elif node.op == "var":
            memo[id(node)] = {((str(node.value), 1),): 1}
        else:
            if len(node.args) != 2:
                raise ValueError(f"Expected binary node for op {node.op}: {node!r}")
            a, b = node.args
            pa = memo[id(a)]
            pb = memo[id(b)]
            if node.op == "add":
                memo[id(node)] = add_poly(dict(pa), pb, sign=1)
            elif node.op == "sub":
                memo[id(node)] = add_poly(dict(pa), pb, sign=-1)
            elif node.op == "mul":
                memo[id(node)] = mul_poly(pa, pb)
            else:
                raise ValueError(f"Unknown op {node.op}")

    mono = memo[id(expr)]
    return {k: v for k, v in mono.items() if v != 0}


def _pow_expr(base: BaseExpr, exp: int) -> BaseExpr:
    if exp < 0:
        raise ValueError(f"negative exponent not supported: {exp}")
    if exp == 0:
        return Const(1)
    acc = Const(1)
    for _ in range(exp):
        acc = Mul(acc, base)
    return acc


def _build_monom_term(coeff: int, key: Tuple[Tuple[str, int], ...]) -> BaseExpr:
    if coeff < 0:
        raise ValueError(f"coefficient must be nonnegative in channelized monomial: {coeff}")
    term: BaseExpr = Const(coeff)
    for v, e in key:
        term = Mul(term, _pow_expr(Var(v), e))
    return term


def _poly_to_equation_channel(poly: BaseExpr) -> Equation:
    """
    Two-channel decomposition:
      P = A - B  with A,B subtraction-free and nonnegative-coefficient.
    Channelized form is A = B.
    """
    mono = _monomials(poly)
    lhs_terms: List[BaseExpr] = []
    rhs_terms: List[BaseExpr] = []
    for key, coeff in mono.items():
        if coeff > 0:
            lhs_terms.append(_build_monom_term(coeff, key))
        elif coeff < 0:
            rhs_terms.append(_build_monom_term(-coeff, key))

    lhs = add_many(lhs_terms) if lhs_terms else Const(0)
    rhs = add_many(rhs_terms) if rhs_terms else Const(0)
    return Eq(lhs, rhs)


def compile_instance(
    k: int,
    w: int,
    base: int = 5,
    aggregation_mode: str = "hierarchical",
    aggregation_block_size: int = 32,
    aggregation_outer_base: int | None = None,
    public_var_map: Sequence[Tuple[str, str]] | None = None,
    reserve_public_slots: bool = False,
    allow_nonadjacent_digits: bool = False,
) -> CompileResult:
    if public_var_map is None:
        public_var_map = [("u", "trace_code")]

    n_lines = max(1, k)
    # Keep bounded and divisible by 4 for gap-4 pair lanes.
    digit_width = max(16, 4 * max(1, w))
    if digit_width % 4 != 0:
        digit_width += (4 - digit_width % 4)

    res = emit_cubic_system(
        n_lines=n_lines,
        digit_width=digit_width,
        allow_nonadjacent_digits=allow_nonadjacent_digits,
    )
    if not bool(res.get("has_degree_3_pre", False)):
        raise ValueError("pre-aggregation polynomial stage has no degree-3 activated constraints")
    if not bool(res.get("activated_selector_quadratic_exists", False)):
        raise ValueError("missing selector*quadratic activation in emitted constraints")
    constraints = res["constraints"]  # type: ignore[assignment]
    assert_equation_channels_well_formed(constraints)  # type: ignore[arg-type]

    U, caps = aggregate(
        constraints,  # type: ignore[arg-type]
        base=base,
        mode=aggregation_mode,
        block_size=aggregation_block_size,
        outer_base=aggregation_outer_base,
    )
    channel_count = len(constraints) + len(caps)  # type: ignore[arg-type]

    vars_list: List[str] = []
    _collect_vars(U, vars_list)
    var_order, public_var_indices = _resolve_var_order(
        vars_list,
        public_var_map,
        reserve_public_slots,
    )
    var_index = {v: i for i, v in enumerate(var_order)}

    mono_map = _monomials(U)
    max_total_degree = 0
    has_degree_3 = False
    count_degree_3 = 0
    for key in mono_map.keys():
        d = sum(e for _, e in key)
        if d > max_total_degree:
            max_total_degree = d
        if d == 3:
            has_degree_3 = True
            count_degree_3 += 1
    if max_total_degree > 3:
        raise ValueError(f"aggregated polynomial degree exceeds 3: {max_total_degree}")
    if not has_degree_3:
        raise ValueError("aggregated polynomial has no degree-3 monomial")

    monomials: List[Tuple[int, Tuple[Tuple[int, int], ...]]] = []
    max_digits = 0
    for key, coeff in mono_map.items():
        max_digits = max(max_digits, len(str(abs(coeff))))
        monomials.append((coeff, tuple((var_index[v], e) for v, e in key)))
    monomials.sort(key=lambda t: (len(t[1]), t[1], t[0]))

    payload = {
        "meta": {
            "base": base,
            "channel_count": channel_count,
            "aggregation_mode": aggregation_mode,
            "aggregation_block_size": aggregation_block_size if aggregation_mode == "hierarchical" else None,
            "aggregation_outer_base": (base + 2 if aggregation_outer_base is None else aggregation_outer_base)
            if aggregation_mode == "hierarchical"
            else None,
            "encoding": "zeckendorf",
            "pairing_layout": "gap4",
            "successor": "nat_plus_one_eq",
            "debug_nonadjacency_disabled": allow_nonadjacent_digits,
            "n_lines": n_lines,
            "digit_width": digit_width,
            "max_repr_lane": _max_zeck(digit_width // 4),
            "max_repr_full": _max_zeck(digit_width),
            "max_coeff_digits": max_digits,
            "max_degree": max_total_degree,
            "has_degree_3": has_degree_3,
            "count_degree_3_monomials": count_degree_3,
        },
        "vars": var_order,
        "monomials": [{"c": str(c), "m": [[str(v), e] for v, e in mons]} for c, mons in monomials],
    }

    data_bytes = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    digest = hashlib.sha256(data_bytes).hexdigest()
    json_size = len(data_bytes)

    return CompileResult(
        base=base,
        channel_count=channel_count,
        aggregation_mode=aggregation_mode,
        aggregation_block_size=aggregation_block_size if aggregation_mode == "hierarchical" else None,
        aggregation_outer_base=(
            (base + 2 if aggregation_outer_base is None else aggregation_outer_base)
            if aggregation_mode == "hierarchical"
            else None
        ),
        encoding="zeckendorf",
        pairing_layout="gap4",
        successor="nat_plus_one_eq",
        debug_nonadjacency_disabled=allow_nonadjacent_digits,
        n_lines=n_lines,
        digit_width=digit_width,
        max_repr_lane=_max_zeck(digit_width // 4),
        max_repr_full=_max_zeck(digit_width),
        max_degree=max_total_degree,
        has_degree_3=has_degree_3,
        count_degree_3_monomials=count_degree_3,
        monomials=monomials,
        var_order=var_order,
        public_vars=public_var_indices,
        max_coeff_digits=max_digits,
        hash=digest,
        json_size_bytes=json_size,
    )


def write_json(path: str, result: CompileResult) -> None:
    payload = {
        "meta": {
            "base": result.base,
            "channel_count": result.channel_count,
            "aggregation_mode": result.aggregation_mode,
            "aggregation_block_size": result.aggregation_block_size,
            "aggregation_outer_base": result.aggregation_outer_base,
            "encoding": result.encoding,
            "pairing_layout": result.pairing_layout,
            "successor": result.successor,
            "debug_nonadjacency_disabled": result.debug_nonadjacency_disabled,
            "n_lines": result.n_lines,
            "digit_width": result.digit_width,
            "max_repr_lane": result.max_repr_lane,
            "max_repr_full": result.max_repr_full,
            "max_coeff_digits": result.max_coeff_digits,
            "max_degree": result.max_degree,
            "has_degree_3": result.has_degree_3,
            "count_degree_3_monomials": result.count_degree_3_monomials,
            "public_vars": result.public_vars,
            "hash": result.hash,
        },
        "vars": result.var_order,
        "monomials": [{"c": str(c), "m": [[str(v), e] for v, e in mons]} for c, mons in result.monomials],
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)


def _canonical_payload(data: dict) -> dict:
    meta = data["meta"]
    return {
        "meta": {
            "base": int(meta["base"]),
            "channel_count": int(meta["channel_count"]),
            "aggregation_mode": meta.get("aggregation_mode"),
            "aggregation_block_size": meta.get("aggregation_block_size"),
            "aggregation_outer_base": meta.get("aggregation_outer_base"),
            "encoding": meta.get("encoding"),
            "pairing_layout": meta.get("pairing_layout"),
            "successor": meta.get("successor"),
            "debug_nonadjacency_disabled": bool(meta.get("debug_nonadjacency_disabled", False)),
            "n_lines": int(meta["n_lines"]),
            "digit_width": int(meta["digit_width"]),
            "max_repr_lane": int(meta["max_repr_lane"]),
            "max_repr_full": int(meta["max_repr_full"]),
            "max_coeff_digits": int(meta["max_coeff_digits"]),
            "max_degree": int(meta["max_degree"]),
            "has_degree_3": bool(meta["has_degree_3"]),
            "count_degree_3_monomials": int(meta["count_degree_3_monomials"]),
        },
        "vars": [str(v) for v in data["vars"]],
        "monomials": [
            {
                "c": str(m["c"]),
                "m": [[str(v), int(e)] for v, e in m["m"]],
            }
            for m in data["monomials"]
        ],
    }


def _canonical_sha256_hex(data: dict) -> str:
    payload = _canonical_payload(data)
    raw = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _coerce_public_indices(data: dict, lock: dict) -> Dict[str, int]:
    meta = data["meta"]
    vars_list = [str(v) for v in data["vars"]]
    if "public_vars" in meta:
        return {str(k): int(v) for k, v in meta["public_vars"].items()}

    source = {str(k): str(v) for k, v in lock.get("public_var_sources", {}).items()}
    out: Dict[str, int] = {}
    for public_name, var_name in source.items():
        if var_name in vars_list:
            out[public_name] = vars_list.index(var_name)
    if "u" not in out:
        raise ValueError("Could not resolve public var 'u' from JSON metadata or lock public_var_sources.")
    return out


def _verify_against_lock(data: dict, lock: dict) -> None:
    meta = data["meta"]
    expected = lock["expected"]
    checks = [
        ("encoding", meta.get("encoding"), expected["encoding"]),
        ("pairing_layout", meta.get("pairing_layout"), expected["pairing_layout"]),
        ("successor", meta.get("successor"), expected["successor"]),
        ("debug_nonadjacency_disabled", bool(meta.get("debug_nonadjacency_disabled", False)), bool(expected["debug_nonadjacency_disabled"])),
        ("n_lines", int(meta.get("n_lines")), int(expected["n_lines"])),
        ("digit_width", int(meta.get("digit_width")), int(expected["digit_width"])),
        ("max_repr_lane", int(meta.get("max_repr_lane")), int(expected["max_repr_lane"])),
        ("max_repr_full", int(meta.get("max_repr_full")), int(expected["max_repr_full"])),
        ("channel_count", int(meta.get("channel_count")), int(expected["channel_count"])),
        ("var_count", len(data["vars"]), int(expected["var_count"])),
        ("max_coeff_digits", int(meta.get("max_coeff_digits")), int(expected["max_coeff_digits"])),
        ("max_degree", int(meta.get("max_degree")), int(expected["max_degree"])),
        ("has_degree_3", bool(meta.get("has_degree_3")), bool(expected["has_degree_3"])),
        (
            "count_degree_3_monomials",
            int(meta.get("count_degree_3_monomials")),
            int(expected["count_degree_3_monomials"]),
        ),
    ]
    mismatches = [(k, got, want) for (k, got, want) in checks if got != want]
    if mismatches:
        lines = ["Lockfile mismatch detected:"]
        for k, got, want in mismatches:
            lines.append(f"  - {k}: got {got!r}, expected {want!r}")
        raise ValueError("\n".join(lines))

    if bool(meta.get("debug_nonadjacency_disabled", False)):
        raise ValueError("Pinned artifact verification rejects debug mode: meta.debug_nonadjacency_disabled must be false.")


def _write_coeff_types(dst: Path, data: dict, coeff_hash: str) -> None:
    vars_list = data["vars"]
    meta = data["meta"]
    with dst.open("w", encoding="utf-8") as f:
        f.write("From Coq Require Import ZArith List String.\n")
        f.write("Import ListNotations.\n")
        f.write("Open Scope Z_scope.\n")
        f.write("Open Scope string_scope.\n\n")
        f.write(f"Definition var_count : nat := {len(vars_list)}.\n")
        f.write(f"Definition base : Z := {meta['base']}.\n")
        f.write(f"Definition channel_count : nat := {meta['channel_count']}.\n")
        f.write(f"Definition bound_n_lines : nat := {meta['n_lines']}.\n")
        f.write(f"Definition bound_digit_width : nat := {meta['digit_width']}.\n")
        f.write(f"Definition bound_max_repr_lane : nat := {meta['max_repr_lane']}.\n")
        f.write(f"Definition bound_max_repr_full : nat := {meta['max_repr_full']}.\n")
        f.write(f"Definition expected_max_degree : nat := {meta['max_degree']}.\n")
        f.write(
            "Definition expected_has_degree_3 : bool := "
            + ("true" if bool(meta.get("has_degree_3", False)) else "false")
            + ".\n"
        )
        f.write(f"Definition expected_count_degree_3_monomials : nat := {meta['count_degree_3_monomials']}.\n")
        f.write(f"Definition encoding_scheme : string := \"{meta.get('encoding', 'unknown')}\".\n")
        f.write(f"Definition pairing_layout : string := \"{meta.get('pairing_layout', 'unknown')}\".\n")
        f.write(f"Definition successor_scheme : string := \"{meta.get('successor', 'unknown')}\".\n")
        f.write(
            "Definition debug_nonadjacency_disabled : bool := "
            + ("true" if bool(meta.get("debug_nonadjacency_disabled", False)) else "false")
            + ".\n"
        )
        f.write(f"Definition max_coeff_digits : nat := {meta['max_coeff_digits']}.\n")
        f.write(f"Definition coeff_hash : string := \"{coeff_hash}\".\n\n")
        f.write("Record monom := { coeff : Z; exps : list (nat * nat) }.\n")


def _chunked(xs: List[dict], size: int) -> Iterable[List[dict]]:
    for i in range(0, len(xs), size):
        yield xs[i : i + size]


def _write_chunks(chunks_dir: Path, monomials: List[dict], chunk_count: int) -> int:
    if chunk_count <= 0:
        raise ValueError("chunk_count must be positive")
    chunk_size = max(1, (len(monomials) + chunk_count - 1) // chunk_count)
    chunks = list(_chunked(monomials, chunk_size))
    chunks_dir.mkdir(parents=True, exist_ok=True)

    for old in chunks_dir.glob("Coeff_chunk_*.v"):
        old.unlink()

    for idx, chunk in enumerate(chunks):
        with (chunks_dir / f"Coeff_chunk_{idx}.v").open("w", encoding="utf-8") as f:
            f.write("From Coq Require Import ZArith List String.\n")
            f.write("Import ListNotations.\n")
            f.write("Open Scope Z_scope.\n\n")
            f.write("From T003 Require Import R01__Coeff_types.\n\n")
            f.write(f"Definition poly_chunk_{idx} : list monom := [\n")
            for i, m in enumerate(chunk):
                coeff = str(m["c"])
                monoms = [[str(v), int(e)] for v, e in m["m"]]
                exps = "; ".join([f"({v}%nat, {e}%nat)" for v, e in monoms])
                sep = ";" if i + 1 < len(chunk) else ""
                f.write(f"  {{| coeff := {coeff} ; exps := [{exps}] |}}{sep}\n")
            f.write("].\n")

    return len(chunks)


def _write_coefficients(dst: Path, chunk_count: int) -> None:
    with dst.open("w", encoding="utf-8") as f:
        f.write("From Coq Require Import ZArith List String.\n")
        f.write("Import ListNotations.\n")
        f.write("Open Scope Z_scope.\n")
        f.write("Open Scope string_scope.\n\n")
        f.write("From T003 Require Import R01__Coeff_types.\n")
        for idx in range(chunk_count):
            f.write(f"From T003.Chunks Require Import Coeff_chunk_{idx}.\n")
        concat = " ++ ".join([f"poly_chunk_{i}" for i in range(chunk_count)]) or "[]"
        f.write(f"\nDefinition poly : list monom := {concat}.\n\n")
        f.write("Definition eval_monom (rho : nat -> Z) (m : monom) : Z :=\n")
        f.write("  m.(coeff)\n")
        f.write("  * fold_left\n")
        f.write("      (fun acc ve =>\n")
        f.write("         let '(v, e) := ve in acc * (rho v) ^ (Z.of_nat e))\n")
        f.write("      m.(exps) 1.\n")
        f.write("Definition U (rho : nat -> Z) : Z := fold_left (fun acc m => acc + eval_monom rho m) poly 0.\n")


def _write_varmap(dst: Path, data: dict, public_indices: Dict[str, int], lock: dict) -> None:
    source = {str(k): str(v) for k, v in lock.get("public_var_sources", {}).items()}
    with dst.open("w", encoding="utf-8") as f:
        f.write("From Coq Require Import ZArith List String Lia Arith.\n")
        f.write("Import ListNotations.\n")
        f.write("Open Scope Z_scope.\n")
        f.write("Open Scope string_scope.\n\n")
        f.write("From T003 Require Import R01__Coeff_types.\n\n")
        f.write("(* Auto-generated public variable map for the pinned bounded cubic artifact. *)\n\n")
        for public_name in sorted(public_indices.keys()):
            idx = int(public_indices[public_name])
            src_name = source.get(public_name, public_name)
            f.write(f"Definition ix_{public_name} : nat := {idx}.\n")
            f.write(f"Definition var_{public_name} : string := \"{src_name}\".\n")
            f.write(f"Lemma ix_{public_name}_lt_var_count : (ix_{public_name} < var_count)%nat.\n")
            f.write("Proof.\n")
            f.write("  apply Nat.ltb_lt.\n")
            f.write("  vm_compute.\n")
            f.write("  reflexivity.\n")
            f.write("Qed.\n\n")
        pairs = "; ".join([f"(\"{k}\", ix_{k})" for k in sorted(public_indices.keys())])
        f.write(f"Definition public_var_indices : list (string * nat) := [{pairs}].\n")


DIGEST_MODULUS = 2305843009213693951  # 2^61 - 1
DIGEST_MUL_EXPS_RAW = 65537
DIGEST_MUL_MONOM_RAW = 11400714819323198485
DIGEST_MUL_TABLE_RAW = 1469598103934665603


def _digest_constants() -> Tuple[int, int, int, int]:
    mod = DIGEST_MODULUS
    mul_exps = DIGEST_MUL_EXPS_RAW % mod
    mul_monom = DIGEST_MUL_MONOM_RAW % mod
    mul_table = DIGEST_MUL_TABLE_RAW % mod
    return mod, mul_exps, mul_monom, mul_table


def _compute_table_digest(monomials: List[dict]) -> int:
    mod, mul_exps, mul_monom, mul_table = _digest_constants()

    def encode_ve(v: str, e: int) -> int:
        return (int(v) * 131 + int(e) + 1) % mod

    def encode_exps(xs: List[List[object]]) -> int:
        acc = 0
        for v, e in xs:
            acc = (acc * mul_exps + encode_ve(str(v), int(e))) % mod
        return acc

    def encode_monom(m: dict) -> int:
        coeff = int(m["c"]) % mod
        return (coeff * mul_monom + encode_exps(m["m"])) % mod

    acc = 0
    for m in monomials:
        acc = (acc * mul_table + encode_monom(m)) % mod
    return acc


def _write_table_inspection(dst: Path, digest_value: int) -> None:
    mod, mul_exps, mul_monom, mul_table = _digest_constants()
    with dst.open("w", encoding="utf-8") as f:
        f.write("(* R07__Table_Inspection.v *)\n")
        f.write("(* Mandatory table-inspection gate for the pinned coefficient list. *)\n\n")
        f.write("From Coq Require Import ZArith List.\n")
        f.write("Import ListNotations.\n")
        f.write("Open Scope Z_scope.\n\n")
        f.write("From T003 Require Import R01__Coeff_types R02__Coefficients.\n\n")
        f.write(f"Definition digest_modulus : Z := {mod}.\n")
        f.write(f"Definition digest_mul_exps : Z := {mul_exps}.\n")
        f.write(f"Definition digest_mul_monom : Z := {mul_monom}.\n")
        f.write(f"Definition digest_mul_table : Z := {mul_table}.\n\n")
        f.write("(*\n")
        f.write("  Digest is intentionally representation-sensitive over the raw `poly`\n")
        f.write("  monomial list (including monomial order and exponent-list order).\n")
        f.write("*)\n")
        f.write("Definition encode_ve (ve : nat * nat) : Z :=\n")
        f.write("  let '(v, e) := ve in\n")
        f.write("  (Z.of_nat v * 131 + Z.of_nat e + 1) mod digest_modulus.\n\n")
        f.write("Definition encode_exps (xs : list (nat * nat)) : Z :=\n")
        f.write("  fold_left\n")
        f.write("    (fun acc ve => (acc * digest_mul_exps + encode_ve ve) mod digest_modulus)\n")
        f.write("    xs 0.\n\n")
        f.write("Definition encode_monom (m : monom) : Z :=\n")
        f.write("  ((m.(coeff) mod digest_modulus) * digest_mul_monom + encode_exps m.(exps))\n")
        f.write("  mod digest_modulus.\n\n")
        f.write("Definition digest_step (acc : Z) (m : monom) : Z :=\n")
        f.write("  (acc * digest_mul_table + encode_monom m) mod digest_modulus.\n\n")
        f.write("Definition table_digest_of (p : list monom) : Z := fold_left digest_step p 0.\n")
        f.write("Definition table_digest : Z := table_digest_of poly.\n")
        f.write("(* Generated by theories/T003/python/gen.py from the pinned JSON artifact. *)\n")
        f.write(f"Definition table_digest_expected : Z := {digest_value}.\n\n")
        f.write("Theorem table_digest_ok : table_digest = table_digest_expected.\n")
        f.write("Proof.\n")
        f.write("  vm_compute.\n")
        f.write("  reflexivity.\n")
        f.write("Qed.\n")


def _write_yaml(dst: Path, data: dict, public_indices: Dict[str, int], canonical_hash: str) -> None:
    meta = data["meta"]
    lines = [
        "bounded_cubic:",
        '  title: "Bounded universal cubic artifact"',
        "  source: \"theories/T003\"",
        "  theorem_endpoint:",
        "    module: \"R08__Bounded_Universality\"",
        "    definition: \"R08__Bounded_Universality.bounded_universal_cubic\"",
        "    equation: \"Bounded_Thm_k t <-> exists rho, InputEncoding_table t rho /\\ RepresentationBound rho /\\ U_table rho = 0\"",
        "  artifact:",
        f"    sha256_canonical_json: \"{canonical_hash}\"",
        f"    var_count: {len(data['vars'])}",
        f"    channel_count: {int(meta['channel_count'])}",
        f"    max_coeff_digits: {int(meta['max_coeff_digits'])}",
        f"    max_degree: {int(meta['max_degree'])}",
        f"    has_degree_3: {str(bool(meta['has_degree_3'])).lower()}",
        f"    count_degree_3_monomials: {int(meta['count_degree_3_monomials'])}",
        "  semantics:",
        f"    encoding: \"{meta.get('encoding', 'unknown')}\"",
        f"    pairing_layout: \"{meta.get('pairing_layout', 'unknown')}\"",
        f"    successor: \"{meta.get('successor', 'unknown')}\"",
        f"    debug_nonadjacency_disabled: {str(bool(meta.get('debug_nonadjacency_disabled', False))).lower()}",
        f"    n_lines: {int(meta['n_lines'])}",
        f"    digit_width: {int(meta['digit_width'])}",
        f"    max_repr_lane: {int(meta['max_repr_lane'])}",
        f"    max_repr_full: {int(meta['max_repr_full'])}",
        "  public_vars:",
    ]
    for k in sorted(public_indices.keys()):
        lines.append(f"    {k}: {int(public_indices[k])}")
    lines.append("")
    dst.write_text("\n".join(lines), encoding="utf-8")


def emit_t003_from_lock(chunk_count: int = 20) -> None:
    script = Path(__file__).resolve()
    t003_root = script.parents[2]
    artifacts_dir = t003_root / "artifacts"
    lock_path = artifacts_dir / "universal_cubic.lock.json"
    json_path = artifacts_dir / "universal_cubic.coefficients.json"

    lock = json.loads(lock_path.read_text(encoding="utf-8"))
    run_self_checks()
    run_contract_suite()

    if lock.get("expected", {}).get("debug_nonadjacency_disabled", False):
        raise ValueError("Pinned lock requests debug_nonadjacency_disabled=true; forbidden for release artifacts.")

    agg = lock["aggregation"]
    inst = lock["instance"]
    public_sources = lock.get("public_var_sources", {"u": "trace_code"})
    public_var_map = [(str(k), str(v)) for k, v in public_sources.items()]

    res = compile_instance(
        int(inst["k"]),
        int(inst["w"]),
        base=int(agg["base"]),
        aggregation_mode=str(agg["mode"]),
        aggregation_block_size=int(agg["block_size"]),
        aggregation_outer_base=int(agg["outer_base"]),
        public_var_map=public_var_map,
        reserve_public_slots=bool(lock.get("reserve_public_slots", False)),
        allow_nonadjacent_digits=False,
    )
    write_json(str(json_path), res)

    data = json.loads(json_path.read_text(encoding="utf-8"))
    canonical_hash = _canonical_sha256_hex(data)
    _verify_against_lock(data, lock)
    public_indices = _coerce_public_indices(data, lock)

    _write_coeff_types(t003_root / "R01__Coeff_types.v", data, canonical_hash)
    produced_chunks = _write_chunks(t003_root / "Chunks", data["monomials"], chunk_count)
    _write_coefficients(t003_root / "R02__Coefficients.v", produced_chunks)
    _write_varmap(t003_root / "R00__VarMap.v", data, public_indices, lock)
    table_digest = _compute_table_digest(data["monomials"])
    _write_table_inspection(t003_root / "R07__Table_Inspection.v", table_digest)
    _write_yaml(artifacts_dir / "universal_cubic.yaml", data, public_indices, canonical_hash)

    print("self_check=ok")
    print("contract_check=ok")
    print(f"computed_sha256(canonical_json)={canonical_hash}")
    print(f"public_vars={public_indices}")
    print(f"wrote: {json_path}")
    print(f"wrote: {t003_root / 'R00__VarMap.v'}")
    print(f"wrote: {t003_root / 'R01__Coeff_types.v'}")
    print(f"wrote: {t003_root / 'R02__Coefficients.v'}")
    print(f"wrote: {t003_root / 'R07__Table_Inspection.v'}")
    print(f"table_digest_expected={table_digest}")
    print(f"wrote chunks: {produced_chunks}")

# Semantic self-checks

def run_self_checks() -> None:
    def _collect_digit_vectors(env: Dict[str, int]) -> Dict[tuple[str, int], List[int]]:
        out: Dict[tuple[str, int], Dict[int, int]] = {}
        for name, value in env.items():
            if not name.startswith("d_"):
                continue
            try:
                rest = name[2:]
                var_name, width_s, idx_s = rest.rsplit("_", 2)
                width = int(width_s)
                idx = int(idx_s)
            except Exception as ex:
                raise AssertionError(f"malformed digit variable name: {name}") from ex
            key = (var_name, width)
            if key not in out:
                out[key] = {}
            out[key][idx] = int(value)
        vecs: Dict[tuple[str, int], List[int]] = {}
        for key, indexed in out.items():
            width = key[1]
            ds = [indexed.get(i, 0) for i in range(width)]
            vecs[key] = ds
        return vecs

    def _assert_pair_roundtrip_constraints() -> None:
        rng = random.Random(0)
        width = 64
        lane = width // 4
        cap = _max_zeck(lane)
        for _ in range(24):
            x = rng.randint(0, min(cap, 400))
            y = rng.randint(0, min(cap, 400))
            z = pair_value(x, y, width)
            ux, uy = unpair_value(z, width)
            if (ux, uy) != (x, y):
                raise AssertionError(f"pair/unpair roundtrip failed: {(x, y)} -> {z} -> {(ux, uy)}")

            cc = ConstraintCompiler(n_lines=1, digit_width=width)
            x_v = Var("pair_x")
            y_v = Var("pair_y")
            z_v = Var("pair_z")
            rel = cc._pair_relation(z_v, x_v, y_v, width)
            eqs = list(cc.equations) + rel
            env: Dict[str, int] = {nm: 0 for nm in _collect_equation_vars(eqs)}
            _set_var(env, "pair_x", x)
            _set_var(env, "pair_y", y)
            _set_var(env, "pair_z", z)
            for (var_name, repr_width), _ in cc._repr_cache.items():
                val = env[var_name]
                ds = zeck_encode(val, repr_width)
                if not zeck_is_admissible(ds):
                    raise AssertionError(f"nonadmissible pair digits for {var_name}/{repr_width}")
                for i, d in enumerate(ds):
                    _set_var(env, f"d_{var_name}_{repr_width}_{i}", d)
            bad = check_equations(eqs, env)
            if bad:
                i, lv, rv = bad[0]
                raise AssertionError(f"pair constraints failed at eq#{i}: {lv}!={rv}")

    def _assert_ambiguous_parse_sentinel_unsat() -> None:
        width = 64
        dz = [0] * width
        dz[1] = 1  # admissible Zeck vector, but invalid for gap-4 pair image (slot 1 must be 0).
        if not zeck_is_admissible(dz):
            raise AssertionError("sentinel digits are unexpectedly inadmissible")
        z = zeck_decode(dz)
        x, y = unpair_value(z, width)

        cc = ConstraintCompiler(n_lines=1, digit_width=width)
        x_v = Var("amb_x")
        y_v = Var("amb_y")
        z_v = Var("amb_z")
        rel = cc._pair_relation(z_v, x_v, y_v, width)
        eqs = list(cc.equations) + rel

        env: Dict[str, int] = {nm: 0 for nm in _collect_equation_vars(eqs)}
        _set_var(env, "amb_x", x)
        _set_var(env, "amb_y", y)
        _set_var(env, "amb_z", z)
        for (var_name, repr_width), _ in cc._repr_cache.items():
            val = env[var_name]
            ds = zeck_encode(val, repr_width)
            for i, d in enumerate(ds):
                _set_var(env, f"d_{var_name}_{repr_width}_{i}", d)

        bad = check_equations(eqs, env)
        if not bad:
            raise AssertionError("ambiguous parse sentinel unexpectedly satisfied pair constraints")

    def _assert_bounds_not_porous() -> None:
        # Width edge case at pinned bounded parameters.
        A = Imp(BOT, BOT)
        edge_width = 16
        env_edge = build_witness([A], A, edge_width)
        eqs_edge = emit_cubic_system(1, edge_width)["constraints"]  # type: ignore[index]
        bad_edge = check_equations(eqs_edge, env_edge)  # type: ignore[arg-type]
        if bad_edge:
            i, lv, rv = bad_edge[0]
            raise AssertionError(f"edge-width witness failed at eq#{i}: {lv}!={rv}")

        # Over-bound proof length sentinel: a proof_code with 3 lines cannot satisfy
        # the exact-length-2 tail condition under the natural decoding assignment.
        k_line = Imp(A, Imp(BOT, A))
        mp_goal = Imp(BOT, A)
        pf_long = [A, k_line, mp_goal]
        if not check_proof(pf_long, mp_goal):
            raise AssertionError("internal test setup error: long proof should be valid")
        width = 652  # representable width for this test instance under current encoding.
        p_long = code_pf(pf_long, width)
        remainder = p_long
        for _ in range(2):
            pred = remainder - 1
            if pred < 0:
                raise AssertionError("unexpected negative predecessor in over-bound test")
            _head, remainder = unpair_value(pred, width)
        if remainder == 0:
            raise AssertionError("over-bound sentinel failed: expected nonzero tail after 2 extractions")

    # Boolean reflection sanity: over N, b=b^2 has only 0/1 solutions.
    for b in range(10):
        if (b == b * b) != (b in (0, 1)):
            raise AssertionError("boolean reflection sanity check failed")

    _assert_pair_roundtrip_constraints()
    _assert_ambiguous_parse_sentinel_unsat()
    _assert_bounds_not_porous()

    A = Imp(BOT, BOT)
    k_line = Imp(A, Imp(BOT, A))
    mp_goal = Imp(BOT, A)
    s_line = Imp(Imp(A, Imp(BOT, BOT)), Imp(Imp(A, BOT), Imp(A, BOT)))

    valid: List[tuple[List[Form], Form]] = [
        ([A], A),
        ([s_line], s_line),
        ([A, k_line, mp_goal], mp_goal),
    ]
    invalid: List[tuple[List[Form], Form]] = [
        ([A, k_line, BOT], BOT),
        ([A, k_line, mp_goal], BOT),
        ([A, k_line, Imp(A, A)], Imp(A, A)),
    ]

    for idx, (pf, goal) in enumerate(valid):
        if not check_proof(pf, goal):
            raise AssertionError(f"valid proof unexpectedly rejected (case {idx})")
        width = _min_width_for_instance(pf, goal)
        env = build_witness(pf, goal, width)
        cc = ConstraintCompiler(n_lines=len(pf), digit_width=width)
        eqs = cc.emit()
        bad = check_equations(eqs, env)  # type: ignore[arg-type]
        if bad:
            i, lv, rv = bad[0]
            raise AssertionError(f"witness failed for valid case {idx} at eq#{i}: {lv}!={rv}")

        # Structural checks: admissible digits, functional pair decoding, exact proof-list decoding.
        digit_vectors = _collect_digit_vectors(env)
        for (var_name, repr_width), ds in digit_vectors.items():
            if not zeck_is_admissible(ds):
                raise AssertionError(f"nonadmissible Zeckendorf digits in witness: {var_name}/{repr_width}")

        for z_name, x_name, y_name, repr_width in sorted(set(cc.pair_links)):
            ux, uy = unpair_value(env[z_name], repr_width)
            if ux != env[x_name] or uy != env[y_name]:
                raise AssertionError(
                    f"pair-link projection mismatch for {z_name} -> ({x_name},{y_name}) at width {repr_width}"
                )

        expected_codes = [enc_form(phi, width) for phi in pf]
        decoded_codes = decode_list(env["proof_code"], width, fuel=len(expected_codes) + 4)
        if decoded_codes != expected_codes:
            raise AssertionError(f"proof_code decoding mismatch: got {decoded_codes}, expected {expected_codes}")

        # Target mutation test.
        env_target_bad = dict(env)
        env_target_bad["goal_code"] = env_target_bad["goal_code"] + 1
        if not check_equations(eqs, env_target_bad):
            raise AssertionError(f"target mutation did not break constraints (case {idx})")

        # Mutation test: break branch selector coherence.
        env_bad = dict(env)
        env_bad["a_0"] = 1 - env_bad.get("a_0", 0)
        if not check_equations(eqs, env_bad):  # type: ignore[arg-type]
            raise AssertionError(f"mutation did not break constraints (case {idx})")

        # MP witness mutation (only applicable when an MP line exists).
        for i in range(1, len(pf)):
            if env.get(f"m_{i}", 0) != 1:
                continue
            env_mp_bad = dict(env)
            for j in range(i):
                for k in range(i):
                    env_mp_bad[f"mp_{i}_{j}_{k}"] = 0
            if not check_equations(eqs, env_mp_bad):
                raise AssertionError(f"MP witness mutation did not break constraints (case {idx}, line {i})")

    for idx, (pf, goal) in enumerate(invalid):
        if check_proof(pf, goal):
            raise AssertionError(f"invalid proof unexpectedly accepted (case {idx})")


def run_contract_suite() -> None:
    """
    Artifact-release contract tests for the bounded checker pipeline.
    """
    A = Imp(BOT, BOT)  # EFQ instance: Bot -> Bot
    valid_cases: List[tuple[List[Form], Form]] = [([A], A)]

    for idx, (pf, goal) in enumerate(valid_cases):
        width = 16  # pinned artifact width for (k=3, w=4)
        if _min_width_for_instance(pf, goal, start=width, limit=width) != width:
            raise AssertionError("contract case is not representable at pinned width")
        if not check_proof(pf, goal):
            raise AssertionError(f"contract valid case rejected semantically (case {idx})")

        env = build_witness(pf, goal, width, validate=True)
        emitted = emit_cubic_system(len(pf), width)
        if not bool(emitted.get("has_degree_3_pre", False)):
            raise AssertionError("contract failure: pre-aggregation stage has no degree-3 constraints")
        if not bool(emitted.get("activated_selector_quadratic_exists", False)):
            raise AssertionError("contract failure: missing selector*quadratic activation")
        eqs = emitted["constraints"]  # type: ignore[index]
        bad = check_equations(eqs, env)  # type: ignore[arg-type]
        if bad:
            i, lv, rv = bad[0]
            raise AssertionError(f"contract pre-aggregation failure at eq#{i}: {lv}!={rv}")

        # Weighted aggregation identity for the equation channels (without capacity channels).
        weights = _hierarchical_weights(len(eqs), inner_base=5, outer_base=7, block_size=32)
        left_terms: List[Tuple[int, BaseExpr]] = []
        right_terms: List[Tuple[int, BaseExpr]] = []
        for wgt, e in zip(weights, eqs):
            left_terms.append((wgt, e.lhs))
            right_terms.append((wgt, e.rhs))
        U_raw = Sub(linear_combination(left_terms), linear_combination(right_terms))
        if eval_expr(U_raw, env) != 0:
            raise AssertionError("contract weighted channel aggregation does not vanish on constructed witness")

        # Decode from witness-carried codes and re-check.
        pf_codes = decode_list(env["proof_code"], width, fuel=len(pf) + 2)
        if len(pf_codes) != len(pf):
            raise AssertionError("decoded proof length mismatch in contract test")
        pf_decoded = [decode_form(code, width, fuel=width) for code in pf_codes]
        goal_decoded = decode_form(env["goal_code"], width, fuel=width)
        if pf_decoded != pf or goal_decoded != goal:
            raise AssertionError("decoded witness proof/goal mismatch in contract test")
        if not check_proof(pf_decoded, goal_decoded):
            raise AssertionError("decoded witness proof fails semantic checker in contract test")

        # Tightness mutations under the structured witness.
        env_target_bad = dict(env)
        env_target_bad["goal_code"] = env_target_bad["goal_code"] + 1
        if not check_equations(eqs, env_target_bad):  # type: ignore[arg-type]
            raise AssertionError("target-mismatch mutation did not break contract satisfiability")

        env_selector_bad = dict(env)
        env_selector_bad["a_0"] = 0
        env_selector_bad["m_0"] = 1
        if not check_equations(eqs, env_selector_bad):  # type: ignore[arg-type]
            raise AssertionError("selector-mismatch mutation did not break contract satisfiability")

        digit_key = f"d_proof_code_{width}_0"
        if digit_key in env:
            env_digit_bad = dict(env)
            env_digit_bad[digit_key] = 2  # violates boolean digit constraint
            if not check_equations(eqs, env_digit_bad):  # type: ignore[arg-type]
                raise AssertionError("nonadmissible-digit mutation did not break contract satisfiability")

# CLI

def _parse_k_values(spec: str) -> List[int]:
    out: List[int] = []
    for tok in spec.split(","):
        tok = tok.strip()
        if not tok:
            continue
        k = int(tok)
        if k <= 0:
            raise ValueError(f"invalid k in scaling list: {k}")
        out.append(k)
    if not out:
        raise ValueError("scaling k list must be non-empty")
    return out


def run_scaling_report(
    ks: Sequence[int],
    w: int,
    base: int,
    mode: str,
    block_size: int,
    outer_base: int | None,
    public_var_map: Sequence[Tuple[str, str]],
    reserve_public_slots: bool,
) -> None:
    print("k,runtime_sec,channel_count,var_count,monomial_count,max_coeff_digits,n_lines,digit_width")
    for k in ks:
        t0 = time.perf_counter()
        res = compile_instance(
            k,
            w,
            base=base,
            aggregation_mode=mode,
            aggregation_block_size=block_size,
            aggregation_outer_base=outer_base if mode == "hierarchical" else None,
            public_var_map=public_var_map,
            reserve_public_slots=reserve_public_slots,
            allow_nonadjacent_digits=False,
        )
        dt = time.perf_counter() - t0
        print(
            f"{k},{dt:.6f},{res.channel_count},{len(res.var_order)},"
            f"{len(res.monomials)},{res.max_coeff_digits},{res.n_lines},{res.digit_width}"
        )


def main() -> None:
    ap = argparse.ArgumentParser(description="Build cubic universal coefficient JSON (single-file).")
    ap.add_argument(
        "--emit-t003",
        action="store_true",
        help="Regenerate pinned T003 artifact files from lockfile (JSON, Chunks, Coq files, YAML).",
    )
    ap.add_argument(
        "--chunk-count",
        type=int,
        default=20,
        help="Chunk count used by --emit-t003 when writing Chunks/Coeff_chunk_*.v.",
    )
    ap.add_argument("--k", type=int, default=3, help="Proof-length bound n.")
    ap.add_argument("--w", type=int, default=4, help="Digit-width control parameter.")
    ap.add_argument("--base", type=int, default=5, help="Radix base used in aggregation (default: 5).")
    ap.add_argument("--mode", choices=["legacy", "hierarchical"], default="hierarchical")
    ap.add_argument("--block-size", type=int, default=32)
    ap.add_argument("--outer-base", type=int, default=None)
    ap.add_argument("--self-check", action="store_true", help="Run semantic self-checks and exit.")
    ap.add_argument("--contract-check", action="store_true", help="Run bounded contract test suite and exit.")
    ap.add_argument("--scaling-report", action="store_true", help="Print scaling metrics and exit.")
    ap.add_argument(
        "--scaling-k-values",
        type=str,
        default="1,2,3",
        help='Comma-separated k values for --scaling-report (e.g. "1,2,3").',
    )
    ap.add_argument(
        "--debug-allow-nonadjacent-digits",
        action="store_true",
        help="Debug only: disable Zeckendorf nonadjacency constraints in generated system.",
    )
    ap.add_argument(
        "--public-vars",
        type=str,
        default="u:trace_code",
        help='Comma-separated public var mapping (e.g. "u:trace_code,c,d").',
    )
    ap.add_argument(
        "--reserve-public-slots",
        action="store_true",
        help="Put public vars first in vars[]; reserves indices even if some are unused.",
    )
    ap.add_argument("--out", type=str, default="coefficients.json", help="Output JSON path.")
    args = ap.parse_args()

    if args.emit_t003:
        emit_t003_from_lock(chunk_count=args.chunk_count)
        return

    if args.self_check:
        run_self_checks()
        print("self_check=ok")
        return
    if args.contract_check:
        run_contract_suite()
        print("contract_check=ok")
        return

    public_var_map = _parse_public_vars(args.public_vars)

    if args.scaling_report:
        ks = _parse_k_values(args.scaling_k_values)
        run_scaling_report(
            ks=ks,
            w=args.w,
            base=args.base,
            mode=args.mode,
            block_size=args.block_size,
            outer_base=args.outer_base,
            public_var_map=public_var_map,
            reserve_public_slots=args.reserve_public_slots,
        )
        return

    res = compile_instance(
        args.k,
        args.w,
        base=args.base,
        aggregation_mode=args.mode,
        aggregation_block_size=args.block_size,
        aggregation_outer_base=args.outer_base if args.mode == "hierarchical" else None,
        public_var_map=public_var_map,
        reserve_public_slots=args.reserve_public_slots,
        allow_nonadjacent_digits=args.debug_allow_nonadjacent_digits,
    )
    write_json(args.out, res)

    print(f"Wrote: {args.out}")
    print(f"base={res.base} mode={res.aggregation_mode} channels={res.channel_count} vars={len(res.var_order)}")
    print(f"n_lines={res.n_lines} digit_width={res.digit_width}")
    print(f"monomials={len(res.monomials)} max_coeff_digits={res.max_coeff_digits}")
    print(f"public_vars={res.public_vars}")
    print(f"sha256(canonical_json)={res.hash}")
    print(f"json_size_bytes={res.json_size_bytes}")


if __name__ == "__main__":
    main()
