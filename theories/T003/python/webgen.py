#!/usr/bin/env python3
"""
webgen.py

Web artifact serializer for T003 coefficient tables.

Purpose:
- Keep `gen.py` as the canonical mathematical/compiler source.
- Keep Rocq ingestion on canonical JSON unchanged.
- Emit a separate compact web JSON (and optional JS payload) for site/runtime use.

This tool does not change arithmetic content. It only changes serialization.
"""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
from typing import Any, Dict, List


def _load_json(path: Path) -> Dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("Input JSON must be an object.")
    if "meta" not in raw or "vars" not in raw or "monomials" not in raw:
        raise ValueError("Input JSON must contain keys: meta, vars, monomials.")
    if not isinstance(raw["meta"], dict):
        raise ValueError("meta must be an object.")
    if not isinstance(raw["vars"], list):
        raise ValueError("vars must be an array.")
    if not isinstance(raw["monomials"], list):
        raise ValueError("monomials must be an array.")
    return raw


def _compact_monomials(monomials: List[Dict[str, Any]]) -> List[List[Any]]:
    """
    Transform canonical monomial objects
      {"c":"...", "m":[["v","e"], ...]}
    into compact tuples
      ["...", [v0,e0,v1,e1,...]]
    """
    out: List[List[Any]] = []
    for i, m in enumerate(monomials):
        if not isinstance(m, dict):
            raise ValueError(f"Invalid monomial at index {i}: expected object.")
        if "c" not in m or "m" not in m:
            raise ValueError(f"Invalid monomial at index {i}: missing c/m.")
        coeff = str(m["c"])
        exps = m["m"]
        if not isinstance(exps, list):
            raise ValueError(f"Invalid monomial at index {i}: m must be array.")
        flat: List[int] = []
        for j, ve in enumerate(exps):
            if not isinstance(ve, list) or len(ve) != 2:
                raise ValueError(f"Invalid exponent entry at monomial {i}, entry {j}.")
            v = int(str(ve[0]))
            e = int(str(ve[1]))
            if v < 0 or e < 0:
                raise ValueError(f"Invalid negative exponent/index at monomial {i}, entry {j}.")
            flat.append(v)
            flat.append(e)
        out.append([coeff, flat])
    return out


def _make_web_payload(src: Dict[str, Any], keep_vars: bool) -> Dict[str, Any]:
    meta = dict(src["meta"])
    vars_list = [str(v) for v in src["vars"]]
    monoms = _compact_monomials(src["monomials"])

    out_meta = {
        "format": "cubic_web_compact_v1",
        "source_format": "t003_coefficients_v1",
        "base": meta.get("base"),
        "channel_count": meta.get("channel_count"),
        "aggregation_mode": meta.get("aggregation_mode"),
        "aggregation_block_size": meta.get("aggregation_block_size"),
        "aggregation_outer_base": meta.get("aggregation_outer_base"),
        "encoding": meta.get("encoding"),
        "pairing_layout": meta.get("pairing_layout"),
        "successor": meta.get("successor"),
        "debug_nonadjacency_disabled": bool(meta.get("debug_nonadjacency_disabled", False)),
        "n_lines": meta.get("n_lines"),
        "digit_width": meta.get("digit_width"),
        "max_repr_lane": meta.get("max_repr_lane"),
        "max_repr_full": meta.get("max_repr_full"),
        "max_coeff_digits": meta.get("max_coeff_digits"),
        "max_degree": meta.get("max_degree"),
        "has_degree_3": meta.get("has_degree_3"),
        "count_degree_3_monomials": meta.get("count_degree_3_monomials"),
        "public_vars": meta.get("public_vars", {}),
        "hash": meta.get("hash"),
        "var_count": len(vars_list),
        "monomial_count": len(monoms),
    }

    payload: Dict[str, Any] = {
        "meta": out_meta,
        "monomials": monoms,
    }
    if keep_vars:
        payload["vars"] = vars_list
    return payload


def _write_json(path: Path, payload: Dict[str, Any], pretty: bool) -> None:
    if pretty:
        text = json.dumps(payload, ensure_ascii=True, indent=2)
    else:
        text = json.dumps(payload, ensure_ascii=True, separators=(",", ":"))
    path.write_text(text + ("\n" if pretty else ""), encoding="utf-8")


def _write_js(path: Path, payload: Dict[str, Any], global_name: str) -> None:
    if not global_name.isidentifier():
        raise ValueError(f"Invalid JS global name: {global_name!r}")
    raw = json.dumps(payload, ensure_ascii=True, separators=(",", ":"))
    text = f"window.{global_name}={raw};\n"
    path.write_text(text, encoding="utf-8")


def _group_digits(n: int) -> str:
    """
    Format integer with thin-space-like HTML separators (NARROW NO-BREAK SPACE entity).
    """
    s = str(abs(n))
    groups: List[str] = []
    while s:
        groups.append(s[-3:])
        s = s[:-3]
    groups.reverse()
    return "&#8239;".join(groups) if groups else "0"


def _render_monom_term(mon: Dict[str, Any]) -> tuple[int, str]:
    coeff = int(str(mon["c"]))
    exps = mon["m"]
    coeff_html = _group_digits(coeff)
    factors: List[str] = []
    for ve in exps:
        v = int(str(ve[0]))
        e = int(str(ve[1]))
        if e <= 0:
            continue
        if e == 1:
            factors.append(f'x<span class="idx">{v}</span>')
        else:
            factors.append(f'x<span class="idx">{v}</span><span class="pow">{e}</span>')
    if factors:
        body = coeff_html + "&nbsp;" + "&nbsp;".join(factors)
    else:
        body = coeff_html
    return coeff, body


def _write_html(path: Path, src: Dict[str, Any], canonical_url: str) -> None:
    meta = src["meta"]
    vars_count = len(src["vars"])
    monomials = src["monomials"]
    term_count = len(monomials)
    base = meta.get("base", "?")
    channels = meta.get("channel_count", "?")

    lines: List[str] = []
    lines.append("<!doctype html>")
    lines.append('<html lang="en">')
    lines.append("<head>")
    lines.append('  <meta charset="utf-8" />')
    lines.append('  <meta name="viewport" content="width=device-width, initial-scale=1" />')
    lines.append("  <title>Universal Cubic Equation</title>")
    lines.append(f'  <link rel="canonical" href="{html.escape(canonical_url, quote=True)}">')
    lines.append('  <meta name="robots" content="noindex, follow">')
    lines.append("")
    lines.append("  <style>")
    lines.append("    :root {")
    lines.append("      color-scheme: light;")
    lines.append("    }")
    lines.append("    h1 {")
    lines.append("      margin: 0 0 8px 0;")
    lines.append("      font-size: 28px;")
    lines.append("      letter-spacing: 0.5px;")
    lines.append("    }")
    lines.append("    .meta {")
    lines.append("      font-size: 14px;")
    lines.append("      line-height: 1.5;")
    lines.append("      margin-bottom: 18px;")
    lines.append("      margin-top: 3em;")
    lines.append("    }")
    lines.append("    .meta code {")
    lines.append('      font-family: "Menlo", "Consolas", monospace;')
    lines.append("      font-size: 12px;")
    lines.append("      padding: 1px 4px;")
    lines.append("    }")
    lines.append("    .equation {")
    lines.append("      padding: 18px;")
    lines.append("      overflow-x: auto;")
    lines.append("    }")
    lines.append("    .line {")
    lines.append("      font-size: 7px;")
    lines.append("      line-height: 1.6;")
    lines.append("      white-space: nowrap;")
    lines.append("      font-family: monospace;")
    lines.append("    }")
    lines.append("    .idx {")
    lines.append("      font-size: 0.7em;")
    lines.append("      vertical-align: -0.35em;")
    lines.append("      margin-left: 0.05em;")
    lines.append("    }")
    lines.append("    .pow {")
    lines.append("      font-size: 0.7em;")
    lines.append("      vertical-align: 0.45em;")
    lines.append("      margin-left: 0.02em;")
    lines.append("    }")
    lines.append("    hr {")
    lines.append("      all: unset;")
    lines.append("      display: block;")
    lines.append("      height: 1px;")
    lines.append("      background: #000;")
    lines.append("      margin: 1em 0;")
    lines.append("    }")
    lines.append("  </style>")
    lines.append("</head>")
    lines.append("<body>")
    lines.append('  <div class="meta">')
    lines.append("    <h2>Universal Cubic Diophantine</h2>")
    lines.append(f"    <div>Terms: {term_count:,} | Variables: {vars_count:,}</div>")
    lines.append(f"    <div>Radix Base: {base} | Channels: {channels:,}</div>")
    lines.append("  </div>")
    lines.append('<div class="equation">')
    lines.append('<div class="line">U(x):</div>')
    lines.append('<div class="line">0 =</div>')

    for i, mon in enumerate(monomials):
        coeff, term_html = _render_monom_term(mon)
        if i == 0:
            if coeff < 0:
                line = f'&#8722;&nbsp;{term_html}'
            else:
                line = term_html
        else:
            if coeff < 0:
                line = f'&#8722;&nbsp;{term_html}'
            else:
                line = f'+&nbsp;{term_html}'
        lines.append(f'<div class="line">{line}</div>')

    lines.append("</div>")
    lines.append("</body>")
    lines.append("</html>")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Emit compact web serialization from canonical T003 coefficient JSON."
    )
    parser.add_argument(
        "--in",
        dest="in_path",
        required=True,
        help="Input canonical coefficients JSON (from gen.py).",
    )
    parser.add_argument(
        "--out",
        dest="out_path",
        default="",
        help="Output compact web JSON path.",
    )
    parser.add_argument(
        "--keep-vars",
        action="store_true",
        help="Keep vars[] names in web JSON (default: omitted).",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print output JSON (default: minified).",
    )
    parser.add_argument(
        "--emit-js",
        dest="emit_js",
        default="",
        help="Optional JS payload output path (window.<global>=...).",
    )
    parser.add_argument(
        "--js-global",
        dest="js_global",
        default="CUBIC_POLY_COMPACT",
        help="Global variable name for --emit-js (default: CUBIC_POLY_COMPACT).",
    )
    parser.add_argument(
        "--emit-html",
        dest="emit_html",
        default="",
        help="Optional standalone HTML equation output path.",
    )
    parser.add_argument(
        "--canonical-url",
        dest="canonical_url",
        default="https://milanrosko.com/projects/cubic.html",
        help="Canonical URL to embed in emitted HTML.",
    )
    args = parser.parse_args()

    in_path = Path(args.in_path).resolve()
    out_path = Path(args.out_path).resolve() if args.out_path else None

    if out_path is None and not args.emit_js and not args.emit_html:
        raise ValueError("No outputs selected. Provide --out and/or --emit-js and/or --emit-html.")

    if out_path is not None:
        out_path.parent.mkdir(parents=True, exist_ok=True)

    src = _load_json(in_path)
    payload = _make_web_payload(src, keep_vars=args.keep_vars)
    if out_path is not None:
        _write_json(out_path, payload, pretty=bool(args.pretty))

    if args.emit_js:
        js_path = Path(args.emit_js).resolve()
        js_path.parent.mkdir(parents=True, exist_ok=True)
        _write_js(js_path, payload, args.js_global)
    if args.emit_html:
        html_path = Path(args.emit_html).resolve()
        html_path.parent.mkdir(parents=True, exist_ok=True)
        _write_html(html_path, src, args.canonical_url)

    in_size = in_path.stat().st_size
    print(f"input:  {in_path} ({in_size} bytes)")
    if out_path is not None:
        out_size = out_path.stat().st_size
        ratio = (out_size / in_size) if in_size > 0 else 0.0
        print(f"output: {out_path} ({out_size} bytes)")
        print(f"ratio:  {ratio:.4f}")
    if args.emit_js:
        print(f"js:     {Path(args.emit_js).resolve()}")
    if args.emit_html:
        html_path = Path(args.emit_html).resolve()
        print(f"html:   {html_path} ({html_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
