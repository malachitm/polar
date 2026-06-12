import sympy
from pysmt.shortcuts import to_smtlib, Pow
from pysmt.typing import REAL
import pysmt.shortcuts as smt
from inputparser import Parser
from program import normalize_program
from recurrences import RecBuilder
from recurrences.solver import RecurrenceSolver
from io import StringIO
from sympy import symbols, Piecewise, sympify, S, Wild, collect, simplify, sqrt, exp, log, sin, cos, Add, Mul
import re
import sys
import time
from collections import defaultdict
from sympy.printing import sstr
from utils import resolve_real_croot, poly_to_int_coeffs, complex_root_metadata, phase_metadata

from sympy import sqrt as sympy_sqrt
import pysmt.shortcuts as smt
import json
from symengine import sympify as se_sympify

from sympy import Mul, Pow, Symbol, Integer

ALGEBRAIC_INTERVAL_EPS = 1e-10


class DebugLogger:
    def __init__(self, enabled=False):
        self.enabled = enabled
        self._totals = defaultdict(float)

    def log(self, message):
        if not self.enabled:
            return
        print(f"[closedforms2 debug] {message}", file=sys.stderr, flush=True)

    def timed(self, label):
        return _TimedBlock(self, label)

    def add_total(self, label, elapsed):
        if self.enabled:
            self._totals[label] += elapsed

    def emit_summary(self):
        if not self.enabled or not self._totals:
            return
        self.log("timing summary:")
        for label, elapsed in sorted(self._totals.items(), key=lambda item: item[1], reverse=True):
            self.log(f"  {label}: {elapsed:.6f}s")


class _TimedBlock:
    def __init__(self, logger, label):
        self._logger = logger
        self._label = label
        self.elapsed = 0.0
        self._start = 0.0

    def __enter__(self):
        self._start = time.perf_counter()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.elapsed = time.perf_counter() - self._start
        self._logger.add_total(self._label, self.elapsed)
        self._logger.log(f"{self._label}: {self.elapsed:.6f}s")
        return False


def parse_main_args(argv):
    args = list(argv[1:])
    debug = False
    filtered_args = []
    for arg in args:
        if arg == "--debug":
            debug = True
            continue
        filtered_args.append(arg)

    if not filtered_args:
        raise SystemExit("usage: closedforms2.py [--debug] <program> [vars ...]")

    return debug, filtered_args[0], filtered_args[1:]


def to_symengine_expr(expr):
    expr = sympy.sympify(expr)
    try:
        return se_sympify(expr)
    except Exception:
        return expr


def sympy_expr_with_locals(expr):
    sympy_expr = sympy.sympify(expr)
    locals_map = {sym.name: sym for sym in sympy_expr.free_symbols if getattr(sym, "name", None)}
    locals_map["I"] = sympy.I
    return sympy_expr, locals_map


def symengine_expand(expr):
    sympy_expr, locals_map = sympy_expr_with_locals(expr)
    backend_expr = to_symengine_expr(sympy_expr)
    if hasattr(backend_expr, "expand"):
        try:
            return sympy.sympify(str(backend_expr.expand()), locals=locals_map)
        except Exception:
            pass
    return sympy.expand(sympy_expr)


def symengine_simplify(expr):
    sympy_expr, locals_map = sympy_expr_with_locals(expr)
    backend_expr = to_symengine_expr(sympy_expr)
    if hasattr(backend_expr, "simplify"):
        try:
            return sympy.sympify(str(backend_expr.simplify()), locals=locals_map)
        except Exception:
            pass
    return sympy.simplify(sympy_expr)


class RootRegistry:
    def __init__(self):
        self._entries = {}
        self._symbols = {}
        self._ordered = []

    def register(self, expr):
        if expr in self._entries:
            return self._entries[expr]["name"]

        resolved = resolve_real_algebraic_expr(expr)
        if resolved is None:
            return None

        poly_expr, low, high = resolved
        entry = {
            "name": f"_alg_{len(self._ordered)}",
            "poly_coeffs": poly_to_int_coeffs(poly_expr),
            "low": str(low),
            "high": str(high),
        }
        self._entries[expr] = entry
        self._symbols[expr] = sympy.Symbol(entry["name"], real=True)
        self._ordered.append(entry)
        return entry["name"]

    def substitution_map(self):
        return dict(self._symbols)

    def to_json(self):
        return list(self._ordered)


def serialize_real_value(value, digits=50):
    value = sympy.simplify(sympy.sympify(value))
    if value.is_Rational:
        return str(value)
    return str(sympy.N(value, digits))


def resolve_algebraic_value(expr, eps=ALGEBRAIC_INTERVAL_EPS):
    """Return (int_coeffs_list, low_str, high_str) for a real algebraic irrational.

    The returned polynomial is the minimal polynomial of *expr* and the interval
    [low, high] isolates it from all other roots.  Returns None when *expr* is
    rational (the caller should use serialize_real_value instead).
    """
    expr = sympy.simplify(sympy.sympify(expr))
    if expr.is_rational:
        return None
    if expr.free_symbols:
        return None

    poly_var = sympy.Symbol("_x")
    try:
        min_poly = sympy.minpoly(expr, poly_var)
    except Exception:
        return None

    poly_num, _ = sympy.fraction(sympy.together(min_poly))
    poly = sympy.Poly(poly_num, poly_var)

    target = sympy.N(expr, 50)
    for interval, _ in poly.intervals(eps=eps):
        low, high = interval
        low_q = sympy.Rational(low)
        high_q = sympy.Rational(high)
        if low_q <= target <= high_q:
            return (poly_to_int_coeffs(poly.as_expr()), str(low_q), str(high_q))

    raise ValueError(f"Could not isolate algebraic polynomial for {expr}")


def linear_n_coeff(exp, symbol_name="n"):
    exp = sympy.sympify(exp)
    if not exp.free_symbols:
        return None

    n_symbols = [sym for sym in exp.free_symbols if getattr(sym, "name", None) == symbol_name]
    if len(n_symbols) != 1 or len(exp.free_symbols) != 1:
        return None

    coeff = sympy.simplify(exp / n_symbols[0])
    return coeff if coeff.is_Rational else None


def affine_n_parts(exp, symbol_name="n"):
    exp = sympy.simplify(sympy.sympify(exp))
    if not exp.free_symbols:
        return sympy.Integer(0), exp

    n_symbols = [sym for sym in exp.free_symbols if getattr(sym, "name", None) == symbol_name]
    if len(n_symbols) != 1 or len(exp.free_symbols) != 1:
        return None

    n_sym = n_symbols[0]
    coeff = sympy.simplify(sympy.diff(exp, n_sym))
    if coeff.free_symbols:
        return None

    constant = sympy.simplify(exp - coeff * n_sym)
    if constant.free_symbols:
        return None

    return coeff, constant


def is_negative_real_constant(expr):
    expr = sympy.simplify(sympy.sympify(expr))
    if expr.free_symbols:
        return False
    if expr.is_real is False:
        return False
    if expr.is_negative is True:
        return True
    try:
        return sympy.N(expr, 50) < 0
    except TypeError:
        return False


def resolve_positive_magnitude_expr(expr, eps=ALGEBRAIC_INTERVAL_EPS):
    expr = sympy.simplify(sympy.sympify(expr))
    if expr.free_symbols or expr.is_real is False:
        raise ValueError(f"Expected a concrete positive real magnitude, got {expr}")

    poly_var = sympy.Symbol("_mag_x")
    min_poly = sympy.minpoly(expr, poly_var)
    poly_num, _ = sympy.fraction(sympy.together(min_poly))
    poly = sympy.Poly(poly_num, poly_var)

    if expr.is_rational:
        qexpr = sympy.Rational(expr)
        return poly.as_expr(), qexpr, qexpr

    target = sympy.N(expr, 50)
    for interval, _ in poly.intervals(eps=eps):
        low, high = interval
        low_q = sympy.Rational(low)
        high_q = sympy.Rational(high)
        if low_q <= target <= high_q:
            return poly.as_expr(), low_q, high_q

    raise ValueError(f"Could not isolate magnitude polynomial for {expr}")


class ComplexPairRegistry:
    def __init__(self):
        self._entries = {}
        self._root_to_entry = {}
        self._negative_entries = {}
        self._ordered = []

    def _key(self, root):
        conj_root = sympy.conjugate(root)
        return tuple(sorted((sstr(root), sstr(conj_root))))

    def _metadata_for_root(self, root):
        if isinstance(root, sympy.ComplexRootOf):
            return complex_root_metadata(root, eps=ALGEBRAIC_INTERVAL_EPS)

        real_part = sympy.simplify(sympy.re(root))
        imag_part = sympy.simplify(sympy.im(root))
        if imag_part == 0:
            raise ValueError(f"expected a non-real algebraic constant, got {root}")

        magnitude = sympy.simplify(sympy.sqrt(real_part**2 + imag_part**2))
        poly_expr, low, high = resolve_positive_magnitude_expr(magnitude)
        phase = phase_metadata(real_part, imag_part)
        return {
            "mag_poly": poly_expr,
            "mag_low": low,
            "mag_high": high,
            **phase,
        }

    def register(self, expr):
        root = sympy.simplify(sympy.sympify(expr))
        if root.free_symbols or root.is_real:
            return None

        if sympy.simplify(sympy.im(root)) == 0:
            return None

        key = self._key(root)
        if key in self._entries:
            return self._entries[key]

        metadata = self._metadata_for_root(root)
        index = len(self._ordered)
        conjugate_root = sympy.conjugate(root)
        period = int(metadata["period"]) if metadata["is_periodic"] else None
        cos_alg = resolve_algebraic_value(metadata["cos_theta"])
        sin_alg = resolve_algebraic_value(metadata["sin_theta"])
        entry = {
            "mag_name": f"_mag_{index}",
            "ccos_name": f"_ccos_{index}",
            "csin_name": f"_csin_{index}",
            "mag_poly": poly_to_int_coeffs(metadata["mag_poly"]),
            "mag_low": str(metadata["mag_low"]),
            "mag_high": str(metadata["mag_high"]),
            "cos_theta": serialize_real_value(metadata["cos_theta"]),
            "sin_theta": serialize_real_value(metadata["sin_theta"]),
            "cos_theta_poly": cos_alg[0] if cos_alg else None,
            "cos_theta_low": cos_alg[1] if cos_alg else None,
            "cos_theta_high": cos_alg[2] if cos_alg else None,
            "sin_theta_poly": sin_alg[0] if sin_alg else None,
            "sin_theta_low": sin_alg[1] if sin_alg else None,
            "sin_theta_high": sin_alg[2] if sin_alg else None,
            "is_periodic": bool(metadata["is_periodic"]),
            "period": period,
            "root": root,
            "conjugate_root": conjugate_root,
            "mag_symbol": sympy.Symbol(f"_mag_{index}", real=True, positive=True),
            "ccos_symbol": sympy.Symbol(f"_ccos_{index}", real=True),
            "csin_symbol": sympy.Symbol(f"_csin_{index}", real=True),
        }
        self._entries[key] = entry
        self._root_to_entry[root] = entry
        self._root_to_entry[conjugate_root] = entry
        self._ordered.append(entry)
        return entry

    def get(self, root):
        return self._root_to_entry.get(sympy.sympify(root))

    def register_negative_real(self, expr):
        root = sympy.simplify(sympy.sympify(expr))
        if not is_negative_real_constant(root):
            return None

        key = sstr(root)
        if key in self._negative_entries:
            return self._negative_entries[key]

        magnitude = sympy.simplify(-root)
        poly_expr, low, high = resolve_positive_magnitude_expr(magnitude)
        phase = phase_metadata(root, sympy.Integer(0))
        index = len(self._ordered)
        cos_alg = resolve_algebraic_value(phase["cos_theta"])
        sin_alg = resolve_algebraic_value(phase["sin_theta"])
        entry = {
            "kind": "negative-real",
            "mag_name": f"_mag_{index}",
            "ccos_name": f"_ccos_{index}",
            "csin_name": f"_csin_{index}",
            "mag_poly": poly_to_int_coeffs(poly_expr),
            "mag_low": str(low),
            "mag_high": str(high),
            "cos_theta": serialize_real_value(phase["cos_theta"]),
            "sin_theta": serialize_real_value(phase["sin_theta"]),
            "cos_theta_poly": cos_alg[0] if cos_alg else None,
            "cos_theta_low": cos_alg[1] if cos_alg else None,
            "cos_theta_high": cos_alg[2] if cos_alg else None,
            "sin_theta_poly": sin_alg[0] if sin_alg else None,
            "sin_theta_low": sin_alg[1] if sin_alg else None,
            "sin_theta_high": sin_alg[2] if sin_alg else None,
            "is_periodic": bool(phase["is_periodic"]),
            "period": int(phase["period"]) if phase["is_periodic"] else None,
            "root": root,
            "mag_symbol": sympy.Symbol(f"_mag_{index}", real=True, positive=True),
            "ccos_symbol": sympy.Symbol(f"_ccos_{index}", real=True),
            "csin_symbol": sympy.Symbol(f"_csin_{index}", real=True),
        }
        self._negative_entries[key] = entry
        self._ordered.append(entry)
        return entry

    def get_negative(self, root):
        return self._negative_entries.get(sstr(sympy.simplify(sympy.sympify(root))))

    def to_json(self):
        result = []
        for entry in self._ordered:
            obj = {
                "mag_name": entry["mag_name"],
                "ccos_name": entry["ccos_name"],
                "csin_name": entry["csin_name"],
                "mag_poly": entry["mag_poly"],
                "mag_low": entry["mag_low"],
                "mag_high": entry["mag_high"],
                "cos_theta": entry["cos_theta"],
                "sin_theta": entry["sin_theta"],
                "is_periodic": entry["is_periodic"],
                "period": entry["period"],
            }
            if entry.get("cos_theta_poly") is not None:
                obj["cos_theta_poly"] = entry["cos_theta_poly"]
                obj["cos_theta_low"] = entry["cos_theta_low"]
                obj["cos_theta_high"] = entry["cos_theta_high"]
            if entry.get("sin_theta_poly") is not None:
                obj["sin_theta_poly"] = entry["sin_theta_poly"]
                obj["sin_theta_low"] = entry["sin_theta_low"]
                obj["sin_theta_high"] = entry["sin_theta_high"]
            result.append(obj)
        return result


def resolve_real_algebraic_expr(expr, eps=ALGEBRAIC_INTERVAL_EPS):
    expr = sympy.simplify(sympy.sympify(expr))
    if expr.is_rational:
        return None

    if isinstance(expr, sympy.ComplexRootOf):
        status, data = resolve_real_croot(expr, eps=eps)
        if status == "real":
            return data
        return None

    if expr.free_symbols:
        return None

    if isinstance(expr, sympy.Pow) and isinstance(expr.exp, sympy.Rational) and not expr.exp.is_Integer:
        if expr.is_real is False:
            return None

        poly_var = sympy.Symbol("_alg_x")
        poly = sympy.Poly(sympy.minpoly(expr, poly_var), poly_var)
        target = sympy.N(expr, 50)
        for interval, _ in poly.intervals(eps=eps):
            low, high = interval
            low_q = sympy.Rational(low)
            high_q = sympy.Rational(high)
            if low_q <= target <= high_q:
                return (poly.as_expr(), low_q, high_q)

        raise ValueError(f"Could not isolate algebraic root for {expr}")

    return None


def extract_algebraic_roots(expr, registry):
    backend_expr = to_symengine_expr(expr)
    sympy_expr = sympy.sympify(backend_expr)
    if registry.register(sympy_expr) is not None:
        return

    for arg in backend_expr.args:
        extract_algebraic_roots(arg, registry)


def extract_complex_pairs(expr, registry):
    backend_expr = to_symengine_expr(expr)
    # Only register the base when this expression is Pow(base, k*n) — the only
    # form where a genuine eigenvalue base appears in a closed form.  Visiting
    # arbitrary complex sub-expressions (e.g. the imaginary unit I inside an
    # eigenvector coefficient) would otherwise register spurious complex pairs.
    if getattr(backend_expr, "is_Pow", False):
        base, exp = backend_expr.args
        if linear_n_coeff(exp, "n") is not None:
            registry.register(base)
            return

    for arg in backend_expr.args:
        extract_complex_pairs(arg, registry)


def substitute_registered_roots(expr, registry):
    substitutions = registry.substitution_map()
    if not substitutions:
        return expr
    return sympy.sympify(expr).xreplace(substitutions)


def split_complex_root_term(term, registry, symbol_name="n"):
    factors = term.args if isinstance(term, sympy.Mul) else (term,)
    coeff = sympy.Integer(1)
    root = None

    for factor in factors:
        normalized = sympy.powdenest(factor, force=True)
        if isinstance(normalized, sympy.Pow):
            base, exp = normalized.as_base_exp()
            if linear_n_coeff(exp, symbol_name) == 1:
                entry = registry.get(base)
                if entry is not None:
                    if root is not None:
                        return None
                    root = sympy.sympify(base)
                    continue
        coeff *= factor

    if root is None:
        return None
    return root, symengine_simplify(coeff)


def rewrite_complex_pairs(expr, registry, n_sym):
    expr = symengine_expand(expr)
    grouped_terms = {}
    unmatched_terms = []

    for term in (expr.args if getattr(expr, "is_Add", False) else [expr]):
        split = split_complex_root_term(term, registry, getattr(n_sym, "name", "n"))
        if split is None:
            unmatched_terms.append(term)
            continue

        root, coeff = split
        entry = registry.get(root)
        if entry is None:
            unmatched_terms.append(term)
            continue

        group = grouped_terms.setdefault(
            entry["mag_name"],
            {"entry": entry, "alpha_coeff": None, "beta_coeff": None},
        )
        if root == entry["root"]:
            group["alpha_coeff"] = coeff if group["alpha_coeff"] is None else symengine_simplify(group["alpha_coeff"] + coeff)
        else:
            group["beta_coeff"] = coeff if group["beta_coeff"] is None else symengine_simplify(group["beta_coeff"] + coeff)

    rewritten_terms = list(unmatched_terms)
    for group in grouped_terms.values():
        entry = group["entry"]
        alpha_coeff = group["alpha_coeff"]
        beta_coeff = group["beta_coeff"]

        if alpha_coeff is None or beta_coeff is None:
            if alpha_coeff is not None:
                rewritten_terms.append(alpha_coeff * entry["root"] ** n_sym)
            if beta_coeff is not None:
                rewritten_terms.append(beta_coeff * entry["conjugate_root"] ** n_sym)
            continue

        trig_coeff = symengine_simplify(
            (alpha_coeff + beta_coeff) * entry["ccos_symbol"]
            + sympy.I * (alpha_coeff - beta_coeff) * entry["csin_symbol"]
        )
        rewritten_terms.append(symengine_simplify((entry["mag_symbol"] ** n_sym) * trig_coeff))

    return symengine_simplify(sympy.Add(*rewritten_terms))


def rewrite_negative_real_phases(expr, registry, n_sym):
    expr = symengine_expand(expr)
    rewritten_terms = []

    for term in (expr.args if getattr(expr, "is_Add", False) else [expr]):
        normalized = sympy.powsimp(term, combine="base", force=True)
        factors = normalized.args if isinstance(normalized, sympy.Mul) else (normalized,)

        negative_pow = None
        remaining = sympy.Integer(1)
        for factor in factors:
            candidate = sympy.powdenest(factor, force=True)
            if isinstance(candidate, sympy.Pow):
                base, exp = candidate.as_base_exp()
                if linear_n_coeff(exp, getattr(n_sym, "name", "n")) == 1 and is_negative_real_constant(base):
                    if negative_pow is not None:
                        negative_pow = None
                        break
                    negative_pow = base
                    continue
            remaining *= factor

        if negative_pow is None:
            rewritten_terms.append(normalized)
            continue

        entry = registry.register_negative_real(negative_pow)
        mag_term = entry["mag_symbol"] ** n_sym
        rewritten_terms.append(symengine_simplify(remaining * mag_term * entry["ccos_symbol"]))

    return symengine_simplify(sympy.Add(*rewritten_terms))

def unroll_powers(expr):
    """
    Recursively converts integer powers into multiplication.
    Example: x**2 -> x*x, (y+1)**3 -> (y+1)*(y+1)*(y+1)
    """
    print("Before unrolling: ", expr)
    if expr.is_Atom:
        return expr

    # Handle Power terms (base**exp)
    if expr.is_Pow:
        base, exp = expr.as_base_exp()
        # Only unroll positive integers (e.g., 2, 3, 4...)
        if exp.is_Integer and exp > 0:
            # Recursively unroll the base first (in case it has powers inside)
            unrolled_base = unroll_powers(base)
            # Create a Multiplication of the base repeated 'exp' times
            return Mul(*[unrolled_base] * int(exp))
    
    # Recursively apply to all arguments of other operators (Add, Mul, etc.)
    new_expr = expr.func(*[unroll_powers(arg) for arg in expr.args])
    print("After unrolling: ", new_expr)
    return new_expr

def sympy_to_pysmt2(sympy_expr, symbol_cache=None):
    """
    Converts a SymPy expression containing only real numbers, symbols,
    addition, and multiplication into a PySMT formula.
    """
    if symbol_cache is None:
        symbol_cache = {}

    # Base Case: SymPy Symbol
    if isinstance(sympy_expr, sympy.Symbol):
        if sympy_expr in symbol_cache:
            return symbol_cache[sympy_expr]
        else:
            pysmt_symbol = smt.Symbol(sympy_expr.name, REAL)
            symbol_cache[sympy_expr] = pysmt_symbol
            return pysmt_symbol

    # Base Case: SymPy Numbers
    elif isinstance(sympy_expr, sympy.Integer):
        return smt.Real((int(sympy_expr), 1))
    elif isinstance(sympy_expr, sympy.Float):
        return smt.Real(float(sympy_expr))
    elif isinstance(sympy_expr, sympy.Rational):
        return smt.Real((int(sympy_expr.p), int(sympy_expr.q)))

    # Recursive Case: Addition
    elif isinstance(sympy_expr, sympy.Add):
        pysmt_args = [sympy_to_pysmt2(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Plus(*pysmt_args)

    # Recursive Case: Multiplication
    elif isinstance(sympy_expr, sympy.Mul):
        pysmt_args = [sympy_to_pysmt2(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Times(*pysmt_args)
    
    # Recursive Case: Power (including square roots)
    elif isinstance(sympy_expr, sympy.Pow):
        base = sympy_expr.args[0]
        exponent = sympy_expr.args[1]

        # General power case
        base_pysmt = sympy_to_pysmt2(base, symbol_cache)
        
        if isinstance(exponent, sympy.Integer):
            exp_val = int(exponent)
            
            # Case 1: x^0 = 1
            if exp_val == 0:
                return smt.Real(1) if base_pysmt.get_type().is_real_type() else smt.Int(1)
            
            # Case 2: x^1 = x
            elif exp_val == 1:
                return base_pysmt
                
            # Case 3: x^n where n > 1 (Unroll to multiplication)
            elif exp_val > 1:
                # Create a list of 'base' repeated 'exp_val' times
                unrolled_factors = [base_pysmt] * exp_val
                return smt.Times(*unrolled_factors)
                
            # Case 4: x^-n (Negative powers become division)
            else:
                # Handle x^-2 as 1 / (x * x)
                positive_exp = -exp_val
                unrolled_factors = [base_pysmt] * positive_exp
                denominator = smt.Times(*unrolled_factors)
                
                # Use Real(1) for division to ensure float division if applicable
                return smt.Div(smt.Real(1), denominator)
        else:
            if exponent.has(sympy.I):
                raise NotImplementedError("Complex exponents are not supported")
            if exponent.free_symbols:
                raise NotImplementedError(
                    f"Non-constant exponent reached sympy_to_pysmt2: {sympy_expr}"
                )
            exp_pysmt = sympy_to_pysmt2(exponent, symbol_cache)
            # return smt.Pow(base_pysmt, smt.Symbol(str(exp_pysmt), REAL))
            return smt.Pow(base_pysmt, exp_pysmt)
    
    # Handle constants
    elif isinstance(sympy_expr, (sympy.core.numbers.Pi, sympy.core.numbers.EulerGamma, sympy.core.numbers.ImaginaryUnit)):
         pysmt_symbol = smt.Symbol(str(sympy_expr), REAL)
         symbol_cache[sympy_expr] = pysmt_symbol
         return pysmt_symbol
    
    # Unsupported Type
    else:
        raise NotImplementedError(f"Conversion for SymPy type '{type(sympy_expr).__name__}' is not implemented.")

def sympy_to_pysmt(sympy_expr, symbol_cache=None):
    if symbol_cache is None:
        symbol_cache = {}

    # Base Case: SymPy Symbol
    if isinstance(sympy_expr, sympy.Symbol):
        # Check cache first
        if sympy_expr in symbol_cache:
            return symbol_cache[sympy_expr]
        else:
            # Create a PySMT REAL symbol and cache it
            pysmt_symbol = smt.Symbol(sympy_expr.name, REAL)
            symbol_cache[sympy_expr] = pysmt_symbol
            return pysmt_symbol

    # Base Case: SymPy Numbers (Integer, Float, Rational)
    elif isinstance(sympy_expr, sympy.Integer):
        # Convert SymPy Integer to PySMT Real
        return smt.Real(float(sympy_expr))
    elif isinstance(sympy_expr, sympy.Float):
        # Convert SymPy Float to PySMT Real
        return smt.Real(float(sympy_expr))
    elif isinstance(sympy_expr, sympy.Rational):
        # Convert SymPy Rational to PySMT Real fraction
        # Use float for simplicity here, but (p, q) is more exact if needed
        # return Real((sympy_expr.p, sympy_expr.q))
        return smt.Real(float(sympy_expr)) # Convert to float for Real

    # Recursive Case: SymPy Addition
    elif isinstance(sympy_expr, sympy.Add):
        # Recursively convert all arguments and sum them with PySMT's Plus
        pysmt_args = [sympy_to_pysmt(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Plus(*pysmt_args)

    # Recursive Case: SymPy Multiplication
    elif isinstance(sympy_expr, sympy.Mul):
        # Recursively convert all arguments and multiply them with PySMT's Times
        pysmt_args = [sympy_to_pysmt(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Times(*pysmt_args)
    
    elif isinstance(sympy_expr, sympy.Pow):
        base = sympy_to_pysmt(sympy_expr.args[0], symbol_cache)
        exponent = sympy_expr.args[1]
        if isinstance(exponent, sympy.Integer):
            exp_val = int(exponent)
            
            # Case 1: x^0 = 1
            if exp_val == 0:
                return smt.Real(1) if base.get_type().is_real_type() else smt.Int(1)
            
            # Case 2: x^1 = x
            elif exp_val == 1:
                return base
                
            # Case 3: x^n where n > 1 (Unroll to multiplication)
            elif exp_val > 1:
                # Create a list of 'base' repeated 'exp_val' times
                unrolled_factors = [base] * exp_val
                return smt.Times(*unrolled_factors)
                
            # Case 4: x^-n (Negative powers become division)
            else:
                # Handle x^-2 as 1 / (x * x)
                positive_exp = -exp_val
                unrolled_factors = [base] * positive_exp
                denominator = smt.Times(*unrolled_factors)
                
                # Use Real(1) for division to ensure float division if applicable
                return smt.Div(smt.Real(1), denominator)
        else:
            if exponent.has(sympy.I):
                raise NotImplementedError("Complex exponents are not supported")
            if exponent.free_symbols:
                raise NotImplementedError(
                    f"Non-constant exponent reached sympy_to_pysmt: {sympy_expr}"
                )
            new_exp = sympy_to_pysmt(exponent, symbol_cache)
            # return smt.Pow(base_pysmt, smt.Symbol(str(new_exp), REAL))
            return smt.Pow(base, new_exp)
    
    # Handle constants like pi, E, etc. (Treat them as symbols for now)
    # Or raise error if they shouldn't be treated as symbols
    
    elif isinstance(sympy_expr, (sympy.core.numbers.Pi, sympy.core.numbers.EulerGamma, sympy.core.numbers.ImaginaryUnit)):
         # Treat known constants as symbols if needed, or error out
         pysmt_symbol = smt.Symbol(str(sympy_expr), REAL)
         symbol_cache[sympy_expr] = pysmt_symbol
         return pysmt_symbol
    
    # Unsupported Type/Operation
    else:
        raise NotImplementedError(f"Conversion for SymPy type '{type(sympy_expr).__name__}' is not implemented.")
    
def get_summands(expr):
    if isinstance(expr, Add):
        return list(expr.args)
    else:
        return [expr]

def separate_pow_and_nonpow(term):
    # If the term is a Mul (product), split its factors
    if isinstance(term, Mul):
        factors = term.args
    else:
        factors = [term]

    flattened_factors = []
    for factor in factors:
        if isinstance(factor, sympy.Pow):
            base, exp = factor.as_base_exp()
            if isinstance(base, sympy.Mul) and not exp.free_symbols:
                flattened_factors.extend(sympy.Pow(arg, exp) for arg in base.args)
                continue
        flattened_factors.append(factor)
    
    pow_factors = []
    nonpow_factors = []
    
    for factor in flattened_factors:
        if isinstance(factor, sympy.Pow):
            pow_factors.append(factor)
        else:
            nonpow_factors.append(factor)
    
    return pow_factors, nonpow_factors

def find_bases_from_formula(formula):
    #print(formula)
    bases = defaultdict(list)
    terms = get_summands(formula)

    for term in terms:
        term = sympy.expand_power_base(term, force=True)
        term = sympy.powsimp(term, combine="base", force=True)
        #print("Term: ", term)
        base = 1
        poly = 1
        pow_factors, nonpow_factors = separate_pow_and_nonpow(term)
        for pow_term in pow_factors:
            pow_term = sympy.powdenest(pow_term, force=True)
            b, exp = pow_term.as_base_exp()
            parts = affine_n_parts(exp)

            # Normalize b^(q*n + c) into (b^q)^n * b^c so the base remains
            # constant and no symbolic exponent reaches the SMT serializer.
            if parts is not None:
                coeff, constant = parts
                if sympy.simplify(coeff) != 0:
                    base *= sympy.Pow(b, coeff)
                if sympy.simplify(constant) != 0:
                    poly *= sympy.Pow(b, constant)
            else:
                poly *= pow_term
        base = sympy.simplify(base)
        for nonpow_factor in nonpow_factors:
            poly *= nonpow_factor
        
        #print("Base: ", base)
        #print("Polynomial: ", poly)
        bases[base].append(poly)

    return dict(bases)

def get_bases_and_coefficients2(formula):
    if(formula == 0):
        return [("constant", "0")]
    
    expanded_formula = formula.expand()
    #print(f"Expanded formula: {expanded_formula}, Original: {formula}")
    bases = find_bases_from_formula(expanded_formula)
    bases_summed = {}
    for base, poly_list in bases.items():
        bases_summed[base] = Add(*poly_list)
    return bases_summed.items()


def normalize_serialized_base_and_coeff(base_expr, coeff_expr, symbol_name="n"):
    base_expr = sympy.sympify(base_expr)
    coeff_expr = sympy.sympify(coeff_expr)
    coeff_expr = sympy.expand_power_base(coeff_expr, force=True)
    coeff_expr = sympy.powsimp(coeff_expr, force=True)

    if isinstance(coeff_expr, sympy.Mul):
        factors = list(coeff_expr.args)
    else:
        factors = [coeff_expr]

    normalized_factors = []
    for factor in factors:
        candidate = sympy.powdenest(factor, force=True)
        if isinstance(candidate, sympy.Pow):
            factor_base, factor_exp = candidate.as_base_exp()
            parts = affine_n_parts(factor_exp, symbol_name)
            if parts is not None:
                n_coeff, constant = parts
                if sympy.simplify(n_coeff) != 0:
                    base_expr *= sympy.Pow(factor_base, n_coeff)
                    if sympy.simplify(constant) != 0:
                        normalized_factors.append(sympy.Pow(factor_base, constant))
                    continue
        normalized_factors.append(candidate)

    base_expr = sympy.powsimp(sympy.expand_power_base(base_expr, force=True), combine="base", force=True)
    coeff_expr = sympy.powsimp(sympy.Mul(*normalized_factors), force=True)
    return sympy.simplify(base_expr), sympy.simplify(coeff_expr)

def convert_coordinates2(text):
    """
    Scans a string and appends ".0" to any whole number (integer) that is 
    not already part of a float (i.e., not immediately preceded or followed by a dot).
    Also skips numbers that are part of special root variable names like sqrt17.
    """
    # Regex Pattern Breakdown:
    # (?<!\.) : Negative Lookbehind. Ensures the number is NOT preceded by a dot
    #           (prevents matching the "45" in "123.45").
    # (?<!sqrt) : Negative Lookbehind. Ensures the number is NOT preceded by "sqrt"
    #           (prevents matching numbers in "sqrt17", "sqrt42", etc.).
    #           (prevents matching numbers in "cbrt8", etc.).
    # \b      : Word Boundary. Ensures we are matching a distinct number.
    # (\d+)   : Group 1. Matches one or more digits.
    # \b      : Word Boundary. Marks the end of the number digits.
    # (?!\.)  : Negative Lookahead. Ensures the number is NOT followed by a dot
    #           (prevents matching the "123" in "123.45").
    pattern = r'(?<![\.t])\b(\d+)\b(?!\.)'

    # The Replacement:
    # \g<1> represents the digits matched in Group 1.
    # .0    is the string we want to insert.
    new_text = re.sub(pattern, r'\g<1>.0', text)
    
    return new_text

def convert_coordinates(text):
    """
    Finds patterns like "(/ 400 500)" and converts them to "(/ 400.0 500.0)".
    """
    # Regex Pattern Breakdown:
    # \(      -> Matches literal "("
    # /       -> Matches literal "/" (no escape needed in Python regex)
    # \s+     -> Matches one or more spaces
    # (\d+)   -> Group 1: Matches the first integer
    # \s+     -> Matches one or more spaces
    # (\d+)   -> Group 2: Matches the second integer
    # \)      -> Matches literal ")"
    pattern = r'\(\/\s+(\d+)\s+(\d+)\)'

    # We use a replacement function to construct the new string
    def replacer(match):
        # match.group(1) is the first number (e.g., "400")
        # match.group(2) is the second number (e.g., "500")
        return f"(/ {match.group(1)}.0 {match.group(2)}.0)"

    # re.sub finds all non-overlapping occurrences of the pattern and replaces them
    new_text = re.sub(pattern, replacer, text)
    
    return new_text

def build_payload(program_path, vars, debug_logger=None):
    debug_logger = DebugLogger() if debug_logger is None else debug_logger

    with debug_logger.timed("parse_file"):
        program = Parser().parse_file(program_path)
    with debug_logger.timed("normalize_program"):
        program = normalize_program(program)
    with debug_logger.timed("build_rec_builder"):
        rec_builder = RecBuilder(program)

    roots: set = set()
    var_dict = {}
    root_registry = RootRegistry()
    complex_registry = ComplexPairRegistry()

    for var in vars:
        debug_logger.log(f"starting variable {var}")
        var_dict[var] = []
        with debug_logger.timed(f"var {var}: get_recurrences"):
            recurr = rec_builder.get_recurrences(var)
        debug_logger.log(
            f"variable {var}: recurrence system size={len(recurr.monomials)}, inhomogeneous={recurr.is_inhomogeneous}, acyclic={recurr.is_acyclic}"
        )
        with debug_logger.timed(f"var {var}: solve_closed_form"):
            solver = RecurrenceSolver(recurr)
            closed_form = solver.get(var)
        debug_logger.log(f"variable {var}: solver exact={solver.is_exact}")
        n_sym = symbols('n')

        if isinstance(closed_form, Piecewise):
            pieces = closed_form.args
        else:
            pieces = [(closed_form, True)]
        debug_logger.log(f"variable {var}: piece count={len(pieces)}")

        rewritten_pieces = []
        with debug_logger.timed(f"var {var}: rewrite_pieces"):
            for formula, cond in pieces:
                extract_complex_pairs(formula, complex_registry)
                rewritten = rewrite_complex_pairs(formula, complex_registry, n_sym)
                rewritten = rewrite_negative_real_phases(rewritten, complex_registry, n_sym)
                extract_algebraic_roots(rewritten, root_registry)
                rewritten_pieces.append((rewritten, cond))

        base_count = 0
        with debug_logger.timed(f"var {var}: serialize_pieces"):
            for i, (formula, _) in enumerate(rewritten_pieces):
                piece = {
                    "bases": [],
                    "coeffs": [],
                }
                bases_and_coefficients = list(get_bases_and_coefficients2(formula))
                base_count += len(bases_and_coefficients)
                for j, (base, coeff) in enumerate(bases_and_coefficients):
                    if base == "constant":
                        base = "1.0"

                    base_expr = substitute_registered_roots(sympy.factor(sympy.radsimp(sympify(base))), root_registry)
                    coeff_expr = substitute_registered_roots(sympy.factor(sympy.radsimp(sympify(coeff))), root_registry)
                    base_expr, coeff_expr = normalize_serialized_base_and_coeff(base_expr, coeff_expr)

                    smt_base = to_smtlib(sympy_to_pysmt2(base_expr), daggify=False)
                    smt_base = convert_coordinates2(smt_base)
                    smt_coeff = to_smtlib(sympy_to_pysmt2(coeff_expr), daggify=False)
                    smt_coeff = convert_coordinates2(smt_coeff)

                    piece["bases"].append(smt_base)
                    piece["coeffs"].append(smt_coeff)

                    if base != "1.0":
                        roots.add(smt_base)

                var_dict[var].append(piece)

        debug_logger.log(
            f"variable {var}: emitted {len(var_dict[var])} serialized pieces, {base_count} base/coeff pairs, total aux_roots={len(root_registry._ordered)}, complex_pairs={len(complex_registry._ordered)}"
        )

    return {"aux_roots": root_registry.to_json(), "complex_pairs": complex_registry.to_json(), **var_dict}


def main(argv=None):
    argv = sys.argv if argv is None else argv
    debug_enabled, program_path, vars = parse_main_args(argv)
    debug_logger = DebugLogger(debug_enabled)
    with debug_logger.timed("total"):
        payload = build_payload(program_path, vars, debug_logger=debug_logger)
    json_string = json.dumps(payload)
    with open('data.json', 'w', encoding='utf-8') as f:
        json.dump(payload, f, ensure_ascii=False, indent=4)
    debug_logger.emit_summary()
    print(str(json_string).replace("pow", "^"))


if __name__ == "__main__":
    main()