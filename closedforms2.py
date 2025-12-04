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
from collections import defaultdict

from sympy import sqrt as sympy_sqrt
import pysmt.shortcuts as smt
import json
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
        pysmt_args = [sympy_to_pysmt(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Plus(*pysmt_args)

    # Recursive Case: Multiplication
    elif isinstance(sympy_expr, sympy.Mul):
        pysmt_args = [sympy_to_pysmt(arg, symbol_cache) for arg in sympy_expr.args]
        return smt.Times(*pysmt_args)
    
    # Recursive Case: Power (including square roots)
    elif isinstance(sympy_expr, sympy.Pow):
        base = sympy_expr.args[0]
        exponent = sympy_expr.args[1]
        
        # Special case: square root (exponent = 1/2)
        if exponent == sympy.Rational(1, 2):
            base_pysmt = sympy_to_pysmt(base, symbol_cache)
            # Check if PySMT has a sqrt function
            # If not, use Pow with exponent 0.5
            try:
                return smt.Sqrt(base_pysmt)  # Try using Sqrt if available
            except AttributeError:
                return smt.Pow(base_pysmt, smt.Real(0.5))
        
        # General power case
        base_pysmt = sympy_to_pysmt(base, symbol_cache)
        
        if isinstance(exponent, sympy.Integer):
            return smt.Pow(base_pysmt, smt.Real(float(exponent)))
        elif isinstance(exponent, sympy.Rational):
            exp_pysmt = smt.Real(float(exponent))
            return smt.Pow(base_pysmt, exp_pysmt)
        elif isinstance(exponent, sympy.Symbol):
            return smt.Pow(base_pysmt, smt.Symbol(str(exponent), REAL))
        else:
            raise NotImplementedError(f"Unsupported exponent type: {type(exponent).__name__}")
    
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
            # Convert integer exponent to PySMT
            return smt.Pow(base, smt.Real(float(exponent)))
        elif isinstance(exponent, sympy.Rational):
            # Convert rational exponent to PySMT
            new_exp = sympy_to_pysmt(exponent, symbol_cache)
            return smt.Pow(base, new_exp)
        elif isinstance(exponent, sympy.Symbol):
            # If exponent is a symbol, treat it as a variable
            # This is a bit tricky, as PySMT doesn't support symbolic exponents directly
            # We can return the base raised to the exponent symbolically
            return smt.Pow(base, smt.Symbol(str(exponent), REAL))
        else:
            # Unsupported exponent type
            raise NotImplementedError(f"Unsupported exponent type: {type(exponent).__name__}")
    
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
    
    pow_factors = []
    nonpow_factors = []
    
    for factor in factors:
        if isinstance(factor, sympy.Pow):
            pow_factors.append(factor)
        else:
            nonpow_factors.append(factor)
    
    return pow_factors, nonpow_factors

def find_bases_from_formula(formula):
    #print(formula)
    bases = defaultdict(list)
    terms = get_summands(formula)
    n = symbols('n')
    for term in terms:
        term = sympy.powsimp(term, combine="base", force=True)
        #print("Term: ", term)
        base = 1
        poly = 1
        pow_factors, nonpow_factors = separate_pow_and_nonpow(term)
        for pow_term in pow_factors:
            b, exp = pow_term.as_base_exp()
            #print("Base:",b, "\t Exp:", exp)
            if str(exp) == "n":
                base *= b
            elif str(exp) == "-n":
                base *= 1/b
            elif len(exp.free_symbols) == 0:
                #print("This exponent has no free_symbols:", str(exp)) 
                poly *= b
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

program = Parser().parse_file(sys.argv[1])
program = normalize_program(program)
rec_builder = RecBuilder(program)
vars = []
if len(sys.argv) > 2:
    vars = sys.argv[2:]

roots: set = set()
var_dict = {}
for var in vars:
    #print(f"{var}")
    var_dict[var] = []
    recurr = rec_builder.get_recurrences(var)
    closed_form = RecurrenceSolver(recurr).get(var)
    n_sym = symbols('n')
    #closed_form = Piecewise((0, n_sym <= 0),(689**(1/2)*7**n_sym/10**n_sym, True))
    #print(closed_form)
    for i, (formula, _) in enumerate(closed_form.args):
        # i represents the ith closed form for this variable.
        piece = {
            "bases" : [],
            "coeffs" : []
        }
        bases_and_coefficients = get_bases_and_coefficients2(formula)
        #print(bases_and_coefficients)
        for j, (base, coeff) in enumerate(bases_and_coefficients):
            if base == "constant":
                base = "1.0"
            #print(f"\tBase {j}: {base}, Coeff: {coeff}")
            smt_base = to_smtlib(sympy_to_pysmt2(sympy.factor(sympy.radsimp(sympify(base)))), daggify=False)
            smt_base = convert_coordinates(smt_base)
            #print(smt_base)
            smt_coeff = to_smtlib(sympy_to_pysmt2(sympy.factor(sympy.radsimp(sympify(coeff)))), daggify=False)
            #print(f"c{i}r{j}: {smt_base}\nc{i}a{j}: {smt_coeff}")
            piece["bases"].append(smt_base)
            piece["coeffs"].append(smt_coeff)
            
            if base != "1.0":
                roots.add(smt_base)
        
        var_dict[var].append(piece)

json_string = json.dumps(var_dict)
with open('data.json', 'w', encoding='utf-8') as f:
    json.dump(var_dict, f, ensure_ascii=False, indent=4)
print(json_string)
#print(f"There were only {len(roots)} roots in all of the closed forms!")