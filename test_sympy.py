import sympy
n = sympy.Symbol('n', integer=True)
alpha = sympy.sympify("CRootOf(x**2 - 2*x + 2, 0)")
conj_alpha = sympy.conjugate(alpha)
expr = (1+sympy.I)*alpha**n + (1-sympy.I)*conj_alpha**n
print('1) Conjugate(alpha):', conj_alpha)
try:
    expanded = sympy.expand_complex(expr)
    print('2) expand_complex(expr):', expanded)
except Exception as e:
    print('2) expand_complex(expr): Failed with', type(e).__name__, ':', e)
re_part = sympy.re(expr)
print('Re(expr):', re_part)
print('3) sin/cos in Re(expr):', any(x in str(re_part) for x in ['sin', 'cos']))
