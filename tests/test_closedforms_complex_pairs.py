import unittest

import sympy

from closedforms2 import (
    ComplexPairRegistry,
    extract_complex_pairs,
    get_bases_and_coefficients2,
    normalize_serialized_base_and_coeff,
    rewrite_complex_pairs,
    rewrite_negative_real_phases,
    sympy_to_pysmt2,
)


class ClosedFormsComplexPairTest(unittest.TestCase):
    def setUp(self):
        self.n = sympy.Symbol("n", integer=True)
        self.alpha = sympy.sympify("CRootOf('x**2 - 2*x + 2', 0)")
        self.alpha_bar = sympy.conjugate(self.alpha)

    def test_registry_emits_complex_pair_metadata(self):
        registry = ComplexPairRegistry()
        extract_complex_pairs(self.alpha**self.n + self.alpha_bar**self.n, registry)

        payload = registry.to_json()
        self.assertEqual(len(payload), 1)
        self.assertEqual(payload[0]["mag_name"], "_mag_0")
        self.assertEqual(payload[0]["ccos_name"], "_ccos_0")
        self.assertEqual(payload[0]["csin_name"], "_csin_0")
        self.assertEqual(payload[0]["mag_poly"], ["-2", "0", "1"])
        self.assertTrue(payload[0]["is_periodic"])
        self.assertEqual(payload[0]["period"], 8)

    def test_rewrite_uses_phase_placeholders(self):
        expr = (1 + sympy.I) * self.alpha**self.n + (1 - sympy.I) * self.alpha_bar**self.n
        registry = ComplexPairRegistry()
        extract_complex_pairs(expr, registry)
        rewritten = sympy.expand(rewrite_complex_pairs(expr, registry, self.n))
        entry = registry.get(self.alpha)

        expected = sympy.expand(
            2 * (entry["mag_symbol"] ** self.n) * (entry["ccos_symbol"] - entry["csin_symbol"])
        )
        self.assertEqual(sympy.simplify(rewritten - expected), 0)
        self.assertFalse(any(isinstance(node, sympy.ComplexRootOf) for node in sympy.preorder_traversal(rewritten)))
        self.assertFalse(rewritten.has(sympy.I))

    def test_bases_and_coefficients_use_mag_base(self):
        expr = self.alpha**self.n + self.alpha_bar**self.n
        registry = ComplexPairRegistry()
        extract_complex_pairs(expr, registry)
        rewritten = rewrite_complex_pairs(expr, registry, self.n)
        base_coeff_pairs = list(get_bases_and_coefficients2(rewritten))

        self.assertEqual(len(base_coeff_pairs), 1)
        base, coeff = base_coeff_pairs[0]
        self.assertEqual(str(base), "_mag_0")
        self.assertEqual(sympy.simplify(coeff - 2 * sympy.Symbol("_ccos_0", real=True)), 0)

    def test_explicit_complex_constant_registers_as_pair(self):
        expr = (1 + sympy.I) ** self.n + (1 - sympy.I) ** self.n
        registry = ComplexPairRegistry()
        extract_complex_pairs(expr, registry)

        payload = registry.to_json()
        self.assertEqual(len(payload), 1)
        self.assertEqual(payload[0]["mag_poly"], ["-2", "0", "1"])
        self.assertTrue(payload[0]["is_periodic"])
        self.assertEqual(payload[0]["period"], 8)

    def test_negative_real_root_rewrites_to_cosine_phase(self):
        expr = (-sympy.sqrt(2)) ** self.n
        registry = ComplexPairRegistry()
        rewritten = sympy.expand(rewrite_negative_real_phases(expr, registry, self.n))
        entry = registry.get_negative(-sympy.sqrt(2))

        expected = sympy.expand((entry["mag_symbol"] ** self.n) * entry["ccos_symbol"])
        self.assertEqual(sympy.simplify(rewritten - expected), 0)
        self.assertFalse(any(isinstance(node, sympy.ComplexRootOf) for node in sympy.preorder_traversal(rewritten)))

        payload = registry.to_json()
        self.assertEqual(len(payload), 1)
        self.assertEqual(payload[0]["period"], 2)
        self.assertEqual(payload[0]["cos_theta"], "-1")
        self.assertEqual(payload[0]["sin_theta"], "0")

    def test_negative_real_root_uses_mag_base_in_decomposition(self):
        expr = (-sympy.sqrt(2)) ** self.n
        registry = ComplexPairRegistry()
        rewritten = rewrite_negative_real_phases(expr, registry, self.n)
        base_coeff_pairs = list(get_bases_and_coefficients2(rewritten))

        self.assertEqual(len(base_coeff_pairs), 1)
        base, coeff = base_coeff_pairs[0]
        self.assertEqual(str(base), "_mag_0")
        self.assertEqual(sympy.simplify(coeff - sympy.Symbol("_ccos_0", real=True)), 0)

    def test_affine_exponent_is_split_before_serialization(self):
        alg = sympy.Symbol("_alg_0", real=True)
        expr = (alg + 2) ** (2 * self.n + 1)

        base_coeff_pairs = list(get_bases_and_coefficients2(expr))

        self.assertEqual(len(base_coeff_pairs), 1)
        base, coeff = base_coeff_pairs[0]
        self.assertEqual(sympy.simplify(base - (alg + 2) ** 2), 0)
        self.assertEqual(sympy.simplify(coeff - (alg + 2)), 0)
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(base)
            )
        )
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(coeff)
            )
        )

    def test_denominator_power_is_split_before_serialization(self):
        coeff_symbol = sympy.Symbol("c", real=True)
        expr = coeff_symbol / (sympy.Integer(2000000) ** self.n)

        base_coeff_pairs = list(get_bases_and_coefficients2(expr))

        self.assertEqual(len(base_coeff_pairs), 1)
        base, coeff = base_coeff_pairs[0]
        self.assertEqual(sympy.simplify(base - sympy.Rational(1, 2000000)), 0)
        self.assertEqual(sympy.simplify(coeff - coeff_symbol), 0)
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(base)
            )
        )
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(coeff)
            )
        )

    def test_nested_denominator_power_is_split_before_serialization(self):
        coeff_symbol = sympy.Symbol("c", real=True)
        denom_symbol = sympy.Symbol("d", real=True)
        mag_symbol = sympy.Symbol("_mag_0", real=True)
        expr = coeff_symbol * (mag_symbol ** self.n) / (denom_symbol * (sympy.Integer(2000000) ** self.n))

        base_coeff_pairs = list(get_bases_and_coefficients2(expr))

        self.assertEqual(len(base_coeff_pairs), 1)
        base, coeff = base_coeff_pairs[0]
        self.assertEqual(sympy.simplify(base - (mag_symbol / 2000000)), 0)
        self.assertEqual(sympy.simplify(coeff - (coeff_symbol / denom_symbol)), 0)
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(base)
            )
        )
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(coeff)
            )
        )

    def test_coefficient_normalization_removes_affine_power_after_factoring(self):
        mag_symbol = sympy.Symbol("_mag_0", real=True)
        base_expr = mag_symbol
        coeff_expr = sympy.Integer(3) * (sympy.Integer(2000000) ** self.n) * (sympy.Integer(2000000) ** (-2 * self.n - 7))

        normalized_base, normalized_coeff = normalize_serialized_base_and_coeff(base_expr, coeff_expr)

        self.assertEqual(sympy.simplify(normalized_base - (mag_symbol / 2000000)), 0)
        self.assertEqual(sympy.simplify(normalized_coeff - (sympy.Integer(3) * sympy.Integer(2000000) ** -7)), 0)
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(normalized_base)
            )
        )
        self.assertFalse(
            any(
                isinstance(node, sympy.Pow) and node.exp.has(self.n)
                for node in sympy.preorder_traversal(normalized_coeff)
            )
        )

        sympy_to_pysmt2(normalized_base)
        sympy_to_pysmt2(normalized_coeff)


if __name__ == "__main__":
    unittest.main()