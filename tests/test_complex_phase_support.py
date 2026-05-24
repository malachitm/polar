import unittest

import sympy

from utils import (
    complex_root_metadata,
    mag_poly_from_complex_root,
    phase_metadata,
    poly_to_int_coeffs,
)


class ComplexPhaseSupportTest(unittest.TestCase):
    def test_negative_real_axis_has_period_two(self):
        metadata = phase_metadata(sympy.Integer(-1), sympy.Integer(0))
        self.assertTrue(metadata["is_periodic"])
        self.assertEqual(metadata["period"], 2)
        self.assertEqual(sympy.simplify(metadata["cos_theta"] + 1), 0)
        self.assertEqual(metadata["sin_theta"], 0)

    def test_sixty_degree_phase_has_period_six(self):
        metadata = phase_metadata(sympy.Rational(1, 2), sympy.sqrt(3) / 2)
        self.assertTrue(metadata["is_periodic"])
        self.assertEqual(metadata["period"], 6)
        self.assertEqual(sympy.simplify(metadata["cos_theta"] - sympy.Rational(1, 2)), 0)
        self.assertEqual(sympy.simplify(metadata["sin_theta"] - sympy.sqrt(3) / 2), 0)

    def test_non_periodic_phase_is_not_flagged(self):
        metadata = phase_metadata(sympy.Integer(1), sympy.Integer(2))
        self.assertFalse(metadata["is_periodic"])
        self.assertEqual(metadata["period"], 0)

    def test_complex_root_magnitude_polynomial(self):
        root = sympy.sympify("CRootOf('x**2 - 2*x + 2', 0)")
        poly_expr, low, high = mag_poly_from_complex_root(root)
        self.assertEqual(poly_to_int_coeffs(poly_expr), ["-2", "0", "1"])
        self.assertLessEqual(low, sympy.sqrt(2))
        self.assertLessEqual(sympy.sqrt(2), high)

    def test_complex_root_metadata_carries_period(self):
        root = sympy.sympify("CRootOf('x**2 - 2*x + 2', 0)")
        metadata = complex_root_metadata(root)
        self.assertEqual(poly_to_int_coeffs(metadata["mag_poly"]), ["-2", "0", "1"])
        self.assertTrue(metadata["is_periodic"])
        self.assertEqual(metadata["period"], 8)


if __name__ == "__main__":
    unittest.main()