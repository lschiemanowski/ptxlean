import unittest
from fractions import Fraction as F
from exact_reference import decode, eps, operation, rounded_word, pow2, dense, float_word


class ExactReferenceTests(unittest.TestCase):
    def test_ties_underflow_and_signed_zero(self):
        self.assertEqual(rounded_word(F(1)+pow2(-24)), 0x3f800000)
        self.assertEqual(rounded_word(F(1)+3*pow2(-24)), 0x3f800002)
        self.assertEqual(rounded_word(pow2(-150)), 0)
        self.assertEqual(rounded_word(-pow2(-150)), 0x80000000)
        self.assertEqual(operation('mul', 0x80000000, 0x3f800000)[0], 0x80000000)
        self.assertEqual(operation('add', 0x80000000, 0)[0], 0)
        self.assertEqual(operation('add', 0x80000000, 0x80000000)[0], 0x80000000)

    def test_boundaries_roundtrip(self):
        for x in [0, 0x80000000, 1, 0x80000001, 0x7fffff, 0x800000, 0x3f800000, 0x7f7fffff, 0xff7fffff]:
            self.assertEqual(rounded_word(decode(x), bool(x >> 31)), x)
        self.assertEqual(eps(F(0)), pow2(-150))
        self.assertEqual(eps(F(1)), pow2(-24))
        self.assertEqual(eps(F(1)-pow2(-24)), pow2(-25))

    def test_cancellation_separate_rounding(self):
        # (1+2^-23)*(1-2^-23) rounds to one, then adding -1 gives zero.
        product, _ = operation('mul', 0x3f800001, 0x3f7ffffe)
        self.assertEqual(operation('add', product, 0xbf800000)[0], 0)

    def test_relu_and_padding(self):
        case = dict(rows=2, columns=3, depth=2,
                    words=list(map(float_word, [1,2,3,1,2,3,-1,-2,-3,1,1])))
        self.assertEqual(dense(case)[0], [float_word(15), 0])

    def test_reject_outside_domain(self):
        with self.assertRaises(ValueError): decode(0x7f800000)
        with self.assertRaises(ValueError): operation('mul', 0x7f7fffff, float_word(2))


if __name__ == '__main__':
    unittest.main()
