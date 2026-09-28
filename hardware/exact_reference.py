"""Independent rational binary32 arithmetic and dense-forward error accounting.

No host float arithmetic enters the expected result or bound. This is executable
validation of the existing formulas, not a new Lean proof of this Python code.
"""
from fractions import Fraction as F
import struct


def pow2(e):
    return F(2**e) if e >= 0 else F(1, 2**-e)


MAX_FINITE = (2-pow2(-23))*pow2(127)


def decode(word):
    exponent, fraction = (word >> 23) & 255, word & 0x7fffff
    if exponent == 255:
        raise ValueError("nonfinite input is outside the accuracy domain")
    value = F(fraction)*pow2(-149) if exponent == 0 else F((1 << 23)+fraction)*pow2(exponent-150)
    return -value if word >> 31 else value


def exponent(value):
    """floor(log2(abs(value))) for a nonzero rational."""
    value = abs(value)
    e = value.numerator.bit_length()-value.denominator.bit_length()
    return e-1 if value < pow2(e) else e


def eps(value):
    return pow2(max(-149, exponent(value)-23)-1) if value else pow2(-150)


def rounded_word(value, negative_zero=False):
    if abs(value) > MAX_FINITE:
        raise ValueError("exact intermediate exceeds the formal finite-range guard")
    sign = 0x80000000 if value < 0 or (value == 0 and negative_zero) else 0
    if not value:
        return sign
    unit = max(-149, exponent(value)-23)
    scaled = abs(value)/pow2(unit)
    q, r = divmod(scaled.numerator, scaled.denominator)
    q += 2*r > scaled.denominator or (2*r == scaled.denominator and q % 2 == 1)
    if q == 0:
        return sign
    if unit == -149 and q < 1 << 23:
        return sign | q
    if q >= 1 << 24:
        q >>= 1
        unit += 1
    return sign | ((unit+150) << 23) | (q-(1 << 23))


def operation(kind, a, b):
    av, bv = decode(a), decode(b)
    exact = av*bv if kind == "mul" else av+bv
    neg = bool((a ^ b) >> 31) if kind == "mul" else a == b == 0x80000000
    return rounded_word(exact, neg), eps(exact)


def dense(case):
    m, n, depth = case['rows'], case['columns'], case['depth']
    words = case['words']
    if len(words) != n+m*n+m:
        raise ValueError('input storage length mismatch')
    values = list(map(decode, words))
    outputs, ideals, allowances, torch_allowances = [], [], [], []
    for row in range(m):
        products = [operation('mul', words[n+row*n+j], words[j]) for j in range(n)]
        products += [(0, eps(F(0)))]*((1 << depth)-n)
        while len(products) > 1:
            reduced = []
            for i in range(0, len(products), 2):
                a, ea = products[i]; b, eb = products[i+1]
                result, allowance = operation('add', a, b)
                reduced.append((result, ea+eb+allowance))
            products = reduced
        dot, allowance = products[0]
        affine, bias_allowance = operation('add', dot, words[n+m*n+row])
        out = 0 if affine >> 31 else affine
        terms = [values[n+row*n+j]*values[j] for j in range(n)]
        ideal = max(sum(terms, F(0))+values[n+m*n+row], F(0))
        bound = allowance+bias_allowance
        assert abs(decode(out)-ideal) <= bound
        # Diagnostic envelope for ordinary FP32 PyTorch, NOT a proved backend bound.
        # Counts enough rounding steps for a dot and bias; permits subnormal error.
        k = 2*n+2
        u = pow2(-24)
        diagnostic = (k*u*(sum(map(abs, terms), F(0))+abs(values[n+m*n+row]))+k*pow2(-150))/(1-k*u)
        outputs.append(out); ideals.append(ideal); allowances.append(bound); torch_allowances.append(diagnostic)
    return outputs, ideals, allowances, torch_allowances


def float_word(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


def word_float(x):
    return struct.unpack('<f', struct.pack('<I', x))[0]
