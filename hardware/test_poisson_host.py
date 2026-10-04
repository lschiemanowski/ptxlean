"""Host control tests run the real Python driver with explicitly mocked kernels.

These check scheduling and status handling, not numerical or GPU behavior.
check_poisson_host.py also compares these cases with the proved Lean host model.
"""
import itertools
import math
import struct
import unittest

from poisson_runtime import solve


def bits(value):
    return struct.unpack('<Q', struct.pack('<d', value))[0]


def number(word):
    return struct.unpack('<d', struct.pack('<Q', word))[0]


def case(**changes):
    value = dict(maximum=3, interval=2, norm=bits(2.), tolerance=bits(.5),
                 residual=bits(1.), active=1, broken=0)
    value.update(changes)
    return value


class MockSession:
    def __init__(self, values):
        self.values = values
        self.launch_log = []

    def launch(self, name):
        self.launch_log.append(name)

    def read(self, name):
        if name in ('applied', 'x'):
            return []  # Read-only diagnostics have no effect on host control.
        return [self.scalar(name)]

    def scalar(self, name):
        key = 'norm' if name == 'rhs_norm' else name
        value = self.values[key]
        return value if name in ('active', 'broken') else number(value)

    def audit_storage(self):
        return 'mock'


def python_result(value):
    result = solve(MockSession(value), dict(maxiter=value['maximum'], check_every=value['interval']))
    return dict(launches=result['launches'], iterations=result['iterations'], reason=result['reason'],
                restarts=result['restarts'], residual=bits(result['true_residual_norm']),
                checks=[dict(c, residual=bits(c['residual'])) for c in result['checks']])


def scenarios():
    """Cartesian branch controls plus exceptional initial and residual values."""
    result = [case(maximum=m, interval=i, residual=bits(r), active=a, broken=b)
              for m, i, r, a, b in itertools.product((0, 1, 3), (1, 2, 5),
                                                    (.25, 1., math.inf, math.nan), (0, 7), (0, 3))]
    result += [case(norm=bits(n), tolerance=bits(t))
               for n, t in itertools.product((0., -0., .25, 2., math.inf, math.nan),
                                              (0., .5, math.inf, math.nan))]
    return result


class HostControl(unittest.TestCase):
    def test_final_iteration_checks_even_off_interval(self):
        value = python_result(case(interval=10))
        self.assertEqual([c['iteration'] for c in value['checks']], [3])
        self.assertEqual(value['reason'], 'maxiter')

    def test_convergence_precedes_broken_flag(self):
        value = python_result(case(residual=bits(.25), broken=3, active=0))
        self.assertEqual((value['iterations'], value['reason'], value['restarts']), (2, 'converged', 0))

    def test_nonfinite_precedes_tolerance(self):
        value = python_result(case(norm=bits(math.inf), tolerance=bits(math.inf)))
        self.assertEqual((value['iterations'], value['reason']), (0, 'breakdown'))
        value = python_result(case(residual=bits(math.nan)))
        self.assertEqual(value['reason'], 'breakdown')

    def test_final_iteration_still_restarts(self):
        value = python_result(case(maximum=1, interval=10, active=0))
        self.assertEqual((value['iterations'], value['reason'], value['restarts']), (1, 'maxiter', 1))
        self.assertEqual(value['launches'][-3:], ['restart_vectors', 'dot_rz', 'restart_flag'])

    def test_zero_budget_still_initializes(self):
        value = python_result(case(maximum=0))
        self.assertEqual(value['launches'], ['element_probe', 'assemble_probe', 'initialize', 'dot_rhs', 'dot_rz', 'start'])
        self.assertEqual(value['reason'], 'maxiter')
        self.assertEqual(value['checks'], [])

    def test_broken_precedes_restart(self):
        value = python_result(case(active=0, broken=3))
        self.assertEqual((value['reason'], value['restarts']), ('breakdown', 0))


if __name__ == '__main__':
    unittest.main()
