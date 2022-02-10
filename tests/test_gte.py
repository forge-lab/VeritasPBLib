import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable

class TestGTE(BaseTest):
    card_encoding = CardinalityEncoding.SEQUENTIAL
    pb_encoding = PBEncoding.GTE


maxVars = 3

xs = [Variable(i) for i in range(1,maxVars + 1)]

factor = 2

for numVars in range(1, maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "gte_geq_base_%i_vars_%i_degree" % (numVars, degree)
        TestGTE.makeTest(TestGTE.geq, test_name, coeffs, xs, degree)

for numVars in range(1, maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "gte_eq_base_%i_vars_%i_degree" % (numVars, degree)
        TestGTE.makeTest(TestGTE.geq, test_name, coeffs, xs, degree)

for numVars in range(1, maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "gte_geq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestGTE.makeTest(TestGTE.geq, test_name, coeffs, xs, -degree)

for numVars in range(1, maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "gte_eq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestGTE.makeTest(TestGTE.geq, test_name, coeffs, xs, -degree)

test_name = "gte_saturated_1"
TestGTE.makeTest(TestGTE.geq, test_name, [10, 2, 2], xs, 5)

test_name = "gte_propagating_1"
TestGTE.makeTest(TestGTE.geq, test_name, [-3, -2, -2], xs, -2)