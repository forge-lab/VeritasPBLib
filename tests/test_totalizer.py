import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestTotalizer(BaseTest):
    card_encoding = CardinalityEncoding.TOTALIZER
    pb_encoding = PBEncoding.GTE


maxVars = 3

xs = [Variable(i) for i in range(1,maxVars + 1)]

factor = 1

for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "totalizer_geq_base_%i_vars_%i_degree" % (numVars, degree)
        TestTotalizer.makeTest(TestTotalizer.geq, test_name, coeffs, xs, degree)

for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "totalizer_eq_base_%i_vars_%i_degree" % (numVars, degree)
        TestTotalizer.makeTest(TestTotalizer.geq, test_name, coeffs, xs, degree)

for numVars in range(maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "totalizer_geq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestTotalizer.makeTest(TestTotalizer.geq, test_name, coeffs, xs, -degree)

for numVars in range(maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "totalizer_eq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestTotalizer.makeTest(TestTotalizer.geq, test_name, coeffs, xs, -degree)