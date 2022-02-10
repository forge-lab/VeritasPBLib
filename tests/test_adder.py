import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestAdder(BaseTest):
    card_encoding = CardinalityEncoding.SEQUENTIAL
    pb_encoding = PBEncoding.ADDER


maxVars = 3

xs = [Variable(i) for i in range(1,maxVars + 1)]

factor = 2

for numVars in range(1, maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "adder_geq_base_%i_vars_%i_degree" % (numVars, degree)
        TestAdder.makeTest(TestAdder.geq, test_name, coeffs, xs, degree)

for numVars in range(1, maxVars + 1):
    for degree in range(maxVars + 1):
        degree *= factor
        coeffs = [factor] * numVars
        test_name = "adder_eq_base_%i_vars_%i_degree" % (numVars, degree)
        TestAdder.makeTest(TestAdder.geq, test_name, coeffs, xs, degree)

for numVars in range(1, maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "adder_geq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestAdder.makeTest(TestAdder.geq, test_name, coeffs, xs, -degree)

for numVars in range(1, maxVars + 1):
    for degree in range(-1, maxVars + 1):
        degree *= factor
        coeffs = [-factor] * numVars
        test_name = "adder_eq_neg_%i_vars_%i_degree" % (numVars, degree)

        TestAdder.makeTest(TestAdder.geq, test_name, coeffs, xs, -degree)

test_name = "adder_saturated_1"
TestAdder.makeTest(TestAdder.geq, test_name, [10, 2, 2], xs, 5)

test_name = "adder_propagating_1"
TestAdder.makeTest(TestAdder.geq, test_name, [-3, -2, -2], xs, -2)