import unittest

from driver import Driver
from driver import CardinalityEncoding, RSResult
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestSequential(unittest.TestCase):
    @classmethod
    def makeTest(cls, fun, test_name, *args):
        def method(self):
            fun(self, test_name, *args)

        method.__name__ = "test_%s"%(test_name)
        setattr(cls, method.__name__, method)


    def geq(self, test_name, constraint, isSat):
        terms, degree = constraint
        if getattr(constraint, "isNormalized", False):
            terms.isNormalized = True
        degree = degree.value
        constraints = [constraint]

        driver = Driver(test_name)
        driver.encode(constraints, card_encoding = CardinalityEncoding.SEQUENTIAL)
        state, value = driver.minimize(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
            assert(degree == value)
        else:
            assert(state == RSResult.UNSAT.value)


    def eq(self, test_name, constraint, isSat):
        terms, degree = constraint
        degree = degree.value
        constraints = [constraint]

        driver = Driver(test_name)
        driver.encode(constraints, card_encoding = CardinalityEncoding.SEQUENTIAL)
        state, value = driver.minimize(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
            assert(degree == value)
        else:
            assert(state == RSResult.UNSAT.value)

        state, value = driver.maximize(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
            assert(degree == value)
        else:
            assert(state == RSResult.UNSAT.value)


def create(formulaPath, helper):
    def fun(self):
        helper(self, formulaPath)
    return fun

maxVars = 3

xs = [Variable(i) for i in range(1,maxVars + 1)]

for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        test_name = "seq_geq_base_%i_vars_%i_degree" % (numVars, degree)
        TestSequential.makeTest(TestSequential.geq, test_name, Geq(sum(xs[:numVars]), Integer(degree)), numVars >= degree)

for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        test_name = "seq_eq_base_%i_vars_%i_degree" % (numVars, degree)
        TestSequential.makeTest(TestSequential.eq, test_name, Equals(sum(xs[:numVars]),  Integer(degree)), numVars >= degree)

for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        test_name = "seq_geq_neg_%i_vars_%i_degree" % (numVars, degree)

        constraint = Geq(Add([Mult([-1, x]) for x in xs[:numVars]]), Integer(-degree))
        constraint.isNormalized = True

        TestSequential.makeTest(TestSequential.geq, test_name, constraint, numVars >= degree)


numVars = 3
degree = 2