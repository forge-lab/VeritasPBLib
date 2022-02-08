import unittest

from driver import Driver
from driver import CardinalityEncoding, RSResult
from pbcas.ast import Variable, Integer, Equals

class TestSequential(unittest.TestCase):
    @classmethod
    def makeTest(cls, fun, test_name, *args):
        def method(self):
            fun(self, test_name, *args)

        method.__name__ = "test_%s"%(test_name)
        setattr(cls, method.__name__, method)


    def geq(self, test_name, terms, degree, isSat):
        constraints = [terms >= Integer(degree)]
        driver = Driver(test_name)
        driver.encode(constraints, card_encoding = CardinalityEncoding.SEQUENTIAL)
        state, value = driver.minimize(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
        else:
            assert(state == RSResult.UNSAT.value)
        assert(degree == value)

    def eq(self, test_name, terms, degree, isSat):
        constraints = [Equals(terms,Integer(degree))]
        driver = Driver(test_name)
        driver.encode(constraints, card_encoding = CardinalityEncoding.SEQUENTIAL)
        state, value = driver.minimize(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
        else:
            assert(state == RSResult.UNSAT.value)
        assert(degree == value)

        state, value = driver.maximise(terms)
        if isSat:
            assert(state == RSResult.OPT.value)
        else:
            assert(state == RSResult.UNSAT.value)
        assert(degree == value)

def create(formulaPath, helper):
    def fun(self):
        helper(self, formulaPath)
    return fun

maxVars = 3

xs = [Variable(i) for i in range(1,maxVars + 1)]
for numVars in range(maxVars + 1):
    for degree in range(maxVars + 1):
        test_name = "seq_geq_base_%i_vars_%i_degree" % (numVars, degree)
        TestSequential.makeTest(TestSequential.geq, test_name, sum(xs[:numVars]),  degree, numVars >= degree)

# numVars = 3
# degree = 2

# test_name = "seq_eq_base_%i_vars_%i_degree" % (numVars, degree)
# TestSequential.makeTest(TestSequential.eq, test_name, sum(xs[:numVars]),  degree, numVars >= degree)