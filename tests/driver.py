from settings import vertiaspblib, roundingsat
import subprocess
from enum import Enum
import unittest
import itertools
import random
from copy import copy

from pbcas.ast import Variable, Integer, normalize_by_reduce, Mult, Add, Equals, Geq
from pbcas.opb_formula import OPBFormula
from pbcas.cnf_formula import CNFFormula
from veripb import run as veripb_verify
from pathlib import Path


class CardinalityEncoding(Enum):
    TOTALIZER = "1"
    SEQUENTIAL = "0"


class PBEncoding(Enum):
    GTE = "0"
    ADDER = "1"


def run_encoder(file_path, card_encoding=CardinalityEncoding.TOTALIZER, pb_encoding=PBEncoding.GTE):
    result = subprocess.run([vertiaspblib, "-card=" + card_encoding.value, "-pb=" + pb_encoding.value, "-verified", file_path],
                            stdout=subprocess.DEVNULL)

    if result.returncode != 0:
        raise EncoderInvalidReturnCode(result.returncode)


class RSResult(Enum):
    OPT = "OPTIMUM"
    SAT = "SATISFIABLE"
    UNSAT = "UNSATISFIABLE"


class InvalidReturnCode(RuntimeError):
    pass


class RoundingSATInvalidReturnCode(InvalidReturnCode):
    pass


class EncoderInvalidReturnCode(InvalidReturnCode):
    pass


def run_roundingsat(file_path):
    rs = subprocess.run([roundingsat, file_path],
                        stdout=subprocess.PIPE, encoding="utf-8")

    if rs.returncode not in [20, 30]:
        raise RoundingSATInvalidReturnCode(rs.returncode)

    stream = rs.stdout
    try:
        stream = stream.split("\n")
    except AttributeError as e:
        pass

    objectiveVal = None
    result = None

    for line in stream:
        if len(line) > 0:
            if line[0] == "o":
                objectiveVal = line.split()[1]
            if line[0] == "s":
                result = line.split()[1]
    return (result, int(objectiveVal) if objectiveVal is not None else None)


def minimize(values, bound):
    minimum = None
    for assmt in itertools.product([0, 1], repeat=len(values)):
        val = sum((a*b) for a, b in zip(assmt, values))
        if val >= bound:
            if minimum is None:
                minimum = val
            else:
                minimum = min(minimum, val)
    return minimum


class BaseTest(unittest.TestCase):
    card_encoding = None
    pb_encoding = None

    @classmethod
    def makeTest(cls, fun, test_name, *args):
        def method(self):
            fun(self, test_name, *args)

        method.__name__ = "test_%s" % (test_name)
        setattr(cls, method.__name__, method)

    def geq(self, test_name, coeffs, variables, degree):
        terms = Add([Mult([a, x]) for a, x in zip(coeffs, variables)])
        terms.isNormalized = True
        constraint = Geq(terms, Integer(degree))
        constraint.isNormalized = True
        opt = minimize(coeffs, degree)

        driver = Driver(test_name)
        driver.encode([constraint], card_encoding=self.card_encoding,
                      pb_encoding=self.pb_encoding)
        state, value = driver.minimize(terms)
        if opt is not None:
            self.assertEqual(state, RSResult.OPT.value)
            self.assertEqual(value, opt)
        else:
            self.assertEqual(state, RSResult.UNSAT.value)

    def eq(self, test_name, coeffs, variables, degree):
        terms = Add([Mult([a, x]) for a, x in zip(coeffs, variables)])
        terms.isNormalized = True
        constraint = Equals(terms, Integer(degree))
        constraint.isNormalized = True
        opt = minimize(coeffs, degree)
        if opt != degree:
            opt = None

        driver = Driver(test_name)
        driver.encode([constraint], card_encoding=self.card_encoding,
                      pb_encoding=self.pb_encoding)
        state, value = driver.minimize(terms)
        if opt is not None:
            self.assertEqual(state, RSResult.OPT.value)
            self.assertEqual(value, opt)
        else:
            self.assertEqual(state, RSResult.UNSAT.value)

        state, value = driver.maximize(terms)
        if opt is not None:
            self.assertEqual(state, RSResult.OPT.value)
            self.assertEqual(value, opt)
        else:
            self.assertEqual(state, RSResult.UNSAT.value)

    @classmethod
    def makeAllCardTests(cls, maxVars, factor=1):
        xs = [Variable(i) for i in range(1, maxVars + 1)]

        minVars = 1

        for numVars in range(minVars, maxVars + 1):
            for degree in range(maxVars + 1):
                degree *= factor
                coeffs = [factor] * numVars
                test_name = "%s_geq_base_%i_vars_%i_degree" % (
                    cls.encoding_name, numVars, degree)
                cls.makeTest(cls.geq, test_name, coeffs, xs, degree)

        for numVars in range(minVars, maxVars + 1):
            for degree in range(maxVars + 1):
                degree *= factor
                coeffs = [factor] * numVars
                test_name = "%s_eq_base_%i_vars_%i_degree" % (
                    cls.encoding_name, numVars, degree)
                cls.makeTest(cls.eq, test_name, coeffs, xs, degree)

        for numVars in range(minVars, maxVars + 1):
            for degree in range(-1, maxVars + 1):
                degree *= factor
                coeffs = [-factor] * numVars
                test_name = "%s_geq_neg_%i_vars_%i_degree" % (
                    cls.encoding_name, numVars, degree)

                cls.makeTest(cls.geq, test_name, coeffs, xs, -degree)

        for numVars in range(minVars, maxVars + 1):
            for degree in range(-1, maxVars + 1):
                degree *= factor
                coeffs = [-factor] * numVars
                test_name = "%s_eq_neg_%i_vars_%i_degree" % (
                    cls.encoding_name, numVars, degree)

                cls.makeTest(cls.eq, test_name, coeffs, xs, -degree)

    @classmethod
    def makeGeneralPBTests(cls):
        maxVars = 10
        xs = [Variable(i) for i in range(1, maxVars + 1)]

        test_name = "%s_geq_saturated_1" % (cls.encoding_name)
        cls.makeTest(cls.geq, test_name, [10, 2, 2], xs, 5)

        test_name = "%s_eq_saturated_1" % (cls.encoding_name)
        cls.makeTest(cls.eq, test_name, [10, 2, 2], xs, 5)

        test_name = "%s_geq_propagating_1" % (cls.encoding_name)
        cls.makeTest(cls.geq, test_name, [-3, -2, -2], xs, -2)

        test_name = "%s_eq_propagating_1" % (cls.encoding_name)
        cls.makeTest(cls.eq, test_name, [-3, -2, -2], xs, -2)

        maxVars = 3
        for k in range(2**(maxVars + 1)):
            test_name = "%s_geq_base_binary_%i" % (cls.encoding_name, k)
            cls.makeTest(cls.geq, test_name, [
                         2**j for j in range(maxVars)], xs, k)

        for k in range(2**(maxVars + 1)):
            test_name = "%s_eq_base_binary_%i" % (cls.encoding_name, k)
            cls.makeTest(cls.eq, test_name, [
                         2**j for j in range(maxVars)], xs, k)

        for k in range(-1, 2**(maxVars + 1)):
            test_name = "%s_geq_neg_binary_%i" % (cls.encoding_name, k)
            cls.makeTest(cls.geq, test_name,
                         [-2**j for j in range(maxVars)], xs, -k)

        for k in range(-1, 2**(maxVars + 1)):
            test_name = "%s_eq_neg_binary_%i" % (cls.encoding_name, k)
            cls.makeTest(cls.eq, test_name,
                         [-2**j for j in range(maxVars)], xs, -k)

        maxVars = 3
        for k in range(2**(maxVars + 1)):
            test_name = "%s_geq_base_binary_non_binary_%i" % (
                cls.encoding_name, k)
            # \sum_{i=1}^{k} 2^i x_i + \sum_{j=1}^{2^k} 2^k y_j >= 2^k + 1
            cls.makeTest(cls.geq, test_name,
                         [2**j for j in range(maxVars)] + [2**maxVars for j in range(2 ^ maxVars)], xs, k)

        random.seed(42)
        xs = copy(xs)
        for i in range(10):
            test_name = "%s_geq_random_%i" % (cls.encoding_name, i)
            coeffs = [random.randint(1, 10) for j in range(10)]
            k = random.randint(1, 20)
            random.shuffle(xs)
            cls.makeTest(cls.geq, test_name,
                         coeffs, copy(xs), k)

        for i in range(10):
            test_name = "%s_geq_random_large_coeff_%i" % (cls.encoding_name, i)
            coeffs = [random.randint(1, 10)*1000 for j in range(10)]
            k = random.randint(1, 20)*1000
            random.shuffle(xs)
            cls.makeTest(cls.geq, test_name,
                         coeffs, copy(xs), k)

        for i in range(2, 5):
            test_name = "%s_geq_%i_coeff_3_vars_%i_degree" % (
                cls.encoding_name, i, i + 1)
            coeffs = [i, i, i]
            k = i + 1
            cls.makeTest(cls.geq, test_name,
                         coeffs, copy(xs), k)


class Driver:
    def __init__(self, test_name):
        self.toEncode = Path("generated/%s.opb" % (test_name))
        self.proof = self.toEncode.with_suffix(".pbp")
        self.encoded = self.toEncode.with_suffix(".cnf")
        self.opt_min = self.toEncode.with_suffix(".min.opt.obp")
        self.opt_max = self.toEncode.with_suffix(".max.opt.obp")

        self.cnf = None

    def encode(self, constraints, card_encoding=CardinalityEncoding.TOTALIZER, pb_encoding=PBEncoding.GTE):
        formula = OPBFormula(constraints)
        with open(self.toEncode, "w") as file:
            formula.write(file)

        run_encoder(self.toEncode, card_encoding, pb_encoding)

        with open(self.toEncode, "r") as opb:
            with open(self.proof, "r") as pbp:
                veripb_verify(opb, pbp)

        with open(self.encoded, "r") as file:
            self.cnf = CNFFormula.read(file)

    def minimize(self, objective):
        opb = OPBFormula(self.cnf.getConstraints(), objective=objective)

        with open(self.opt_min, "w") as file:
            opb.write(file)

        return run_roundingsat(self.opt_min)

    def maximize(self, objective):
        if not getattr(objective, "isNormalized", False):
            objective = normalize_by_reduce(objective)[0]

        print(objective)

        terms = []
        for term in objective:
            coeff, var = term
            terms.append(Mult([-1 * coeff, var]))
        flippedObj = Add(terms)
        flippedObj.isNormalized = True

        opb = OPBFormula(self.cnf.getConstraints(), objective=flippedObj)

        with open(self.opt_max, "w") as file:
            opb.write(file)

        result, val = run_roundingsat(self.opt_max)
        return (result, -val if val is not None else None)


def main():
    print(minimize([-2, -2, -2], -8))


if __name__ == '__main__':
    main()
