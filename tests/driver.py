from settings import vertiaspblib, roundingsat
import subprocess
from enum import Enum
import unittest
import itertools

from pbcas.ast import Variable, Integer, normalize_by_reduce, Mult, Add, Equals, Geq
from pbcas.opb_formula import OPBFormula
from pbcas.cnf_formula import CNFFormula
from veripb import run as veripb_verify
from pathlib import Path

class CardinalityEncoding(Enum):
    TOTALIZER = "0"
    SEQUENTIAL = "1"

class PBEncoding(Enum):
    GTE = "0"
    ADDER = "1"

def run_encoder(file_path, card_encoding = CardinalityEncoding.TOTALIZER, pb_encoding = PBEncoding.GTE):
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
    rs = subprocess.run([roundingsat, file_path], stdout = subprocess.PIPE, encoding="utf-8")

    if rs.returncode not in [20,30]:
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
    for assmt in itertools.product([0,1], repeat=len(values)):
        val = sum((a*b) for a,b in zip(assmt, values))
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

        method.__name__ = "test_%s"%(test_name)
        setattr(cls, method.__name__, method)


    def geq(self, test_name, coeffs, variables, degree):
        terms = Add([Mult([a, x]) for a,x in zip(coeffs,variables)])
        terms.isNormalized = True
        constraint = Geq(terms, Integer(degree))
        constraint.isNormalized = True
        opt = minimize(coeffs, degree)

        driver = Driver(test_name)
        driver.encode([constraint], card_encoding = self.card_encoding, pb_encoding = self.pb_encoding)
        state, value = driver.minimize(terms)
        if opt is not None:
            self.assertEqual(state, RSResult.OPT.value)
            self.assertEqual(value, opt)
        else:
            self.assertEqual(state, RSResult.UNSAT.value)


    def eq(self, test_name, coeffs, variables, degree):
        terms = Add([Mult([a, x]) for a,x in zip(coeffs,variables)])
        terms.isNormalized = True
        constraint = Geq(terms, Integer(degree))
        constraint.isNormalized = True
        opt = minimize(coeffs, degree)

        driver = Driver(test_name)
        driver.encode([constraint], card_encoding = self.card_encoding, pb_encoding = self.pb_encoding)
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

class Driver:
    def __init__(self, test_name):
        self.toEncode = Path("generated/%s.opb"%(test_name))
        self.proof = self.toEncode.with_suffix(".pbp")
        self.encoded = self.toEncode.with_suffix(".cnf")
        self.opt_min = self.toEncode.with_suffix(".min.opt.obp")
        self.opt_max = self.toEncode.with_suffix(".max.opt.obp")

        self.cnf = None

    def encode(self, constraints, card_encoding = CardinalityEncoding.TOTALIZER, pb_encoding = PBEncoding.GTE):
        formula = OPBFormula(constraints)
        with open(self.toEncode, "w") as file:
            formula.write(file)

        run_encoder(self.toEncode)

        with open(self.toEncode, "r") as opb:
            with open(self.proof, "r") as pbp:
                veripb_verify(opb, pbp)

        with open(self.encoded, "r") as file:
            self.cnf = CNFFormula.read(file)

    def minimize(self, objective):
        opb = OPBFormula(self.cnf.getConstraints(), objective = objective)

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

        opb = OPBFormula(self.cnf.getConstraints(), objective = flippedObj)

        with open(self.opt_max, "w") as file:
            opb.write(file)

        result, val = run_roundingsat(self.opt_max)
        return (result, -val if val is not None else None)

def main():
    print(minimize([-2,-2,-2],-8))




if __name__ == '__main__':
    main()