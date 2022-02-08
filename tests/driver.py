from settings import vertiaspblib, roundingsat
import subprocess
from enum import Enum

from pbcas.ast import Variable, Integer
from pbcas.opb_formula import OPBFormula
from pbcas.cnf_formula import CNFFormula
from veripb import run as veripb_verify
from pathlib import Path

class CardinalityEncoding(Enum):
    TOTALIZER = "0"
    SEQUENTIAL = "1"

class PBEncoding(Enum):
    GTE = "0"
    ADDERT = "1"

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
        flippedObj = 0
        for term in objective:
            coeff, var = term
            flippedObj += -coeff * var

        opb = OPBFormula(self.cnf.getConstraints(), objective = flippedObj)

        with open(self.opt_max, "w") as file:
            opb.write(file)

        return run_roundingsat(self.opt_max)

def main():
    formula = OPBFormula()
    xs = [Variable(i) for i in range(1,10)]

    terms  = sum(xs)
    degree = 3

    constraints = [terms >= degree]

    driver = TestDriver("test")
    driver.encode(constraints)
    print(driver.minimize(terms))




if __name__ == '__main__':
    main()