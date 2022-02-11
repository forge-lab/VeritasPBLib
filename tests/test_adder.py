import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestAdder(BaseTest):
    card_encoding = CardinalityEncoding.SEQUENTIAL
    pb_encoding = PBEncoding.ADDER
    encoding_name = "adder"


# TestAdder.makeAllCardTests(maxVars = 3, factor = 2)
TestAdder.makeGeneralPBTests()