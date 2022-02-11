import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestSequential(BaseTest):
    card_encoding = CardinalityEncoding.SEQUENTIAL
    pb_encoding = PBEncoding.GTE
    encoding_name = "sequential"


TestSequential.makeAllCardTests(maxVars = 3)
