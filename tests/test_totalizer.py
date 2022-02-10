import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable, Integer, Equals, Geq, Add, Mult

class TestTotalizer(BaseTest):
    card_encoding = CardinalityEncoding.TOTALIZER
    pb_encoding = PBEncoding.GTE
    encoding_name = "totalizer"


TestTotalizer.makeAllEqCoefsTests(maxVars = 3, factor = 1)
