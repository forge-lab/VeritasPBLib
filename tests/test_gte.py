import unittest

from driver import Driver, BaseTest
from driver import CardinalityEncoding, PBEncoding
from pbcas.ast import Variable

class TestGTE(BaseTest):
    card_encoding = CardinalityEncoding.SEQUENTIAL
    pb_encoding = PBEncoding.GTE
    encoding_name = "gte"


TestGTE.makeAllEqCoefsTests(maxVars = 3, factor = 2)
TestGTE.makeGeneralPBTests()