package coulomb.parser

import shapeless.{ ::, HNil }

import spire.math._
import spire.std.any._

import singleton.ops._

import utest._

import coulomb._
import coulomb.unitops._
import coulomb.si._
import coulomb.siprefix._
import coulomb.mks._
import coulomb.accepted._
import coulomb.time._
import coulomb.info._
import coulomb.binprefix._
import coulomb.us._
import coulomb.temp._

import coulomb.validators.CoulombValidators._

object ConfigIntegration {
  import com.typesafe.config.ConfigFactory
  import coulomb.parser.QuantityParser
  import coulomb.typesafeconfig._

  val confTS = ConfigFactory.parseString("""
    "duration" = "60 second"
    "memory" = "100 gigabyte"
    "bandwidth" = "10 megabyte / second"
  """)

  private val qp = QuantityParser[Byte :: Second :: Giga :: Mega :: HNil]

  val conf = confTS.withQuantityParser(qp)
}

object QuantityParserTests extends TestSuite {
  import coulomb.parser.QuantityParser
  import ConfigIntegration._

  val tests = Tests {
    test("return configured unit quantities") {
      assert(
        conf.getQuantity[Double, Second]("duration").get.isValidQ[Double, Second](60),
        conf.getQuantity[Int, Giga %* Byte]("memory").get.isValidQ[Int, Giga %* Byte](100),
        conf.getQuantity[Float, Mega %* Byte %/ Second]("bandwidth").get.isValidQ[Float, Mega %* Byte %/ Second](10)
      )
    }

    test("return convertable unit quantities") {
      assert(
        conf.getQuantity[Double, Minute]("duration").get.isValidQ[Double, Minute](1),
        conf.getQuantity[Int, Giga %* Bit]("memory").get.isValidQ[Int, Giga %* Bit](800),
        conf.getQuantity[Float, Giga %* Bit %/ Minute]("bandwidth").get.isValidQ[Float, Giga %* Bit %/ Minute](4.8)
      )
    }

    test("fail on incompatible units") {
      val try1 = conf.getQuantity[Double, Meter]("duration")
      assert(try1.isInstanceOf[scala.util.Failure[_]])
    }

    test("support ser/de") {
      import coulomb.scalatest.serde._
      val expr = "3.14 gigabyte / second"
      val qp1 = QuantityParser[Byte :: Second :: Giga :: Mega :: HNil]
      val t1 = qp1[Float, Giga %* Byte %/ Second](expr).get
      val qp2 = roundTripSerDe(qp1)
      val t2 = qp2[Float, Giga %* Byte %/ Second](expr).get
      assert(t1 === t2)
      assert(t2.isValidQ[Float, Giga %* Byte %/ Second](3.14))
    }
  }
}
