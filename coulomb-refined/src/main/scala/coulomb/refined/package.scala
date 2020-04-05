/*
Copyright 2017-2020 Erik Erlandson

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

import spire.math.{ Rational, ConvertableFrom, ConvertableTo }
import spire.algebra._
import eu.timepit.refined._, eu.timepit.refined.api._, eu.timepit.refined.numeric._
import coulomb.unitops._
import coulomb.infra.NoImplicit

package coulomb {

package refined.infra {
  import coulomb.refined.policy._
  import coulomb.refined.CoulombRefinedException

  object enhance {
    implicit class EnhanceWithToRefined[V](v: V) {
      @inline def toRefined[P](implicit vvp: Validate[V, P]) = refineV[P](v) match {
        case Left(err) => throw CoulombRefinedException(err)
        case Right(ref) => ref
      }
    }
  }

  import enhance._

  trait CoulombRefinedP2 {
    implicit def valueToRefinedPolicy[V1, U1, V2, P2, U2](implicit
        enable: EnableUnsoundRefinedConversions,
        cf1: ConvertableFrom[V1],
        ct2: ConvertableTo[V2],
        vv2: Validate[V2, P2]): UnitConverterPolicy[V1, U1, Refined[V2, P2], U2] =
      new UnitConverterPolicy[V1, U1, Refined[V2, P2], U2] {
        def convert(v: V1, cu: ConvertableUnits[U1, U2]): Refined[V2, P2] = {
          val v2 = ct2.fromType[Rational](cf1.toType[Rational](v) * cu.coef)
          v2.toRefined[P2]
        }
      }

    implicit def refinedToValuePolicy[V1, P1, U1, V2, U2](implicit
        cf1: ConvertableFrom[V1],
        ct2: ConvertableTo[V2]): UnitConverterPolicy[Refined[V1, P1], U1, V2, U2] =
      new UnitConverterPolicy[Refined[V1, P1], U1, V2, U2] {
        def convert(v: Refined[V1, P1], cu: ConvertableUnits[U1, U2]): V2 = {
          ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        }
      }
  }

  trait CoulombRefinedP1 extends CoulombRefinedP2 {
    implicit def refinedToRefinedPolicy[V1, P1, U1, V2, P2, U2](implicit
        enable: EnableUnsoundRefinedConversions,
        cf1: ConvertableFrom[V1],
        ct2: ConvertableTo[V2],
        vv2: Validate[V2, P2]): UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] =
      new UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] {
        def convert(v: Refined[V1, P1], cu: ConvertableUnits[U1, U2]): Refined[V2, P2] = {
          val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
          v2.toRefined[P2]
        }
      }
  }
}

package object refined extends coulomb.refined.infra.CoulombRefinedP1 {
  import coulomb.refined.infra.enhance._

  object policy {
    trait EnableUnsoundRefinedConversions
    object unsoundRefinedConversions {
      implicit object enableUnsoundRefinedConversions extends
          EnableUnsoundRefinedConversions {}
    }
  }

  case class CoulombRefinedException(msg: String) extends Exception(msg)

  implicit def refinedPosAdd[V](implicit
      vv: Validate[V, Positive],
      gv: AdditiveSemigroup[V]): AdditiveSemigroup[Refined[V, Positive]] =
    new AdditiveSemigroup[Refined[V, Positive]] {
      def plus(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        gv.plus(x.value, y.value).toRefined[Positive]
    }

  implicit def refinedNonNegAdd[V](implicit
      vv: Validate[V, NonNegative],
      gv: AdditiveMonoid[V]): AdditiveMonoid[Refined[V, NonNegative]] =
    new AdditiveMonoid[Refined[V, NonNegative]] {
      val zero: Refined[V, NonNegative] = gv.zero.toRefined[NonNegative]
      def plus(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        gv.plus(x.value, y.value).toRefined[NonNegative]
    }

  implicit def refinedPosMul[V](implicit
      vv: Validate[V, Positive],
      gv: MultiplicativeGroup[V]): MultiplicativeGroup[Refined[V, Positive]] =
    new MultiplicativeGroup[Refined[V, Positive]] {
      val one: Refined[V, Positive] = gv.one.toRefined[Positive]
      def times(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        gv.times(x.value, y.value).toRefined[Positive]
      def div(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        gv.div(x.value, y.value).toRefined[Positive]
    }

  implicit def refinedNonNegMul[V](implicit
      vv: Validate[V, NonNegative],
      gv: MultiplicativeGroup[V]): MultiplicativeGroup[Refined[V, NonNegative]] =
    new MultiplicativeGroup[Refined[V, NonNegative]] {
      val one: Refined[V, NonNegative] = gv.one.toRefined[NonNegative]
      def times(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        gv.times(x.value, y.value).toRefined[NonNegative]
      def div(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        gv.div(x.value, y.value).toRefined[NonNegative]
    }

  implicit def refinedPosMulMonoid[V](implicit
      vv: Validate[V, Positive],
      noMG: NoImplicit[MultiplicativeGroup[V]],
      gv: MultiplicativeMonoid[V]): MultiplicativeMonoid[Refined[V, Positive]] =
    new MultiplicativeMonoid[Refined[V, Positive]] {
      val one: Refined[V, Positive] = gv.one.toRefined[Positive]
      def times(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        gv.times(x.value, y.value).toRefined[Positive]
    }

  implicit def refinedNonNegMulMonoid[V](implicit
      vv: Validate[V, NonNegative],
      noMG: NoImplicit[MultiplicativeGroup[V]],
      gv: MultiplicativeMonoid[V]): MultiplicativeMonoid[Refined[V, NonNegative]] =
    new MultiplicativeMonoid[Refined[V, NonNegative]] {
      val one: Refined[V, NonNegative] = gv.one.toRefined[NonNegative]
      def times(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        gv.times(x.value, y.value).toRefined[NonNegative]
    }

  implicit def refinedPosPosPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, Positive]): UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, Positive], U2] =
    new UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, Positive], U2] {
      def convert(v: Refined[V1, Positive], cu: ConvertableUnits[U1, U2]): Refined[V2, Positive] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        v2.toRefined[Positive]
      }
    }

  implicit def refinedPosNonNegPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, NonNegative]): UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, NonNegative], U2] =
    new UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, NonNegative], U2] {
      def convert(v: Refined[V1, Positive], cu: ConvertableUnits[U1, U2]): Refined[V2, NonNegative] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        v2.toRefined[NonNegative]
      }
    }

  implicit def refinedNonNegNonNegPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, NonNegative]): UnitConverterPolicy[Refined[V1, NonNegative], U1, Refined[V2, NonNegative], U2] =
    new UnitConverterPolicy[Refined[V1, NonNegative], U1, Refined[V2, NonNegative], U2] {
      def convert(v: Refined[V1, NonNegative], cu: ConvertableUnits[U1, U2]): Refined[V2, NonNegative] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        v2.toRefined[NonNegative]
      }
    }
}
}
