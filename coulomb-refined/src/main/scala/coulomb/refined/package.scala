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
  trait CoulombRefinedP2 {
    implicit def valueToRefinedPolicy[V1, U1, V2, P2, U2](implicit
        enable: coulomb.refined.policy.EnableUnsoundRefinedConversions,
        cf1: ConvertableFrom[V1],
        ct2: ConvertableTo[V2],
        vv2: Validate[V2, P2]): UnitConverterPolicy[V1, U1, Refined[V2, P2], U2] =
      new UnitConverterPolicy[V1, U1, Refined[V2, P2], U2] {
        def convert(v: V1, cu: ConvertableUnits[U1, U2]): Refined[V2, P2] = {
          val v2 = ct2.fromType[Rational](cf1.toType[Rational](v) * cu.coef)
          refineV[P2](v2).toOption.get
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
        enable: coulomb.refined.policy.EnableUnsoundRefinedConversions,
        cf1: ConvertableFrom[V1],
        ct2: ConvertableTo[V2],
        vv2: Validate[V2, P2]): UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] =
      new UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] {
        def convert(v: Refined[V1, P1], cu: ConvertableUnits[U1, U2]): Refined[V2, P2] = {
          val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
          refineV[P2](v2).toOption.get
        }
      }
  }
}

package object refined extends coulomb.refined.infra.CoulombRefinedP1 {
  object policy {
    trait EnableUnsoundRefinedConversions
    object unsoundRefinedConversions {
      implicit object enableUnsoundRefinedConversions extends
          EnableUnsoundRefinedConversions {}
    }
  }

  implicit def refinedPosAdd[V](implicit
      vv: Validate[V, Positive],
      gv: AdditiveSemigroup[V]): AdditiveSemigroup[Refined[V, Positive]] =
    new AdditiveSemigroup[Refined[V, Positive]] {
      def plus(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        refineV[Positive](gv.plus(x.value, y.value)).toOption.get
    }

  implicit def refinedNonNegAdd[V](implicit
      vv: Validate[V, NonNegative],
      gv: AdditiveMonoid[V]): AdditiveMonoid[Refined[V, NonNegative]] =
    new AdditiveMonoid[Refined[V, NonNegative]] {
      val zero: Refined[V, NonNegative] = refineV[NonNegative](gv.zero).toOption.get
      def plus(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        refineV[NonNegative](gv.plus(x.value, y.value)).toOption.get
    }

  implicit def refinedPosMul[V](implicit
      vv: Validate[V, Positive],
      gv: MultiplicativeGroup[V]): MultiplicativeGroup[Refined[V, Positive]] =
    new MultiplicativeGroup[Refined[V, Positive]] {
      val one: Refined[V, Positive] = refineV[Positive](gv.one).toOption.get
      def times(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        refineV[Positive](gv.times(x.value, y.value)).toOption.get
      def div(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        refineV[Positive](gv.div(x.value, y.value)).toOption.get
    }

  implicit def refinedNonNegMul[V](implicit
      vv: Validate[V, NonNegative],
      gv: MultiplicativeGroup[V]): MultiplicativeGroup[Refined[V, NonNegative]] =
    new MultiplicativeGroup[Refined[V, NonNegative]] {
      val one: Refined[V, NonNegative] = refineV[NonNegative](gv.one).toOption.get
      def times(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        refineV[NonNegative](gv.times(x.value, y.value)).toOption.get
      def div(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        refineV[NonNegative](gv.div(x.value, y.value)).toOption.get
    }

  implicit def refinedPosMulMonoid[V](implicit
      vv: Validate[V, Positive],
      noMG: NoImplicit[MultiplicativeGroup[V]],
      gv: MultiplicativeMonoid[V]): MultiplicativeMonoid[Refined[V, Positive]] =
    new MultiplicativeMonoid[Refined[V, Positive]] {
      val one: Refined[V, Positive] = refineV[Positive](gv.one).toOption.get
      def times(x: Refined[V, Positive], y: Refined[V, Positive]): Refined[V, Positive] =
        refineV[Positive](gv.times(x.value, y.value)).toOption.get
    }

  implicit def refinedNonNegMulMonoid[V](implicit
      vv: Validate[V, NonNegative],
      noMG: NoImplicit[MultiplicativeGroup[V]],
      gv: MultiplicativeMonoid[V]): MultiplicativeMonoid[Refined[V, NonNegative]] =
    new MultiplicativeMonoid[Refined[V, NonNegative]] {
      val one: Refined[V, NonNegative] = refineV[NonNegative](gv.one).toOption.get
      def times(x: Refined[V, NonNegative], y: Refined[V, NonNegative]): Refined[V, NonNegative] =
        refineV[NonNegative](gv.times(x.value, y.value)).toOption.get
    }

  implicit def refinedPosPosPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, Positive]): UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, Positive], U2] =
    new UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, Positive], U2] {
      def convert(v: Refined[V1, Positive], cu: ConvertableUnits[U1, U2]): Refined[V2, Positive] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        refineV[Positive](v2).toOption.get
      }
    }

  implicit def refinedPosNonNegPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, NonNegative]): UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, NonNegative], U2] =
    new UnitConverterPolicy[Refined[V1, Positive], U1, Refined[V2, NonNegative], U2] {
      def convert(v: Refined[V1, Positive], cu: ConvertableUnits[U1, U2]): Refined[V2, NonNegative] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        refineV[NonNegative](v2).toOption.get
      }
    }

  implicit def refinedNonNegNonNegPolicy[V1, U1, V2, U2](implicit
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, NonNegative]): UnitConverterPolicy[Refined[V1, NonNegative], U1, Refined[V2, NonNegative], U2] =
    new UnitConverterPolicy[Refined[V1, NonNegative], U1, Refined[V2, NonNegative], U2] {
      def convert(v: Refined[V1, NonNegative], cu: ConvertableUnits[U1, U2]): Refined[V2, NonNegative] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        refineV[NonNegative](v2).toOption.get
      }
    }
}
}
