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
import spire.util.Opt
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

  object soundcheck {
    trait SoundAddAlgebra[P]
    trait SoundMulAlgebra[P]
    implicit object posIsSoundAdd extends SoundAddAlgebra[Positive] {}
    implicit object nonNegIsSoundAdd extends SoundAddAlgebra[NonNegative] {}
    implicit object posIsSoundMul extends SoundMulAlgebra[Positive] {}
    implicit object nonNegIsSoundMul extends SoundMulAlgebra[NonNegative] {}    
  }

  import soundcheck._

  trait CoulombRefinedP1 {
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
}

package object refined extends coulomb.refined.infra.CoulombRefinedP1 {
  import coulomb.refined.infra.enhance._
  import coulomb.refined.infra.soundcheck._

  object policy {
    trait EnableUnsoundRefinedConversions
    object unsoundRefinedConversions {
      implicit object enableUnsoundRefinedConversions extends
          EnableUnsoundRefinedConversions {}
    }
  }
  import policy._

  case class CoulombRefinedException(msg: String) extends Exception(msg)

  implicit def refinedAddSGSound[V, P](implicit
      noAG: NoImplicit[AdditiveGroup[Refined[V, P]]],
      ps: SoundAddAlgebra[P],
      vv: Validate[V, P],
      gv: AdditiveSemigroup[V]): AdditiveSemigroup[Refined[V, P]] =
    new AdditiveSemigroup[Refined[V, P]] {
      def plus(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.plus(x.value, y.value).toRefined[P]
    }

  // additive group (subtraction) is unsound for all predicates
  implicit def refinedAddGroupUnsound[V, P](implicit
      enable: EnableUnsoundRefinedConversions,
      vv: Validate[V, P],
      gv: AdditiveGroup[V]): AdditiveGroup[Refined[V, P]] =
    new AdditiveGroup[Refined[V, P]] {
      val zero: Refined[V, P] = gv.zero.toRefined[P]
      def plus(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.plus(x.value, y.value).toRefined[P]
      override def minus(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.minus(x.value, y.value).toRefined[P]
      def negate(x: Refined[V, P]): Refined[V, P] =
        gv.negate(x.value).toRefined[P]
    }

  implicit def refinedMulSGSound[V, P](implicit
      noMG: NoImplicit[MultiplicativeGroup[Refined[V, P]]],
      ps: SoundMulAlgebra[P],
      vv: Validate[V, P],
      gv: MultiplicativeSemigroup[V]): MultiplicativeSemigroup[Refined[V, P]] =
    new MultiplicativeSemigroup[Refined[V, P]] {
      def times(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.times(x.value, y.value).toRefined[P]
    }

  implicit def refinedMulGroupSound[V, P](implicit
      ps: SoundMulAlgebra[P],
      vv: Validate[V, P],
      gv: MultiplicativeGroup[V]): MultiplicativeGroup[Refined[V, P]] =
    new MultiplicativeGroup[Refined[V, P]] {
      val one: Refined[V, P] = gv.one.toRefined[P]
      def times(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.times(x.value, y.value).toRefined[P]
      def div(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        gv.div(x.value, y.value).toRefined[P]
    }

  implicit def refinedTDSound[V, P](implicit
      noMG: NoImplicit[MultiplicativeGroup[Refined[V, P]]],
      ps: SoundMulAlgebra[P],
      vv: Validate[V, P],
      td: TruncatedDivision[V]): TruncatedDivision[Refined[V, P]] =
    new TruncatedDivision[Refined[V, P]] {
      def toBigIntOpt(x: Refined[V, P]): Opt[BigInt] = td.toBigIntOpt(x.value)
      def compare(x: Refined[V, P], y: Refined[V, P]): Int = td.compare(x.value, y.value)
      def abs(x: Refined[V, P]): Refined[V, P] = td.abs(x.value).toRefined[P]
      def signum(x: Refined[V, P]): Int = td.signum(x.value)
      def tquot(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        td.tquot(x.value, y.value).toRefined[P]
      def tmod(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        td.tmod(x.value, y.value).toRefined[P]
      def fquot(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        td.fquot(x.value, y.value).toRefined[P]
      def fmod(x: Refined[V, P], y: Refined[V, P]): Refined[V, P] =
        td.fmod(x.value, y.value).toRefined[P]
    }

  implicit def refinedToRefinedSound[V1, P1, U1, V2, P2, U2](implicit
      s12: Inference[P1, P2],
      cf1: ConvertableFrom[V1],
      ct2: ConvertableTo[V2],
      vv2: Validate[V2, P2]): UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] =
    new UnitConverterPolicy[Refined[V1, P1], U1, Refined[V2, P2], U2] {
      def convert(v: Refined[V1, P1], cu: ConvertableUnits[U1, U2]): Refined[V2, P2] = {
        val v2 = ct2.fromType[Rational](cf1.toType[Rational](v.value) * cu.coef)
        v2.toRefined[P2]
      }
    }

  implicit def refinedToRefinedUnsound[V1, P1, U1, V2, P2, U2](implicit
      enable: EnableUnsoundRefinedConversions,
      u12: NoImplicit[Inference[P1, P2]],
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
