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

package coulomb.refined

import utest._

import spire.std.any._
import spire.algebra._

import eu.timepit.refined._
import eu.timepit.refined.api._
import eu.timepit.refined.numeric._

import coulomb._
import coulomb.si._

import coulomb.validators.CoulombValidators._

object RefinedTests extends TestSuite {
  val tests = Tests {
    test("refined NonNegative") {
      assert(refineMV[NonNegative](0.0).withUnit[Meter].isValidQ[Refined[Double, NonNegative], Meter](0))
    }
  }
}
