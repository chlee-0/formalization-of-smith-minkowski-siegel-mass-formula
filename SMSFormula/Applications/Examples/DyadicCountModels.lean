import SMSFormula.Applications.Examples.Inputs
import SMSFormula.StandardAxiomsGuard

/-!
Explicit finite models for dyadic local-density calculations.
These counts do not identify the native local-dual quotient or its depth.
-/

namespace MassFormulaReleaseExamples

abbrev TernaryDyadicVector := Fin 8 × Fin 4 × Fin 8

def ternaryDyadicQ (v : TernaryDyadicVector) : ℤ :=
  (v.1 : ℤ)^2 + 2 * (v.2.1 : ℤ)^2 + 11 * (v.2.2 : ℤ)^2

def ternaryDyadicPair (v w : TernaryDyadicVector) : ℤ :=
  (v.1 : ℤ) * w.1 + 2 * (v.2.1 : ℤ) * w.2.1 + 11 * (v.2.2 : ℤ) * w.2.2

def ternaryDyadicShell (a : ℤ) : Finset TernaryDyadicVector :=
  Finset.univ.filter fun v => ternaryDyadicQ v % 16 = a % 16

def ternaryDyadicModelFamilies : Finset ((TernaryDyadicVector × TernaryDyadicVector) ×
    TernaryDyadicVector) :=
  ((ternaryDyadicShell 1 ×ˢ ternaryDyadicShell 2) ×ˢ ternaryDyadicShell 11).filter
    fun v => ternaryDyadicPair v.1.1 v.1.2 % 8 = 0 ∧
      ternaryDyadicPair v.1.1 v.2 % 8 = 0 ∧ ternaryDyadicPair v.1.2 v.2 % 8 = 0

theorem ternaryDyadicShell_one_card : (ternaryDyadicShell 1).card = 16 := by decide
theorem ternaryDyadicShell_two_card : (ternaryDyadicShell 2).card = 16 := by decide
theorem ternaryDyadicShell_eleven_card : (ternaryDyadicShell 11).card = 16 := by decide

theorem ternaryDyadicModelFamilies_card : ternaryDyadicModelFamilies.card = 128 := by
  decide +kernel

abbrev A4DyadicVector := Fin 4 → ZMod 2

def a4DyadicQ (v : A4DyadicVector) : ZMod 2 :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 - v 0 * v 1 - v 1 * v 2 - v 2 * v 3

def a4DyadicPair (v w : A4DyadicVector) : ZMod 2 :=
  -(v 0 * w 1 + v 1 * w 0 + v 1 * w 2 + v 2 * w 1 + v 2 * w 3 + v 3 * w 2)

def a4DyadicShell : Finset A4DyadicVector := Finset.univ.filter fun v => a4DyadicQ v = 1

def a4DyadicModelFamilies : Finset ((A4DyadicVector × A4DyadicVector) ×
    (A4DyadicVector × A4DyadicVector)) :=
  ((a4DyadicShell ×ˢ a4DyadicShell) ×ˢ (a4DyadicShell ×ˢ a4DyadicShell)).filter fun v =>
    a4DyadicPair v.1.1 v.1.2 = 1 ∧ a4DyadicPair v.1.1 v.2.1 = 0 ∧
      a4DyadicPair v.1.1 v.2.2 = 0 ∧ a4DyadicPair v.1.2 v.2.1 = 1 ∧
      a4DyadicPair v.1.2 v.2.2 = 0 ∧ a4DyadicPair v.2.1 v.2.2 = 1

theorem a4DyadicShell_card : a4DyadicShell.card = 10 := by decide

theorem a4DyadicModelFamilies_card : a4DyadicModelFamilies.card = 120 := by decide +kernel

end MassFormulaReleaseExamples
