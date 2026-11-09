import SMSFormula.RationalAdeleNormalizedWordSplit
import SMSFormula.RationalFiniteAdeleAdditiveCharacter
import Mathlib.Topology.LocallyConstant.Basic
import SMSFormula.QuadraticRegularValueDifferential
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Normed.Module.FiniteDimension
import SMSFormula.LocalScalarCoordinateHaar
import SMSFormula.QuadraticScalarOrthogonalTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import SMSFormula.PadicCayleyTangentNorm
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Algebra.Indicator
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRangeGoodPlace
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange
import SMSFormula.RationalFiniteAdeleIntegralLatticeDilation
import SMSFormula.PadicScalarAdditiveHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import SMSFormula.RationalFiniteAdeleQuadraticGaussStandardQuotient
import SMSFormula.RationalFiniteAdeleHaarScaling
import SMSFormula.RationalFiniteAdeleStandardFamilyScaleNormalization
import SMSFormula.RationalPadicStandardGaussFactorization
import SMSFormula.RationalIdeleFiniteModule
import SMSFormula.RationalFiniteAdeleStandardFamilyPolarFrequency
import SMSFormula.RationalAdeleRankOnePolarGaussianLatticeFourierSquare
import SMSFormula.RealPolarGaussianOperators
import SMSFormula.RationalAdeleRankOneDilationFourierCovariance
import SMSFormula.RationalPadicPlaceNormProduct
import SMSFormula.RationalAdeleVectorPolarThetaSpecialization

/-!
# Explicit decay of the standard rational theta to its cusp value

The common Theta/E covariance is exact and estimates nothing.  This file supplies the
first actual estimate on the theta side: at large positive real scale the standard
rational theta approaches its literal cusp value `1` at an explicit exponential rate.

The only inputs are the existing integer-theta identification, the existing
positive-definite lower bound `c * (sum of squares) <= x . S x`, and the existing
summability.  No new lattice, test family, cutoff or Haar is introduced.

Negative scope: this bounds only the theta side.  It says nothing about the cusp
functional `E`, nothing about the difference `Theta - E`, and nothing about any orbit;
the rate is the existing positive-definite constant of the polar matrix and is not
claimed to be optimal.
-/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal real summand of the standard rational theta at a real scale. -/
def polarStandardThetaSummand (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (z : Fin n → ℤ) : ℝ :=
  Real.exp (-Real.pi * a * (integerVectorReal z ⬝ᵥ
    L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec (integerVectorReal z)))

/-- The standard rational theta at a real scale, written as a real sum. -/
def polarStandardThetaReal (L : PositiveDefiniteIntegralLattice n) (a : ℝ) : ℝ :=
  ∑' z : Fin n → ℤ, L.polarStandardThetaSummand a z

theorem integerVectorReal_zero : integerVectorReal (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [integerVectorReal]

theorem polarStandardThetaSummand_pos (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (z : Fin n → ℤ) :
    0 < L.polarStandardThetaSummand a z := Real.exp_pos _

@[simp]
theorem polarStandardThetaSummand_zero (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    L.polarStandardThetaSummand a 0 = 1 := by
  simp [polarStandardThetaSummand, integerVectorReal_zero]

/-- A nonzero integer vector has coordinate-square sum at least one. -/
theorem one_le_sum_sq_integerVectorReal {z : Fin n → ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ ∑ i, integerVectorReal z i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  have hone : (1 : ℝ) ≤ integerVectorReal z i ^ 2 := by
    have h1 : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
    have h2 : (1 : ℝ) ≤ |((z i : ℝ))| := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ |((z i : ℝ))| ^ 2 := by gcongr
      _ = integerVectorReal z i ^ 2 := by simp [integerVectorReal, sq_abs]
  exact hone.trans (Finset.single_le_sum (f := fun j => integerVectorReal z j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

end PositiveDefiniteIntegralLattice
