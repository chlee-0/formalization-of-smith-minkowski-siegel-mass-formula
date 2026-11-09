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
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual rational WN words split into the normalized real operators and
the finite fold with its explicit real raw amplitude. These pointwise identities
use the existing tensor formulas; they add no convergence for arbitrary tests. -/
noncomputable section
open PositiveDefiniteIntegralLattice MeasureTheory
namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}

/-- The rational parameter has the literal rational real coordinate. -/
theorem rationalAdeleRealScalar_diagonal (t : ℚ) :
    rationalAdeleRealScalar (algebraMap ℚ RationalAdele t) = (t : ℝ) := by
  change rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele t) = _
  rw [rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  rfl

/-- Exact one-step splitting, with operator normalization rather than Haar
normalization. Arbitrary supplied factors carry no extra convergence assertion. -/
theorem rationalAdeleWN_normalized_realFinite (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (realTest : (Fin n → ℝ) → ℂ) (finiteTest : (Fin n → RationalFiniteAdele) → ℂ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator (algebraMap ℚ RationalAdele t)
        (fun x => realTest (rationalAdeleVectorRealPart n x) * finiteTest (rationalAdeleVectorFinitePart n x))) =
      fun x => L.polarRealNormalizedFourier (L.polarRealPhaseOperator (t : ℝ) realTest)
        (rationalAdeleVectorRealPart n x) *
        ((L.polarRealFourierMass : ℂ) * standardFiniteFourier
          (fun y => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t y : ℂ) * finiteTest y)
          (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec (rationalAdeleVectorFinitePart n x))) := by
  funext x
  rw [rationalAdeleRankOneWeylUnipotent_realFiniteTensor, rationalAdeleRealScalar_diagonal]
  rw [standardFiniteFourier_eq_fourierIntegral]
  change L.polarRealRawFourier (L.polarRealPhaseOperator (t : ℝ) realTest) _ * _ = _
  rw [L.polarRealRawFourier_eq_mass_normalized]
  have hphase : (fun x => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
      (algebraMap ℚ RationalAdele t).2 x : ℂ) * finiteTest x) =
      (fun x => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * finiteTest x) := rfl
  rw [hphase]
  ring

/-- Every finite rational word is an equality of actual test functions, with
literal real and finite folds. No generic representation or new family. -/
theorem rationalAdeleWN_word_normalized_realFinite (L : PositiveDefiniteIntegralLattice n) (word : List ℚ)
    (realTest : (Fin n → ℝ) → ℂ) (finiteTest : (Fin n → RationalFiniteAdele) → ℂ) :
    word.foldr (fun t test => L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator (algebraMap ℚ RationalAdele t) test))
      (fun x => realTest (rationalAdeleVectorRealPart n x) * finiteTest (rationalAdeleVectorFinitePart n x)) =
    fun x => (word.foldr (fun (t : ℚ) f => L.polarRealNormalizedFourier (L.polarRealPhaseOperator (t : ℝ) f)) realTest)
        (rationalAdeleVectorRealPart n x) *
      (word.foldr (fun t f z => (L.polarRealFourierMass : ℂ) * standardFiniteFourier
        (fun y => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t y : ℂ) * f y)
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec z)) finiteTest)
        (rationalAdeleVectorFinitePart n x) := by
  induction word with
  | nil => rfl
  | cons t word ih =>
    simp only [List.foldr_cons]
    rw [ih, rationalAdeleWN_normalized_realFinite]

/-- Real intermediate outputs remain in the Gaussian family on the full
rational word, so the split does not hide arbitrary real output tests. -/
theorem isPolarRealGaussian_normalized_WN_word (L : PositiveDefiniteIntegralLattice n) (word : List ℚ)
    {realTest : (Fin n → ℝ) → ℂ} (hreal : L.IsPolarRealGaussian realTest) :
    L.IsPolarRealGaussian
      (word.foldr (fun (t : ℚ) f => L.polarRealNormalizedFourier (L.polarRealPhaseOperator (t : ℝ) f)) realTest) := by
  induction word with
  | nil => exact hreal
  | cons t word ih => exact (ih.phase L (t : ℝ)).normalizedFourier L

end RationalQuadraticSpaceMatrix
