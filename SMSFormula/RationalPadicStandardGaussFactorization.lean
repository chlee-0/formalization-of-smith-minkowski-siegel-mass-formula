import SMSFormula.RationalFiniteAdeleIntegralLatticeDilation
import SMSFormula.RationalFiniteAdeleAdditiveCharacter
import Mathlib.Topology.LocallyConstant.Basic
import SMSFormula.PadicScalarAdditiveHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
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
import SMSFormula.RationalFiniteAdeleQuadraticGaussStandardQuotient
import SMSFormula.RationalFiniteAdeleQuadraticGaussFourierRegularity
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange

/-!
# Native local factorization of the actual standard finite Gauss Fourier integral

The finite factor used by the actual adelic W-after-M operator is factored on
its existing integral carrier. Native negative dot kernels, the scalar-extended
quadratic form and all supplied vector Haar unit-ball masses remain literal.
-/
noncomputable section
open PositiveDefiniteIntegralLattice MeasureTheory IsDedekindDomain Topology QuadraticMap Matrix
open scoped ENNReal
namespace RationalQuadraticSpaceMatrix

local instance (place : HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv place).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv place).2⟩
local instance (place : HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[Rat.HeightOneSpectrum.primesEquiv place] := borel _
local instance (place : HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[Rat.HeightOneSpectrum.primesEquiv place] := ⟨rfl⟩

variable {n : ℕ}

/-- Evaluation of the quadratic value is the actual native scalar extension. -/
theorem padicEquiv_finiteAdelicQuadraticFormValue (V : RationalQuadraticSpaceMatrix n)
    (place : HeightOneSpectrum ℤ) (x : Fin n → RationalFiniteAdele) :
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place) (V.finiteAdelicQuadraticFormValue x place) =
    V.commutativeScalarExtensionQuadraticForm ℚ_[Rat.HeightOneSpectrum.primesEquiv place]
      (fun i => (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place) (x i place)) := by
  rw [commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
  let ev : RationalFiniteAdele →+* place.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ) place
  change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place) (ev (V.finiteAdelicQuadraticFormValue x)) = _
  simp [finiteAdelicQuadraticFormValue, finiteAdelicFormMatrix, gramQuadraticValue,
    specialOrthogonalMappedFormMatrix, Matrix.mulVec, dotProduct, map_sum, map_mul,
    show ∀ q : ℚ, ev (algebraMap ℚ RationalFiniteAdele q) = algebraMap ℚ (place.adicCompletion ℚ) q from fun q => rfl]
  rfl

end RationalQuadraticSpaceMatrix
