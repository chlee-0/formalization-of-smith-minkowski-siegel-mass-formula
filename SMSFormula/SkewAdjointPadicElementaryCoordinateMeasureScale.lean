import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureTransport
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport

/-!
# Same-carrier scale of the form-adapted p-adic coordinate measure

The inverse basis change sends the scalar-extended fixed basis to the
form-adapted basis.  Its determinant is therefore the scalar extension of
the single rational fixed/form-adapted comparison determinant.  Combining
this with the measure transport along the basis change and the general
coordinate transport expresses the form-adapted coordinate measure as a
same-carrier scalar multiple of the fixed-basis coordinate measure.

Away from the finite rational comparison support this scalar is one.  The
support remains separate from the Schulze--Pillot bad-prime set.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Matrix

variable {n : ℕ}

local instance skewAdjointPadicElementaryScaleMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicElementaryScaleBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The determinant of the inverse form-to-fixed basis change is exactly the
scalar extension of the rational fixed/form-adapted comparison determinant. -/
theorem det_skewAdjointFormElementaryToFixedPadicBasisChange_symm
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    LinearMap.det
        (skewAdjointFormElementaryToFixedPadicBasisChange
          p F hF hdet).symm.toLinearMap =
      algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet) := by
  let b := skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F
  let c := skewAdjointFormElementaryPadicFinBasis p F hF hdet
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  have hec : ∀ i, e.symm (b i) = c i := by
    intro i
    apply e.injective
    simpa [e, b, c] using
      (skewAdjointFormElementaryToFixedPadicBasisChange_apply_basis
        p F hF hdet i).symm
  calc
    LinearMap.det e.symm.toLinearMap =
        b.det (fun i ↦ e.symm (b i)) := by
      symm
      have hcomp :=
        Module.Basis.det_comp b e.symm.toLinearMap b
      simpa only [Module.Basis.det_self, mul_one] using hcomp
    _ = b.det c := by
      congr 1
      funext i
      exact hec i
    _ = algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet) := by
      exact skewAdjointFixedPadicBasis_det_formElementary p F hF hdet

/-- On the common skew-adjoint carrier, the form-adapted coordinate measure
is the fixed-basis coordinate measure scaled by the inverse norm of the single
rational basis-comparison determinant. -/
theorem skewAdjointFormElementaryPadicCoordinateMeasure_eq_smul
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet =
      ‖algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  let μ := skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
  let ν := skewAdjointPadicCoordinateMeasure F p
  have hforward : Measure.map e μ = ν :=
    map_skewAdjointFormElementaryPadicCoordinateMeasure_basisChange
      p F hF hdet
  calc
    μ = Measure.map e.symm (Measure.map e μ) := by
      exact
        (MeasurableEquiv.map_map_symm
          e.symm.toHomeomorph.toMeasurableEquiv).symm
    _ = Measure.map e.symm ν := by rw [hforward]
    _ = ‖LinearMap.det e.symm.toLinearMap‖₊⁻¹ • ν := by
      exact
        map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det
          F p e.symm
    _ = ‖algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊⁻¹ • ν := by
      rw [det_skewAdjointFormElementaryToFixedPadicBasisChange_symm]

/-- Outside the rational comparison-determinant support, the form-adapted and
fixed-basis coordinate measures agree on their common carrier. -/
theorem skewAdjointFormElementaryPadicCoordinateMeasure_eq_of_not_mem
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    skewAdjointFormElementaryPadicCoordinateMeasure q.1 F hF hdet =
      skewAdjointPadicCoordinateMeasure F q.1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [skewAdjointFormElementaryPadicCoordinateMeasure_eq_smul]
  rw [nnnorm_skewAdjointFixedFormElementaryDetScalar_eq_one_of_not_mem
    F hF hdet q hq]
  simp

end Matrix
