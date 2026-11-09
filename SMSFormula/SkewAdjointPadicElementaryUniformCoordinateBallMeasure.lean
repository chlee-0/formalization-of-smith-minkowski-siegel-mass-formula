import SMSFormula.SkewAdjointPadicElementaryCoordinateBall
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureTransport
import SMSFormula.SkewAdjointPadicUniformCoordinateBallMeasure

/-!
# Haar mass of form-adapted p-adic uniform coordinate balls

The form-to-fixed basis change commutes with uniform scalar
multiplication.  It therefore maps every form-adapted uniform coordinate ball
onto the corresponding fixed-coordinate ball.  Combining this exact
set transport with the measure pushforward and the fixed-coordinate
ball mass gives the form-adapted ball mass.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Matrix

variable {n : ℕ}

local instance skewAdjointPadicElementaryUniformBallMeasureMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicElementaryUniformBallMeasureBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

set_option maxRecDepth 2000 in
/-- The form-to-fixed basis change maps each form-adapted level-`k`
uniform coordinate ball onto the fixed-coordinate ball at the same
level. -/
theorem
    skewAdjointFormElementaryToFixedPadicBasisChange_image_uniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet ''
        skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet =
      skewAdjointPadicUniformCoordinateBall F p k := by
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  let A := skewAdjointPadicUniformCoordinateDilation F p k
  let C := skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet
  let D := skewAdjointPadicCoordinateLattice F p
  have hCD : e '' (C : Set _) = (D : Set _) :=
    skewAdjointFormElementaryToFixedPadicBasisChange_image_lattice
      p F hF hdet
  change e '' (A '' (C : Set _)) = A '' (D : Set _)
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ?_, ?_⟩
    · rw [← hCD]
      exact ⟨x, hx, rfl⟩
    · have hcomm : e (A x) = A (e x) := by
        dsimp only [A]
        rw [skewAdjointPadicUniformCoordinateDilation_apply,
          skewAdjointPadicUniformCoordinateDilation_apply]
        exact e.map_smul ((p : ℚ_[p]) ^ k) x
      exact hcomm.symm
  · rintro ⟨_, hy, rfl⟩
    rw [← hCD] at hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨A x, ⟨x, hx, rfl⟩, ?_⟩
    dsimp only [A]
    rw [skewAdjointPadicUniformCoordinateDilation_apply,
      skewAdjointPadicUniformCoordinateDilation_apply]
    exact e.map_smul ((p : ℚ_[p]) ^ k) x

/-- The inverse image of a fixed-coordinate ball under the
form-to-fixed basis change is the form-adapted ball at the same level. -/
theorem
    skewAdjointFormElementaryToFixedPadicBasisChange_preimage_uniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet ⁻¹'
        skewAdjointPadicUniformCoordinateBall F p k =
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet := by
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  let C :=
    skewAdjointFormElementaryPadicUniformCoordinateBall p k F hF hdet
  have himage : e '' C = skewAdjointPadicUniformCoordinateBall F p k :=
    skewAdjointFormElementaryToFixedPadicBasisChange_image_uniformCoordinateBall
      p k F hF hdet
  calc
    e ⁻¹' skewAdjointPadicUniformCoordinateBall F p k =
        e ⁻¹' (e '' C) :=
      congrArg (fun s : Set _ ↦ e ⁻¹' s) himage.symm
    _ = C := e.toEquiv.preimage_image C

/-- The form-adapted normalized additive Haar measure of its level-`k`
uniform coordinate ball is `p ^ (-k d)`, where `d` is the symbolic rational
skew-adjoint rank. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_uniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet) =
      ((p : ℝ≥0∞) ^
        (k * Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
  let e := skewAdjointFormElementaryToFixedPadicBasisChange p F hF hdet
  let μ := skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
  let D := skewAdjointPadicUniformCoordinateBall F p k
  have hmap : Measure.map e μ = skewAdjointPadicCoordinateMeasure F p :=
    map_skewAdjointFormElementaryPadicCoordinateMeasure_basisChange
      p F hF hdet
  have happly := congrArg (fun ν : Measure _ ↦ ν D) hmap
  change
    (Measure.map e μ) D =
      skewAdjointPadicCoordinateMeasure F p D at happly
  rw [Measure.map_apply e.continuous.measurable
      (isClopen_skewAdjointPadicUniformCoordinateBall F p k).2.measurableSet,
    skewAdjointFormElementaryToFixedPadicBasisChange_preimage_uniformCoordinateBall
      p k F hF hdet,
    skewAdjointPadicCoordinateMeasure_uniformCoordinateBall] at happly
  exact happly

end Matrix
