import SMSFormula.RationalAdeleOrthogonalFourierCovariance
import SMSFormula.RationalCliffordGeneralSpinQuadraticValueInvariant
import SMSFormula.RationalAdeleRationalMatrixHaar

/-!
# The full-adelic acting group preserves both the coordinate Haar and the value

The rational-point case of this statement follows from the rational-matrix Haar law.
The adelic case follows from adelic orthogonal Haar invariance (`RationalAdeleOverlapTranspose`):
every full-adelic `GSpin` point acts through a special-orthogonal matrix point, and
every full-adelic orthogonal matrix preserves the fixed coordinate Haar.

Combined with value invariance, the full acting group -- not merely its rational
points -- preserves the whole fibration of the coordinate space over the value line, measure and
all.

Preserving the fibration is not a disintegration.  No family of conditional measures is
constructed, no orbital measure is identified with a fiber of the coordinate Haar, and no
quotient-measure comparison follows.  Uniqueness of an invariant measure on a transitive space
still determines it only up to a scalar.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- A full-adelic special orthogonal matrix preserves the fixed coordinate Haar. -/
theorem measurePreserving_fullAdelicSpecialOrthogonal_mulVec
    (V : RationalQuadraticSpaceMatrix n) (h : V.FullAdelicSpecialOrthogonalGroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ h.1.1.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
  V.fullAdelicOrthogonal_measurePreserving_coordinateHaar h.1

/-- The adelic case of the Haar invariance, at the acting group itself. -/
theorem measurePreserving_fullAdelicCliffordGeneralSpin_mulVec
    (V : RationalQuadraticSpaceMatrix n) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.matrixPoint.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have h := V.measurePreserving_fullAdelicSpecialOrthogonal_mulVec g.matrixGroup
  simpa using h

theorem map_rationalAdeleCoordinateAddHaarMeasure_fullAdelicCliffordGeneralSpin
    (V : RationalQuadraticSpaceMatrix n) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (fun x : Fin n → RationalAdele ↦ g.matrixPoint.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) =
      rationalAdeleCoordinateAddHaarMeasure n :=
  (V.measurePreserving_fullAdelicCliffordGeneralSpin_mulVec g).map_eq

/-- Nonnegative integrals are unchanged by the full-adelic action. -/
theorem lintegral_comp_fullAdelicCliffordGeneralSpin
    (V : RationalQuadraticSpaceMatrix n) (g : V.FullAdelicCliffordGeneralSpinGroup)
    (f : (Fin n → RationalAdele) → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (g.matrixPoint.1.mulVec x) ∂rationalAdeleCoordinateAddHaarMeasure n =
      ∫⁻ x, f x ∂rationalAdeleCoordinateAddHaarMeasure n :=
  (V.measurePreserving_fullAdelicCliffordGeneralSpin_mulVec g).lintegral_comp hf

/-- The fibration is preserved by the whole acting group: the action preserves the coordinate
Haar and preserves every value fiber. -/
theorem fullAdelicCliffordGeneralSpin_preserves_haar_and_value
    (V : RationalQuadraticSpaceMatrix n) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.matrixPoint.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (rationalAdeleCoordinateAddHaarMeasure n) ∧
      ∀ x : Fin n → RationalAdele,
        V.fullAdelicQuadraticFormValue (g.matrixPoint.1 *ᵥ x) =
          V.fullAdelicQuadraticFormValue x :=
  ⟨V.measurePreserving_fullAdelicCliffordGeneralSpin_mulVec g,
    fun x ↦ V.fullAdelicQuadraticFormValue_cliffordGeneralSpin g x⟩

end RationalQuadraticSpaceMatrix

end
