import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicGroupHaarFactor
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberOverlap

/-!
# Product measures on the p-adic presentation-chart overlap

The fixed block central-fiber product measure is first carried to ambient
coordinates by the supplied presentation.  Its intrinsic restriction and the
ambient fixed product measure's intrinsic restriction to the genuine selected
chart overlap are then compared through the actual cross-chart homeomorphism.

The comparison is the already evaluated reciprocal p-adic tangent modulus.
No independently chosen chart domains are identified, and no finite cylinder
is transported here.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance padicOverlapMeasureUnitMeasurableSpace :
    MeasurableSpace ℚ_[p]ˣ := borel _

local instance padicOverlapMeasureUnitBorelSpace :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

local instance padicOverlapMeasureGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (W.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

local instance padicOverlapMeasureGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace (W.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-- The fixed block central-fiber product measure transported to ambient
target coordinates. -/
def transportedBlockPadicCentralFiberProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  Measure.map
    (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℚ_[p])
    ((P.blockSpace hx)
      |>.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

/-- Intrinsic restriction of the transported block product measure to the
exact transported-coordinate overlap. -/
def transportedPadicCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedPadicCentralFiberTargetOverlap p hx) :=
  Measure.comap Subtype.val
    (P.transportedBlockPadicCentralFiberProductMeasure p hx)

/-- Intrinsic restriction of the ambient fixed product measure to the exact
ambient-coordinate overlap. -/
def ambientPadicCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.ambientPadicCentralFiberTargetOverlap p hx) :=
  Measure.comap Subtype.val
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

/-- The exact selected target-overlap transition carries the transported
block product measure by the reciprocal p-adic tangent modulus. -/
theorem map_transportedPadicCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx)
        (P.transportedPadicCentralFiberTargetOverlapProductMeasure p hx) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx := by
  let e := P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx
  let S := P.transportedPadicCentralFiberTargetOverlap p hx
  let T := P.ambientPadicCentralFiberTargetOverlap p hx
  let μ := P.transportedBlockPadicCentralFiberProductMeasure p hx
  let ν := V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p
  let q : ℝ≥0 :=
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  have hS : MeasurableSet S :=
    (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet
  have hT : MeasurableSet T :=
    (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet
  apply (MeasurableEmbedding.subtype_coe hT).map_injective
  rw [Measure.map_map continuous_subtype_val.measurable e.measurable]
  rw [show (Subtype.val ∘ e) =
      (Subtype.val : S → ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) by
        funext y
        exact P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph_apply
          p hx y]
  rw [transportedPadicCentralFiberTargetOverlapProductMeasure,
    ambientPadicCentralFiberTargetOverlapProductMeasure]
  rw [map_comap_subtype_coe hS, Measure.map_smul,
    map_comap_subtype_coe hT]
  change μ.restrict S = q • ν.restrict T
  rw [show S = T by
    exact P.transportedPadicCentralFiberTargetOverlap_eq_ambient p hx]
  rw [← Measure.restrict_smul]
  congr 1
  exact P.map_blockToAmbientPadicCentralFiberProductMeasure hx p

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
