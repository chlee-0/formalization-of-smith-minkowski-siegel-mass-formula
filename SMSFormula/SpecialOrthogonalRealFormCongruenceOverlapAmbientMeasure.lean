import SMSFormula.SpecialOrthogonalRealFormCongruencePointCenteredDensity

/-!
# Ambient measure comparison for explicit real-congruence overlaps

This module extends the two chart densities measurably to the fixed source
tangent carrier, rewrites their cocycle on the exact overlap, and applies the
real nonlinear additive-Haar change-of-variables theorem.  The tangent basis
comparison scalar does not enter this fixed-carrier Jacobian step.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceOverlapAmbientMeasureMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapAmbientMeasureBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The source identity-chart density, extended by zero to the ambient source
tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet 1)
    (fun _ => 0) x

/-- The independently normalized target identity-chart density, extended by
zero and pulled back through the explicit tangent equivalence. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target →
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule)
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F' hF' hdet' 1)
    (fun _ => 0)
    (c.tangentEquiv x)

/-- The ambient source density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measurable
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
        F hF hdet) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        F hF hdet).open_target.measurableSet).measurable_extend
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1)
      measurable_const

/-- The pulled-back ambient target density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measurable
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
        F F' hF' hdet' c) := by
  apply Measurable.comp _ c.tangentEquiv.continuous.measurable
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        F' hF' hdet').open_target.measurableSet).measurable_extend
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F' hF' hdet' 1)
      measurable_const

/-- On the source identity-chart target, the ambient source density is the
subtype density. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) :
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
        F hF hdet x =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1 ⟨x, hx⟩ := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- On the pulled-back target chart, the ambient target density is the
target-form subtype density. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : c.tangentEquiv x ∈
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target) :
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
        F F' hF' hdet' c x =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F' hF' hdet' 1 ⟨c.tangentEquiv x, hx⟩ := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨_, hx⟩

/-- On the exact ambient source, the source density is the target density
after the cross transition times the absolute Frechet Jacobian. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientDensityCocycle
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
        F hF hdet x =
      specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
          F F' hF' hdet' c
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x) *
        ENNReal.ofReal
          |(fderiv ℝ
            (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
              F F' hF hdet hF' hdet' c) x).det| := by
  have hmap :=
    mapsTo_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c hx
  have htarget :
      c.tangentEquiv
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x) ∈
        (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target :=
    hmap.1
  rw [
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity_eq
      F hF hdet x hx.1,
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity_eq
      F F' hF' hdet' c
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x) htarget]
  have hcoordinate :
      c.tangentEquiv
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x) =
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx).1 := by
    rw [specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at
      F F' hF hdet hF' hdet' c x hx, c.tangentEquiv.apply_symm_apply]
  have hcoordinateSubtype :
      (⟨c.tangentEquiv
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x), htarget⟩ :
        (specialFormPreservingSmoothRealIdentityChart
          F' hF' hdet').target) =
        specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx :=
    Subtype.ext hcoordinate
  rw [hcoordinateSubtype]
  simpa only [
    specialFormPreservingSmoothRealFormCongruenceTransitionJacobian,
    specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant,
    fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c x hx] using
    specialFormPreservingSmoothRealFormCongruenceChartDensityCocycle_source
      F F' hF hdet hF' hdet' c x hx

/-- On the exact ambient overlap, the full derivative is also a derivative
within the source set. -/
theorem hasFDerivWithinAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    HasFDerivWithinAt
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (fderiv ℝ
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c) x)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) x := by
  rw [fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    F F' hF hdet hF' hdet' c x hx]
  exact
    (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c x hx).hasFDerivWithinAt

/-- The fixed-carrier nonlinear transition sends Jacobian-weighted source
coordinate Haar to coordinate Haar restricted to the exact image. -/
theorem map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          fun x => ENNReal.ofReal
            |(fderiv ℝ
              (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
                F F' hF hdet hF' hdet' c) x).det|) =
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
          F F' hF hdet hF' hdet' c) := by
  letI : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
    realFormCongruenceOverlapAmbientMeasureBorelSpace F
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let U :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c
  let V :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
      F F' hF hdet hF' hdet' c
  let Ψ :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  have hderiv : ∀ x ∈ U,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) U x := by
    intro x hx
    exact
      hasFDerivWithinAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x hx
  have hmap := @MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule
    _ _ _ U Ψ (fun x => fderiv ℝ Ψ x)
    (realFormCongruenceOverlapAmbientMeasureMeasurableSpace F)
    (realFormCongruenceOverlapAmbientMeasureBorelSpace F) μ
    (Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0)
    (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet.nullMeasurableSet
    hderiv
    (injOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c)
  have himage : Ψ '' U = V :=
    image_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c
  simpa [μ, U, V, Ψ, himage] using hmap

end PositiveDefiniteIntegralLattice
