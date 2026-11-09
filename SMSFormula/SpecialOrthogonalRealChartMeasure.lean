import SMSFormula.AdelicProperFinitePresentation
import SMSFormula.SkewAdjointRealMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Real measures on the common smooth chart sources

This file restricts the normalized real skew-adjoint coordinate measure to the
target of the common smooth identity chart, transports it to every exact
centered source subtype, and compares those source measures through common
coordinates. It does not extend these measures to the full special orthogonal
group or glue them across chart overlaps.
-/

noncomputable section

open scoped Matrix.Norms.Operator ContDiff

namespace Matrix

variable {n : ℕ}

/-- The determinant of a finite real matrix is maximally smooth for the
operator norm used by the special-orthogonal coordinate model. -/
theorem contDiff_det_real : ContDiff ℝ ∞
    (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  simp_rw [Matrix.det_apply]
  apply ContDiff.sum
  intro σ hσ
  have hprod : ContDiff ℝ ∞
      (fun A : Matrix (Fin n) (Fin n) ℝ => ∏ i, A (σ i) i) := by
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ ∞
        (fun _A : Matrix (Fin n) (Fin n) ℝ => (1 : ℝ)))
    | @insert i s hi ih =>
        let e : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
          ⟨{
            toFun := fun A => A (σ i) i
            map_add' := by intro A B; rfl
            map_smul' := by intro c A; rfl
          }, LinearMap.continuous_of_finiteDimensional _⟩
        simpa [Finset.prod_insert hi] using
          ((e.contDiff : ContDiff ℝ ∞
            (fun A : Matrix (Fin n) (Fin n) ℝ => A (σ i) i)).mul ih)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  · exact hprod
  · exact hprod.neg

/-- Replacing one row of a finite real matrix by a fixed row is maximally
smooth for the operator norm. -/
theorem contDiff_updateRow_real (j : Fin n) (v : Fin n → ℝ) : ContDiff ℝ ∞
    (fun A : Matrix (Fin n) (Fin n) ℝ => A.updateRow j v) := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    {
      toFun := fun A => A.updateRow j 0
      map_add' := by
        intro A B
        ext i k
        by_cases h : i = j <;> simp [Matrix.updateRow, h]
      map_smul' := by
        intro c A
        ext i k
        by_cases h : i = j <;> simp [Matrix.updateRow, h]
    }
  let Lc : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  have heq : (fun A : Matrix (Fin n) (Fin n) ℝ => A.updateRow j v) =
      fun A => Lc A + (0 : Matrix (Fin n) (Fin n) ℝ).updateRow j v := by
    funext A
    ext i k
    by_cases h : i = j <;> simp [Lc, L, Matrix.updateRow, h]
  rw [heq]
  exact Lc.contDiff.add contDiff_const

/-- Adjugation of finite real matrices is maximally smooth for the operator
norm used by the special-orthogonal coordinate model. -/
theorem contDiff_adjugate_real : ContDiff ℝ ∞
    (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) := by
  let R : (Fin n → Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ⟨LinearMap.id, LinearMap.continuous_of_finiteDimensional _⟩
  have hentries : ContDiff ℝ ∞
      (fun A : Matrix (Fin n) (Fin n) ℝ =>
        (fun i j => A.adjugate i j : Fin n → Fin n → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    rw [show (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate i j) =
        (fun A => (A.updateRow j (Pi.single i 1)).det) by
      funext A
      exact Matrix.adjugate_apply A i j]
    exact contDiff_det_real.comp (contDiff_updateRow_real j (Pi.single i 1))
  simpa [R] using R.contDiff.comp hentries

end Matrix

namespace PositiveDefiniteIntegralLattice

open MeasureTheory

variable {n : ℕ}

private theorem realChart_isSymm_map_algebraMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    (F.map (algebraMap ℚ ℝ)).IsSymm :=
  hF.map _

private theorem realChart_det_map_algebraMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℝ)).det ≠ 0 := by
  have hmap : algebraMap ℚ ℝ F.det ≠ 0 := by
    intro hz
    apply hdet
    apply (algebraMap ℚ ℝ).injective
    simpa using hz
  have heq : (F.map (algebraMap ℚ ℝ)).det = algebraMap ℚ ℝ F.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((algebraMap ℚ ℝ).map_det F).symm
  rwa [heq]

private theorem realChart_ringChar_ne_two : ringChar ℝ ≠ 2 := by
  norm_num [ringChar.eq ℝ]

local instance specialFormPreservingSmoothRealGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance specialFormPreservingSmoothRealGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance specialFormPreservingSmoothRealChartModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance specialFormPreservingSmoothRealChartModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The common smooth real chart centered at a supplied group point. -/
abbrev specialFormPreservingSmoothRealChart
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g

/-- The common smooth real chart centered at the identity. -/
abbrev specialFormPreservingSmoothRealIdentityChart
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :=
  specialFormPreservingSmoothRealChart F hF hdet 1

/-- The same-form transition between two centered real charts, with the real
normalization proofs fixed for downstream differential arguments. -/
abbrev specialFormPreservingSmoothRealSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g h

/-- Every center belongs to the source of its real chart. This form fixes
the chart's private normalization proofs for downstream use. -/
theorem self_mem_specialFormPreservingSmoothRealChart_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    g ∈ (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g

/-- The real chart sends its center to zero. This form fixes the chart's
private normalization proofs for downstream use. -/
@[simp]
theorem specialFormPreservingSmoothRealChart_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChart F hF hdet g g = 0 :=
  specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_center
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g

/-- The exact same-point overlap of the sources of two centered real charts. -/
def specialFormPreservingSmoothRealChartSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  (specialFormPreservingSmoothRealChart F hF hdet g).source ∩
    (specialFormPreservingSmoothRealChart F hF hdet h).source

/-- The subtype of group points lying in both centered chart sources. -/
abbrev specialFormPreservingSmoothRealChartSourceOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  {x // x ∈ specialFormPreservingSmoothRealChartSourceOverlapSet
    F hF hdet g h}

/-- The exact same-point overlap is open in the full group topology. -/
theorem isOpen_specialFormPreservingSmoothRealChartSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealChartSourceOverlapSet
      F hF hdet g h) :=
  (specialFormPreservingSmoothRealChart F hF hdet g).open_source.inter
    (specialFormPreservingSmoothRealChart F hF hdet h).open_source

/-- Include the common overlap into the source of the chart centered at `g`. -/
def specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
      (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  fun x => ⟨x.1, x.2.1⟩

/-- Include the common overlap into the source of the chart centered at `h`. -/
def specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
      (specialFormPreservingSmoothRealChart F hF hdet h).source :=
  fun x => ⟨x.1, x.2.2⟩

/-- The same-point inclusion into the left chart source is continuous. -/
theorem continuous_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Continuous (specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h) :=
  continuous_subtype_val.subtype_mk _

/-- The same-point inclusion into the right chart source is continuous. -/
theorem continuous_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Continuous (specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h) :=
  continuous_subtype_val.subtype_mk _

/-- Inside the left source subtype, the overlap is the preimage of the right
chart source. -/
def specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  Subtype.val ⁻¹' (specialFormPreservingSmoothRealChart F hF hdet h).source

/-- Inside the right source subtype, the overlap is the preimage of the left
chart source. -/
def specialFormPreservingSmoothRealChartSourceOverlapWithinRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingSmoothRealChart F hF hdet h).source :=
  Subtype.val ⁻¹' (specialFormPreservingSmoothRealChart F hF hdet g).source

/-- The common overlap is open inside the left chart source subtype. -/
theorem isOpen_specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
      F hF hdet g h) :=
  (specialFormPreservingSmoothRealChart F hF hdet h).open_source.preimage
    continuous_subtype_val

/-- The common overlap is open inside the right chart source subtype. -/
theorem isOpen_specialFormPreservingSmoothRealChartSourceOverlapWithinRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealChartSourceOverlapWithinRight
      F hF hdet g h) :=
  (specialFormPreservingSmoothRealChart F hF hdet g).open_source.preimage
    continuous_subtype_val

/-- The left-source overlap set is measurable, so its source measure can be
restricted there. -/
theorem measurableSet_specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet (specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
      F hF hdet g h) :=
  ((specialFormPreservingSmoothRealChart F hF hdet h).open_source.preimage
    continuous_subtype_val).measurableSet

/-- The right-source overlap set is measurable, so its source measure can be
restricted there. -/
theorem measurableSet_specialFormPreservingSmoothRealChartSourceOverlapWithinRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet (specialFormPreservingSmoothRealChartSourceOverlapWithinRight
      F hF hdet g h) :=
  ((specialFormPreservingSmoothRealChart F hF hdet g).open_source.preimage
    continuous_subtype_val).measurableSet

/-- The same-point inclusion into the left chart source is measurable. -/
theorem measurable_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable (specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h) :=
  (continuous_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    F hF hdet g h).measurable

/-- The same-point inclusion into the right chart source is measurable. -/
theorem measurable_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable (specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h) :=
  (continuous_specialFormPreservingSmoothRealChartSourceOverlapToRight
    F hF hdet g h).measurable

private def specialFormPreservingSmoothRealChartSourceOverlapLeftHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h where
  toFun x := ⟨specialFormPreservingSmoothRealChartSourceOverlapToLeft
    F hF hdet g h x, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def specialFormPreservingSmoothRealChartSourceOverlapRightHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartSourceOverlapWithinRight
        F hF hdet g h where
  toFun x := ⟨specialFormPreservingSmoothRealChartSourceOverlapToRight
    F hF hdet g h x, x.2.1⟩
  invFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The same-point inclusion into the left chart source is an open
topological embedding. -/
theorem isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsOpenEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapToLeft
        F hF hdet g h) := by
  let e := specialFormPreservingSmoothRealChartSourceOverlapLeftHomeomorph
    F hF hdet g h
  have hi : Topology.IsOpenEmbedding
      (Subtype.val : specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h →
          (specialFormPreservingSmoothRealChart F hF hdet g).source) :=
    (isOpen_specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
      F hF hdet g h).isOpenEmbedding_subtypeVal
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealChartSourceOverlapLeftHomeomorph] using
      hi.comp e.isOpenEmbedding

/-- The same-point inclusion into the right chart source is an open
topological embedding. -/
theorem isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsOpenEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapToRight
        F hF hdet g h) := by
  let e := specialFormPreservingSmoothRealChartSourceOverlapRightHomeomorph
    F hF hdet g h
  have hi : Topology.IsOpenEmbedding
      (Subtype.val : specialFormPreservingSmoothRealChartSourceOverlapWithinRight
        F hF hdet g h →
          (specialFormPreservingSmoothRealChart F hF hdet h).source) :=
    (isOpen_specialFormPreservingSmoothRealChartSourceOverlapWithinRight
      F hF hdet g h).isOpenEmbedding_subtypeVal
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealChartSourceOverlapRightHomeomorph] using
      hi.comp e.isOpenEmbedding

/-- The same-point inclusion into the left chart source is a topological
embedding. -/
theorem isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapToLeft
        F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    F hF hdet g h).isEmbedding

/-- The same-point inclusion into the right chart source is a topological
embedding. -/
theorem isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapToRight
        F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
    F hF hdet g h).isEmbedding

/-- The same-point inclusion into the left chart source is a measurable
embedding onto the exact source-internal overlap set. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableEmbedding (specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h) := by
  let e := specialFormPreservingSmoothRealChartSourceOverlapLeftHomeomorph
    F hF hdet g h
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val : specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h →
          (specialFormPreservingSmoothRealChart F hF hdet g).source) :=
    MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h)
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealChartSourceOverlapLeftHomeomorph] using
      hi.comp he

/-- The same-point inclusion into the right chart source is a measurable
embedding onto the exact source-internal overlap set. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableEmbedding (specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h) := by
  let e := specialFormPreservingSmoothRealChartSourceOverlapRightHomeomorph
    F hF hdet g h
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val : specialFormPreservingSmoothRealChartSourceOverlapWithinRight
        F hF hdet g h →
          (specialFormPreservingSmoothRealChart F hF hdet h).source) :=
    MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapWithinRight
        F hF hdet g h)
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealChartSourceOverlapRightHomeomorph] using
      hi.comp he

/-- The range of the left same-point inclusion is the exact overlap inside
the left chart source. -/
theorem range_specialFormPreservingSmoothRealChartSourceOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set.range (specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h) =
      specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2.2
  · intro hx
    exact ⟨⟨x.1, ⟨x.2, hx⟩⟩, rfl⟩

/-- The range of the right same-point inclusion is the exact overlap inside
the right chart source. -/
theorem range_specialFormPreservingSmoothRealChartSourceOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set.range (specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h) =
      specialFormPreservingSmoothRealChartSourceOverlapWithinRight
        F hF hdet g h := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2.1
  · intro hx
    exact ⟨⟨x.1, ⟨hx, x.2⟩⟩, rfl⟩

/-- Every centered real chart has the same target as the identity chart,
bundled as a homeomorphism between the exact target subtypes. -/
def specialFormPreservingSmoothRealChartTargetHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChart F hF hdet g).target ≃ₜ
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  Homeomorph.setCongr <|
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g).trans
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two 1).symm

/-- Identifying a centered real chart target with the fixed identity-chart
target does not change its underlying coordinate point. -/
theorem coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    ((specialFormPreservingSmoothRealChartTargetHomeomorph
      F hF hdet g y).1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1 := by
  let heq : (specialFormPreservingSmoothRealChart F hF hdet g).target =
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g).trans
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two 1).symm
  change ((Equiv.setCongr heq y).1 :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1
  rw [Equiv.setCongr_apply]

/-- A centered real chart as a homeomorphism from its exact source subtype to
the fixed identity-chart target subtype. -/
def specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChart F hF hdet g).source ≃ₜ
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  (specialFormPreservingSmoothRealChart
    F hF hdet g).toHomeomorphSourceTarget.trans
      (specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet g)

/-- The normalized coordinate measure restricted to the exact target subtype
of the common smooth real identity chart. -/
def specialFormPreservingSmoothRealIdentityChartTargetMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  Measure.comap Subtype.val (Matrix.skewAdjointRealCoordinateDetMeasure F 0)

/-- The centered chart-source measure obtained by transporting the fixed
identity-target measure through the centered chart inverse. Its type is the
exact centered source subtype. -/
def specialFormPreservingSmoothRealChartSourceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  Measure.map
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet g).symm
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- A centered source measure is equivalently the fixed target measure pulled
back through the centered source-target coordinates. -/
theorem specialFormPreservingSmoothRealChartSourceMeasure_eq_target_comap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g =
      Measure.comap
        (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
          F hF hdet g)
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) := by
  rw [specialFormPreservingSmoothRealChartSourceMeasure]
  exact (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet g).toMeasurableEquiv.map_symm

/-- Every centered chart transports its source measure to the fixed
identity-target measure. -/
theorem map_specialFormPreservingSmoothRealChartSourceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
          F hF hdet g)
        (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g) =
      specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet := by
  rw [specialFormPreservingSmoothRealChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet g).toMeasurableEquiv

/-- The identity-chart source measure obtained by transporting the restricted
coordinate measure through the chart inverse. Its type is the exact open
source subtype, not the full special orthogonal group. -/
def specialFormPreservingSmoothRealIdentityChartSourceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure (specialFormPreservingSmoothRealIdentityChart F hF hdet).source :=
  Measure.map
    (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).toHomeomorphSourceTarget.symm
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- The common-coordinate homeomorphism from the identity chart source to a
centered chart source. -/
def specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ≃ₜ
      (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  (specialFormPreservingSmoothRealIdentityChart
    F hF hdet).toHomeomorphSourceTarget.trans
      (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
        F hF hdet g).symm

/-- The common-coordinate source homeomorphism is fixed left multiplication
on underlying group points. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealIdentityChart F hF hdet).source) :
    (specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
      F hF hdet g x).1 = g * x.1 := by
  let FR := F.map (algebraMap ℚ ℝ)
  let hFR : FR.IsSymm := realChart_isSymm_map_algebraMap F hF
  let hdetR : FR.det ≠ 0 := realChart_det_map_algebraMap_ne_zero F hdet
  let hchar := realChart_ringChar_ne_two
  let C1 := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let Cg := specialFormPreservingSmoothRealChart F hF hdet g
  have hxsource : x.1 ∈
      specialFormPreservingSmoothTranslatedChartNeighborhood
        FR hFR hdetR hchar 1 := by
    simpa only [
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
      using x.2
  rcases hxsource with ⟨z, hz, hzx⟩
  have hz_eq : z = x.1 := by simpa using hzx
  have hxidentity : x.1 ∈
      specialFormPreservingSmoothIdentityChartNeighborhood
        FR hFR hdetR hchar := by
    rwa [← hz_eq]
  have hgxsource : g * x.1 ∈ Cg.source := by
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    exact ⟨x.1, hxidentity, rfl⟩
  let gx : Cg.source := ⟨g * x.1, hgxsource⟩
  let e1 := C1.toHomeomorphSourceTarget
  let eg := specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet g
  have heq :
      specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
          F hF hdet g x = gx := by
    apply eg.injective
    change eg (eg.symm (e1 x)) = eg gx
    rw [eg.apply_symm_apply]
    apply Subtype.ext
    change C1 x.1 = Cg (g * x.1)
    symm
    simpa [FR, hFR, hdetR, hchar, C1, Cg] using
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
        FR hFR hdetR hchar g (g * x.1) hgxsource
  exact congrArg Subtype.val heq

/-- The centered source measure is the fixed-left common-coordinate transport
of the identity source measure. -/
theorem map_specialFormPreservingSmoothRealIdentityChartSourceMeasure_left_mul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
          F hF hdet g)
        (specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet) =
      specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g := by
  let e1 := (specialFormPreservingSmoothRealIdentityChart
    F hF hdet).toHomeomorphSourceTarget
  let eg := specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet g
  change Measure.map (e1.trans eg.symm)
      (Measure.map e1.symm
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)) =
    Measure.map eg.symm
      (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)
  rw [Measure.map_map (e1.trans eg.symm).continuous.measurable
    e1.symm.continuous.measurable]
  congr 1
  funext y
  simp [e1, eg]

/-- The common-coordinate homeomorphism from the source of the chart centered
at `g` to the source of the chart centered at `h`. -/
def specialFormPreservingSmoothRealChartSourceHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChart F hF hdet g).source ≃ₜ
      (specialFormPreservingSmoothRealChart F hF hdet h).source :=
  (specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
    F hF hdet g).symm.trans
      (specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
        F hF hdet h)

/-- The inverse common-coordinate source homeomorphism is left multiplication
by the inverse center on underlying group points. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    ((specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
      F hF hdet g).symm x).1 = g⁻¹ * x.1 := by
  let Lg := specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
    F hF hdet g
  have hforward : g * (Lg.symm x).1 = x.1 := by
    calc
      g * (Lg.symm x).1 = (Lg (Lg.symm x)).1 := by
        symm
        exact coe_specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph_apply
          F hF hdet g (Lg.symm x)
      _ = x.1 := congrArg Subtype.val (Lg.apply_symm_apply x)
  calc
    (Lg.symm x).1 = g⁻¹ * (g * (Lg.symm x).1) := by simp
    _ = g⁻¹ * x.1 := congrArg (fun z => g⁻¹ * z) hforward

/-- Changing chart centers from `g` to `h` is left multiplication by
`h * g⁻¹` on underlying group points. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealChartSourceHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    (specialFormPreservingSmoothRealChartSourceHomeomorph
      F hF hdet g h x).1 = (h * g⁻¹) * x.1 := by
  rw [specialFormPreservingSmoothRealChartSourceHomeomorph,
    Homeomorph.trans_apply,
    coe_specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph_apply,
    coe_specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph_symm_apply]
  simp only [mul_assoc]

/-- Changing a chart source from a center to itself is pointwise the identity. -/
@[simp]
theorem specialFormPreservingSmoothRealChartSourceHomeomorph_self_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    specialFormPreservingSmoothRealChartSourceHomeomorph F hF hdet g g x =
      x := by
  apply Subtype.ext
  simp

/-- Common-coordinate changes between chart sources satisfy the pointwise
cocycle law. -/
@[simp]
theorem specialFormPreservingSmoothRealChartSourceHomeomorph_trans_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h k : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    specialFormPreservingSmoothRealChartSourceHomeomorph F hF hdet h k
        (specialFormPreservingSmoothRealChartSourceHomeomorph
          F hF hdet g h x) =
      specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet g k x := by
  apply Subtype.ext
  simp [mul_assoc]

/-- The common-coordinate change from the `g` chart source to the `h` chart
source transports the normalized source measure. -/
theorem map_specialFormPreservingSmoothRealChartSourceMeasure_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g) =
      specialFormPreservingSmoothRealChartSourceMeasure F hF hdet h := by
  let Lg := specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
    F hF hdet g
  let Lh := specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph
    F hF hdet h
  let e := specialFormPreservingSmoothRealChartSourceHomeomorph
    F hF hdet g h
  let μ := specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet
  calc
    Measure.map e
        (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g) =
        Measure.map e (Measure.map Lg μ) := by
          rw [map_specialFormPreservingSmoothRealIdentityChartSourceMeasure_left_mul]
    _ = Measure.map Lh μ := by
      rw [Measure.map_map e.continuous.measurable Lg.continuous.measurable]
      congr 1
      funext x
      simp [e, Lg, Lh,
        specialFormPreservingSmoothRealChartSourceHomeomorph]
    _ = specialFormPreservingSmoothRealChartSourceMeasure F hF hdet h :=
      map_specialFormPreservingSmoothRealIdentityChartSourceMeasure_left_mul
        F hF hdet h

/-- Successive common-coordinate changes transport source measures
functorially. -/
theorem map_map_specialFormPreservingSmoothRealChartSourceMeasure_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h k : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceHomeomorph
          F hF hdet h k)
        (Measure.map
          (specialFormPreservingSmoothRealChartSourceHomeomorph
            F hF hdet g h)
          (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g)) =
      specialFormPreservingSmoothRealChartSourceMeasure F hF hdet k := by
  rw [map_specialFormPreservingSmoothRealChartSourceMeasure_center_change,
    map_specialFormPreservingSmoothRealChartSourceMeasure_center_change]

/-- The fixed-target coordinates of a common-overlap point through the left
centered chart. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet g) ∘
      (specialFormPreservingSmoothRealChartSourceOverlapToLeft
        F hF hdet g h)

/-- The fixed-target coordinates of a common-overlap point through the right
centered chart. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet h) ∘
      (specialFormPreservingSmoothRealChartSourceOverlapToRight
        F hF hdet g h)

/-- The left coordinate image of the exact common chart-source overlap. -/
abbrev specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  Set.range
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h)

/-- The right coordinate image of the exact common chart-source overlap. -/
abbrev specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  Set.range
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h)

/-- The left overlap-coordinate map is an open topological embedding into the
fixed target subtype. -/
theorem isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsOpenEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h) := by
  exact
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet g).isOpenEmbedding.comp
        (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)

/-- The right overlap-coordinate map is an open topological embedding into the
fixed target subtype. -/
theorem isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsOpenEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h) := by
  exact
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet h).isOpenEmbedding.comp
        (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h)

/-- The exact left coordinate image of a common overlap is open in the fixed
target subtype. -/
theorem isOpen_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    F hF hdet g h).isOpen_range

/-- The exact right coordinate image of a common overlap is open in the fixed
target subtype. -/
theorem isOpen_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
      F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    F hF hdet g h).isOpen_range

/-- The exact left coordinate image is measurable in the fixed target
subtype. -/
theorem measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h) :=
  (isOpen_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
    F hF hdet g h).measurableSet

/-- The exact right coordinate image is measurable in the fixed target
subtype. -/
theorem measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h) :=
  (isOpen_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
    F hF hdet g h).measurableSet

/-- The left overlap-coordinate map is a topological embedding into the fixed
target subtype. -/
theorem isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    F hF hdet g h).isEmbedding

/-- The right overlap-coordinate map is a topological embedding into the fixed
target subtype. -/
theorem isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Topology.IsEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h) :=
  (isOpenEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    F hF hdet g h).isEmbedding

/-- The left range homeomorphism followed by coordinate-image inclusion is
the original left overlap-coordinate map. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft_toHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    (((isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph x).1 :
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h x :=
  rfl

/-- The right range homeomorphism followed by coordinate-image inclusion is
the original right overlap-coordinate map. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight_toHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    (((isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).toHomeomorph x).1 :
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h x :=
  rfl

/-- The exact coordinate transition between the left and right images of a
common chart-source overlap. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h :=
  (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    F hF hdet g h).toHomeomorph.symm.trans
      (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h).toHomeomorph

/-- The coordinate-image homeomorphism sends the left coordinates of an
overlap point to its right coordinates. -/
@[simp]
theorem specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h
        ((isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h).toHomeomorph x) =
      (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h).toHomeomorph x := by
  simp [specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph]

/-- On coordinates coming from an overlap point, the coordinate-image
homeomorphism has the same underlying model-space value as the established
common smooth chart transition. -/
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply_eq_transition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h
        ((isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h).toHomeomorph x)).1 :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) =
      specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h
        (((isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h).toHomeomorph x).1 :
            (specialFormPreservingSmoothRealIdentityChart F hF hdet).target).1 := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply]
  change
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h x).1 =
      specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h x).1
  have hleft :
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h x).1 =
        specialFormPreservingSmoothRealChart F hF hdet g x.1 := by
    rfl
  have hright :
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
          F hF hdet g h x).1 =
        specialFormPreservingSmoothRealChart F hF hdet h x.1 := by
    rfl
  rw [hleft, hright, specialFormPreservingSmoothSkewAdjointTransition,
    OpenPartialHomeomorph.trans_apply]
  rw [(specialFormPreservingSmoothRealChart F hF hdet g).left_inv x.2.1]

/-- At every point of the exact left coordinate image, the coordinate-image
homeomorphism is the restriction of the established common smooth chart
transition. -/
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_eq_transition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h y).1 :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) =
      specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y.1.1 := by
  let e :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph.toMeasurableEquiv
  rw [← e.apply_symm_apply y]
  exact
    coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply_eq_transition
      F hF hdet g h (e.symm y)

/-- The left overlap-coordinate map is a measurable embedding into the fixed
target subtype. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h) := by
  exact
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet g).toMeasurableEquiv.measurableEmbedding.comp
        (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)

/-- The right overlap-coordinate map is a measurable embedding into the fixed
target subtype. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h) := by
  exact
    (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
      F hF hdet h).toMeasurableEquiv.measurableEmbedding.comp
        (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h)

/-- The left chart-source measure pulled back to the common same-point overlap
subtype. -/
def specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChartSourceOverlap
      F hF hdet g h) :=
  Measure.comap
    (specialFormPreservingSmoothRealChartSourceOverlapToLeft F hF hdet g h)
    (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g)

/-- The right chart-source measure pulled back to the common same-point
overlap subtype. -/
def specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChartSourceOverlap
      F hF hdet g h) :=
  Measure.comap
    (specialFormPreservingSmoothRealChartSourceOverlapToRight F hF hdet g h)
    (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet h)

/-- The left-induced overlap measure is the fixed target measure pulled back
through the left overlap-coordinate map. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft_eq_coordinate_comap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
        F hF hdet g h =
      Measure.comap
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h)
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft,
    specialFormPreservingSmoothRealChartSourceMeasure_eq_target_comap]
  let e := specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet g
  have hi :=
    measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  exact Measure.comap_comap
    (fun s hs => hi.measurableSet_image.2 hs) he.injective
    (fun s hs => he.measurableSet_image.2 hs)
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- The right-induced overlap measure is the fixed target measure pulled back
through the right overlap-coordinate map. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight_eq_coordinate_comap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
        F hF hdet g h =
      Measure.comap
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
          F hF hdet g h)
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight,
    specialFormPreservingSmoothRealChartSourceMeasure_eq_target_comap]
  let e := specialFormPreservingSmoothRealChartSourceTargetHomeomorph
    F hF hdet h
  have hi :=
    measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  exact Measure.comap_comap
    (fun s hs => hi.measurableSet_image.2 hs) he.injective
    (fun s hs => he.measurableSet_image.2 hs)
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- Equality of the two common-overlap measures is exactly equality of the
fixed target measure pulled back through the two overlap coordinate maps. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapMeasure_eq_iff_coordinate_comap_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
          F hF hdet g h =
        specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
          F hF hdet g h ↔
      Measure.comap
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
            F hF hdet g h)
          (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet) =
        Measure.comap
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
            F hF hdet g h)
          (specialFormPreservingSmoothRealIdentityChartTargetMeasure
            F hF hdet) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft_eq_coordinate_comap,
    specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight_eq_coordinate_comap]

/-- The fixed target measure restricted to the exact left coordinate-image
subtype. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h) :=
  Measure.comap Subtype.val
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- The fixed target measure restricted to the exact right coordinate-image
subtype. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h) :=
  Measure.comap Subtype.val
    (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet)

/-- Mapping the left overlap pullback through its coordinate embedding gives
the fixed target measure restricted to the exact left coordinate image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft_coordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft_eq_coordinate_comap,
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).map_comap]

/-- Mapping the right overlap pullback through its coordinate embedding gives
the fixed target measure restricted to the exact right coordinate image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight_coordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight_eq_coordinate_comap,
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).map_comap]

/-- Mapping the left coordinate-image subtype measure back to the fixed target
gives restriction to the exact left coordinate image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft]
  exact map_comap_subtype_coe
    (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) _

/-- Mapping the right coordinate-image subtype measure back to the fixed target
gives restriction to the exact right coordinate image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight]
  exact map_comap_subtype_coe
    (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
      F hF hdet g h) _

/-- Mapping the left-induced overlap measure through its same-point inclusion
recovers the left source measure restricted to the exact overlap. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapToLeft F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet g).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromLeft,
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h).map_comap,
    range_specialFormPreservingSmoothRealChartSourceOverlapToLeft]

/-- Mapping the right-induced overlap measure through its same-point inclusion
recovers the right source measure restricted to the exact overlap. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapToRight F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceMeasure F hF hdet h).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapWithinRight
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapMeasureFromRight,
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h).map_comap,
    range_specialFormPreservingSmoothRealChartSourceOverlapToRight]

/-- Mapping the target-subtype measure back to the full coordinate model gives
exactly the coordinate measure restricted to the chart target. -/
theorem map_specialFormPreservingSmoothRealIdentityChartTargetMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet) =
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target := by
  rw [specialFormPreservingSmoothRealIdentityChartTargetMeasure]
  exact map_comap_subtype_coe
    (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).open_target.measurableSet _

/-- The identity chart transports its source measure back to the exact target
subtype measure. -/
theorem map_specialFormPreservingSmoothRealIdentityChartSourceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.map
        (specialFormPreservingSmoothRealIdentityChart
          F hF hdet).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet) =
      specialFormPreservingSmoothRealIdentityChartTargetMeasure F hF hdet := by
  rw [specialFormPreservingSmoothRealIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).toHomeomorphSourceTarget.toMeasurableEquiv

private theorem openPartialHomeomorph_apply_mem_symm_trans_source
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (A B : OpenPartialHomeomorph X E) (x : X)
    (hxA : x ∈ A.source) (hxB : x ∈ B.source) :
    A x ∈ (A.symm.trans B).source := by
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · exact A.map_source hxA
  · change A.symm (A x) ∈ B.source
    rwa [A.left_inv hxA]

private theorem fderiv_openPartialHomeomorph_chartTransition_cocycle
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A B C : OpenPartialHomeomorph X E) (x : X)
    (hxA : x ∈ A.source) (hxB : x ∈ B.source)
    (hxC : x ∈ C.source)
    (hAB : HasFDerivAt (A.symm.trans B)
      (fderiv ℝ (A.symm.trans B) (A x)) (A x))
    (hBC : HasFDerivAt (B.symm.trans C)
      (fderiv ℝ (B.symm.trans C) (B x)) (B x))
    (hAC : HasFDerivAt (A.symm.trans C)
      (fderiv ℝ (A.symm.trans C) (A x)) (A x)) :
    fderiv ℝ (A.symm.trans C) (A x) =
      (fderiv ℝ (B.symm.trans C) (B x)).comp
        (fderiv ℝ (A.symm.trans B) (A x)) := by
  have hAB_apply : (A.symm.trans B) (A x) = B x := by
    rw [OpenPartialHomeomorph.trans_apply, A.left_inv hxA]
  have hBC' : HasFDerivAt (B.symm.trans C)
      (fderiv ℝ (B.symm.trans C) (B x)) ((A.symm.trans B) (A x)) := by
    rw [hAB_apply]
    exact hBC
  have hcomp' := hBC'.comp (A x) hAB
  have hcomp : HasFDerivAt ((B.symm.trans C) ∘ (A.symm.trans B))
      ((fderiv ℝ (B.symm.trans C) (B x)).comp
        (fderiv ℝ (A.symm.trans B) (A x))) (A x) := by
    simpa only [hAB_apply] using hcomp'
  have hsourceAB :=
    openPartialHomeomorph_apply_mem_symm_trans_source A B x hxA hxB
  have hsourceAC :=
    openPartialHomeomorph_apply_mem_symm_trans_source A C x hxA hxC
  have heq : ((B.symm.trans C) ∘ (A.symm.trans B)) =ᶠ[nhds (A x)]
      (A.symm.trans C) := by
    filter_upwards
      [(A.symm.trans B).open_source.mem_nhds hsourceAB,
        (A.symm.trans C).open_source.mem_nhds hsourceAC]
      with y hyAB hyAC
    rw [OpenPartialHomeomorph.trans_source] at hyAB hyAC
    change C (B.symm (B (A.symm y))) = C (A.symm y)
    rw [B.left_inv hyAB.2]
  exact hAC.unique (hcomp.congr_of_eventuallyEq heq.symm)

/-- The ambient determinant-one matrix represented by a real skew-adjoint
identity coordinate. -/
def specialFormPreservingSmoothRealInverseCoordinateMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two).symm
      (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)).symm y)

/-- At zero, the ambient inverse-coordinate matrix has derivative the
canonical inclusion of the real skew-adjoint tangent carrier. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    HasFDerivAt
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL 0 :=
  Matrix.hasFDerivAt_specialOrthogonalSmoothIdentityInverseCoordinate_zero
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two

/-- The zero real skew-adjoint coordinate represents the matrix identity. -/
@[simp]
theorem specialFormPreservingSmoothRealInverseCoordinateMatrix_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet 0 = 1 := by
  simp [specialFormPreservingSmoothRealInverseCoordinateMatrix]

/-- The ambient inverse-coordinate matrix is maximally smooth on the
exact common target of the real centered charts. -/
theorem contDiffOn_specialFormPreservingSmoothRealInverseCoordinateMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
      (specialFormPreservingSmoothRealChart F hF hdet g).target := by
  have h :=
    Matrix.contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two
  rw [← specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g] at h
  simpa only [specialFormPreservingSmoothRealInverseCoordinateMatrix] using h

/-- The inverse-coordinate matrix has its ambient Frechet derivative
at every point of an exact real chart target. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    HasFDerivAt
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
      (fderiv ℝ
        (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet) y) y := by
  apply DifferentiableAt.hasFDerivAt
  exact
    ((contDiffOn_specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet g).differentiableOn (by simp)).differentiableAt
        ((specialFormPreservingSmoothRealChart F hF hdet g).open_target.mem_nhds hy)

/-- Chain the inverse-coordinate derivative with an arbitrary continuous
linear map without unfolding the smooth inverse-chart construction. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ)))
    (e : E →L[ℝ] (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (y : E)
    (hy : e y ∈ (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    HasFDerivAt
      (fun x => specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet (e x))
      ((fderiv ℝ
        (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
        (e y)).comp e) y :=
  (hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
    F hF hdet g (e y) hy).comp y e.hasFDerivAt

/-- The matrix coefficient in the transition from a fixed chart to the chart
centered at the point represented by `y`. -/
def specialFormPreservingSmoothRealChartCenterCoefficient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)⁻¹ * g).1.1.1 :
    Matrix (Fin n) (Fin n) ℝ)

/-- Every available inverse-coordinate matrix has determinant one. -/
theorem det_specialFormPreservingSmoothRealInverseCoordinateMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet y.1).det = 1 := by
  have htarget : (specialFormPreservingSmoothRealChart F hF hdet g).target =
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g
  let yc : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two := ⟨y.1, htarget ▸ y.2⟩
  let q :=
    (Matrix.specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two).symm yc
  have hq := Matrix.det_eq_one_of_mem_specialOrthogonalSmoothIdentityZeroFiber
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two q.1 q.2
  simpa only [q, yc, specialFormPreservingSmoothRealInverseCoordinateMatrix,
    Matrix.coe_specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph_symm_apply]
    using hq

/-- In fixed coordinates the varying-center coefficient is independent of the
fixed center: it is the adjugate of the determinant-one inverse coordinate. -/
theorem specialFormPreservingSmoothRealChartCenterCoefficient_eq_adjugate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y =
      (specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet y.1).adjugate := by
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let x := A.symm y.1
  let q := specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet y.1
  have htarget : (specialFormPreservingSmoothRealChart F hF hdet g).target =
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g
  let yc : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two := ⟨y.1, htarget ▸ y.2⟩
  have hx : x.1.1.1 = g.1.1.1 * q := by
    simpa only [A, x, q, yc,
      specialFormPreservingSmoothRealInverseCoordinateMatrix]
      using
        coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g yc
  have hleft :
      specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y * q = 1 := by
    change (x⁻¹).1.1.1 * g.1.1.1 * q = 1
    rw [Matrix.mul_assoc, ← hx]
    change ((x⁻¹ * x).1.1.1 : Matrix (Fin n) (Fin n) ℝ) = 1
    simp
  have hdetq : q.det = 1 := by
    exact det_specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet g y
  calc
    specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y =
        specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y * 1 :=
      (Matrix.mul_one _).symm
    _ = specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y *
        (q * q.adjugate) := by rw [Matrix.mul_adjugate, hdetq, one_smul]
    _ = (specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g y * q) *
        q.adjugate := by rw [Matrix.mul_assoc]
    _ = q.adjugate := by rw [hleft, Matrix.one_mul]

/-- The ambient varying-center coefficient formula is maximally smooth on the
exact common target of every fixed centered chart. -/
theorem contDiffOn_specialFormPreservingSmoothRealChartCenterCoefficient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    ContDiffOn ℝ ∞ (fun y =>
      (specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet y).adjugate)
      (specialFormPreservingSmoothRealChart F hF hdet g).target := by
  have hq :=
    Matrix.contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two
  rw [← specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g] at hq
  have hq' : ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
      (specialFormPreservingSmoothRealChart F hF hdet g).target := by
    simpa only [specialFormPreservingSmoothRealInverseCoordinateMatrix] using hq
  exact Matrix.contDiff_adjugate_real.comp_contDiffOn hq'

/-- The ambient forward coordinate from a real determinant-one matrix to the
fixed skew-adjoint model. -/
def specialFormPreservingSmoothRealForwardCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (q : Matrix (Fin n) (Fin n) ℝ) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two q).snd

/-- The ambient real forward coordinate is maximally smooth on the full
matrix space. -/
theorem contDiff_specialFormPreservingSmoothRealForwardCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    ContDiff ℝ ∞
      (specialFormPreservingSmoothRealForwardCoordinate F hF hdet) := by
  apply (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
    (F.map (algebraMap ℚ ℝ))
    (realChart_isSymm_map_algebraMap F hF)).contDiff.comp
  apply contDiff_snd.comp
  simpa [Matrix.symmetricFormPreservingSmoothDetOneIdentityChart,
    Matrix.symmetricFormPreservingSmoothIdentityChart] using
      (Matrix.contDiff_symmetricFormPreservingIdentityChart
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two).of_le
          (show (∞ : WithTop ℕ∞) ≤ ⊤ by simp)

/-- On a real skew-adjoint line through the identity, the ambient
forward coordinate is exactly the tangent parameter. -/
theorem specialFormPreservingSmoothRealForwardCoordinate_one_add
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealForwardCoordinate F hF hdet
        (1 + (X : Matrix (Fin n) (Fin n) ℝ)) = X :=
  Matrix.specialOrthogonalSmoothIdentityForwardCoordinate_one_add
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two X

/-- The derivative of the ambient forward coordinate at the matrix identity
is inverse to the tangent-carrier inclusion. -/
theorem fderiv_specialFormPreservingSmoothRealForwardCoordinate_one_comp_subtypeL
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (fderiv ℝ
      (specialFormPreservingSmoothRealForwardCoordinate F hF hdet) 1).comp
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  rw [show fderiv ℝ
      (specialFormPreservingSmoothRealForwardCoordinate F hF hdet) 1 =
        Matrix.specialOrthogonalSmoothIdentityForwardCoordinateDerivative
          (F.map (algebraMap ℚ ℝ))
          (realChart_isSymm_map_algebraMap F hF) from
    (Matrix.hasFDerivAt_specialOrthogonalSmoothIdentityForwardCoordinate
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two 1).fderiv]
  exact
    Matrix.specialOrthogonalSmoothIdentityForwardCoordinateDerivative_comp_subtypeL
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)

/-- The two-coordinate real transition formula whose first coordinate chooses
the moving center and whose second coordinate is the transition input. -/
def specialFormPreservingSmoothRealJointTransitionCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (p : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ×
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  specialFormPreservingSmoothRealForwardCoordinate F hF hdet
    ((specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet p.1).adjugate *
      specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet p.2)

/-- The explicit two-coordinate real transition formula is maximally smooth
on the product of the exact common chart targets. -/
theorem contDiffOn_specialFormPreservingSmoothRealJointTransitionCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet)
      ((specialFormPreservingSmoothRealChart F hF hdet g).target ×ˢ
        (specialFormPreservingSmoothRealChart F hF hdet g).target) := by
  let t := (specialFormPreservingSmoothRealChart F hF hdet g).target
  have hcoeff : ContDiffOn ℝ ∞ (fun y =>
      (specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet y).adjugate) t :=
    contDiffOn_specialFormPreservingSmoothRealChartCenterCoefficient
      F hF hdet g
  have hinv : ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet) t := by
    have hq :=
      Matrix.contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two
    rw [← specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g] at hq
    simpa only [t, specialFormPreservingSmoothRealInverseCoordinateMatrix] using hq
  have hleft : ContDiffOn ℝ ∞ (fun p =>
      (specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet p.1).adjugate) (t ×ˢ t) :=
    hcoeff.comp contDiffOn_fst (fun _ hp => hp.1)
  have hright : ContDiffOn ℝ ∞ (fun p =>
      specialFormPreservingSmoothRealInverseCoordinateMatrix
        F hF hdet p.2) (t ×ˢ t) :=
    hinv.comp contDiffOn_snd (fun _ hp => hp.2)
  exact
    (contDiff_specialFormPreservingSmoothRealForwardCoordinate
      F hF hdet).comp_contDiffOn (hleft.mul hright)

/-- On exact target coordinates, the joint formula uses the actual coefficient
of every supplied fixed centered chart. -/
theorem specialFormPreservingSmoothRealJointTransitionCoordinate_eq_coefficient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y z : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet (y.1, z.1) =
      specialFormPreservingSmoothRealForwardCoordinate F hF hdet
        (specialFormPreservingSmoothRealChartCenterCoefficient
          F hF hdet g y *
          specialFormPreservingSmoothRealInverseCoordinateMatrix
            F hF hdet z.1) := by
  rw [specialFormPreservingSmoothRealJointTransitionCoordinate,
    specialFormPreservingSmoothRealChartCenterCoefficient_eq_adjugate]

/-- On its exact source, the real identity-centered partial chart is the
ambient forward coordinate of the underlying matrix. -/
theorem specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (q : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (hq : q ∈ (specialFormPreservingSmoothRealIdentityChart F hF hdet).source) :
    specialFormPreservingSmoothRealIdentityChart F hF hdet q =
      specialFormPreservingSmoothRealForwardCoordinate F hF hdet q.1.1.1 := by
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    at hq
  let qs : specialFormPreservingSmoothTranslatedChartNeighborhood
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two 1 := ⟨q, hq⟩
  rw [show specialFormPreservingSmoothRealIdentityChart F hF hdet q =
      (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two 1 qs :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule) by
    exact
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two 1 qs]
  apply Subtype.ext
  rw [specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply]
  simp only [specialFormPreservingSmoothRealForwardCoordinate,
    Matrix.coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply,
    inv_one, one_mul]
  rfl

/-- On its exact source, a real transition is the identity chart applied to
the represented group point translated by the inverse target center. This form
fixes the private real chart normalization proofs. -/
theorem specialFormPreservingSmoothRealSkewAdjointTransition_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).source) :
    specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y =
      specialFormPreservingSmoothRealIdentityChart F hF hdet
        (h⁻¹ * (specialFormPreservingSmoothRealChart F hF hdet g).symm y) :=
  specialFormPreservingSmoothSkewAdjointTransition_apply
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g h y hy

/-- For a fixed first coordinate, the joint formula agrees on the exact
transition source with the existing transition to the chart centered at the
represented point. -/
theorem specialFormPreservingSmoothRealJointTransitionCoordinate_slice_eqOn
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    Set.EqOn
      (fun z => specialFormPreservingSmoothRealJointTransitionCoordinate
        F hF hdet (y.1, z))
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g
        ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1))
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g
        ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)).source := by
  intro z hz
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let x := A.symm y.1
  have hztarget : z ∈ A.target := by
    have hz' := hz
    rw [specialFormPreservingSmoothSkewAdjointTransition_source] at hz'
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target]
    exact hz'.1
  let zs : A.target := ⟨z, hztarget⟩
  change specialFormPreservingSmoothRealJointTransitionCoordinate
      F hF hdet (y.1, z) =
    specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g x z
  rw [show specialFormPreservingSmoothRealJointTransitionCoordinate
      F hF hdet (y.1, z) =
        specialFormPreservingSmoothRealForwardCoordinate F hF hdet
          (specialFormPreservingSmoothRealChartCenterCoefficient
            F hF hdet g y *
            specialFormPreservingSmoothRealInverseCoordinateMatrix
              F hF hdet z) by
    simpa only [A, zs] using
      specialFormPreservingSmoothRealJointTransitionCoordinate_eq_coefficient
        F hF hdet g y zs]
  rw [specialFormPreservingSmoothSkewAdjointTransition_apply
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g x z hz]
  have hxsource : A.symm z ∈
      (specialFormPreservingSmoothRealChart F hF hdet x).source := by
    have hz' := hz
    rw [specialFormPreservingSmoothSkewAdjointTransition,
      OpenPartialHomeomorph.trans_source] at hz'
    exact hz'.2
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    at hxsource
  rcases hxsource with ⟨w, hw, hwx⟩
  have hshift : x⁻¹ * A.symm z = w := by
    rw [← hwx]
    simp
  have hqidentity : x⁻¹ * A.symm z ∈
      specialFormPreservingSmoothIdentityChartNeighborhood
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two := by
    rwa [hshift]
  have hqsource : x⁻¹ * A.symm z ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).source := by
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    exact ⟨x⁻¹ * A.symm z, hqidentity, one_mul _⟩
  rw [specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
    F hF hdet (x⁻¹ * A.symm z) hqsource]
  apply congrArg (specialFormPreservingSmoothRealForwardCoordinate F hF hdet)
  have htarget : A.target =
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g
  let zc : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two := ⟨z, htarget ▸ hztarget⟩
  have hAz :=
    coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g zc
  change ((A.symm y.1)⁻¹ * g).1.1.1 *
      specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet z =
    (x⁻¹).1.1.1 * (A.symm z).1.1.1
  rw [hAz]
  change ((x⁻¹).1.1.1 * g.1.1.1) *
      specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet z =
    (x⁻¹).1.1.1 * (g.1.1.1 *
      specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet z)
  exact Matrix.mul_assoc _ _ _

/-- At every point of the exact transition source, a fixed-first-coordinate
slice of the joint formula eventually equals the existing moving-center
transition. -/
theorem specialFormPreservingSmoothRealJointTransitionCoordinate_slice_eventuallyEq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target)
    (z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hz : z ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g
      ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)).source) :
    (fun w => specialFormPreservingSmoothRealJointTransitionCoordinate
      F hF hdet (y.1, w)) =ᶠ[nhds z]
        specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g
          ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1) := by
  let t := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g
    ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)
  filter_upwards [t.open_source.mem_nhds hz] with w hw
  exact specialFormPreservingSmoothRealJointTransitionCoordinate_slice_eqOn
    F hF hdet g y hw

/-- The continuous linear inclusion of the skew-adjoint model into the second
factor of its product with itself. -/
def specialFormPreservingSmoothRealSecondFactorInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ×
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  ContinuousLinearMap.inr ℝ _ _

@[simp]
theorem specialFormPreservingSmoothRealSecondFactorInclusion_apply
    (F : Matrix (Fin n) (Fin n) ℚ)
    (v : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealSecondFactorInclusion F v = (0, v) :=
  rfl

/-- At an exact transition-source point, the existing transition derivative
is the joint-map derivative composed with the second-factor inclusion. -/
theorem fderiv_specialFormPreservingSmoothRealTransition_eq_joint_comp_secondFactor
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target)
    (z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hz : z ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g
      ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)).source) :
    fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g
          ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)) z =
      (fderiv ℝ
        (specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet)
        (y.1, z)).comp
          (specialFormPreservingSmoothRealSecondFactorInclusion F) := by
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let J := specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet
  let T := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g (A.symm y.1)
  have hztarget : z ∈ A.target := by
    have hz' := hz
    rw [specialFormPreservingSmoothSkewAdjointTransition_source] at hz'
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target]
    exact hz'.1
  have hJ : DifferentiableAt ℝ J (y.1, z) :=
    ((contDiffOn_specialFormPreservingSmoothRealJointTransitionCoordinate
      F hF hdet g).differentiableOn (by simp)).differentiableAt
        ((A.open_target.prod A.open_target).mem_nhds ⟨y.2, hztarget⟩)
  have hi : HasFDerivAt (fun w => (y.1, w))
      (specialFormPreservingSmoothRealSecondFactorInclusion F) z := by
    exact hasFDerivAt_prodMk_right y.1 z
  have hslice :
      fderiv ℝ (fun w => J (y.1, w)) z =
        (fderiv ℝ J (y.1, z)).comp
          (specialFormPreservingSmoothRealSecondFactorInclusion F) := by
    exact (hJ.hasFDerivAt.comp z hi).fderiv
  have heventually : (fun w => J (y.1, w)) =ᶠ[nhds z] T := by
    simpa only [A, J, T] using
      specialFormPreservingSmoothRealJointTransitionCoordinate_slice_eventuallyEq
        F hF hdet g y z hz
  calc
    fderiv ℝ T z = fderiv ℝ (fun w => J (y.1, w)) z :=
      heventually.fderiv_eq.symm
    _ = (fderiv ℝ J (y.1, z)).comp
        (specialFormPreservingSmoothRealSecondFactorInclusion F) := hslice

/-- The absolute Jacobian of the second-variable derivative of the joint real
transition formula, restricted to the diagonal. -/
def specialFormPreservingSmoothRealDiagonalPartialJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  |((fderiv ℝ
      (specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet)
      (y, y)).comp
        (specialFormPreservingSmoothRealSecondFactorInclusion F)).det|

/-- The diagonal second-variable Jacobian is continuous on the exact common
target of every fixed real chart. -/
theorem continuousOn_specialFormPreservingSmoothRealDiagonalPartialJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    ContinuousOn
      (specialFormPreservingSmoothRealDiagonalPartialJacobian F hF hdet)
      (specialFormPreservingSmoothRealChart F hF hdet g).target := by
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let J := specialFormPreservingSmoothRealJointTransitionCoordinate F hF hdet
  let ι₂ := specialFormPreservingSmoothRealSecondFactorInclusion F
  have hderiv : ContinuousOn (fderiv ℝ J) (A.target ×ˢ A.target) :=
    (contDiffOn_specialFormPreservingSmoothRealJointTransitionCoordinate
      F hF hdet g).continuousOn_fderiv_of_isOpen
        (A.open_target.prod A.open_target) (by simp)
  have hdiag : ContinuousOn (fun y => (y, y)) A.target :=
    (continuous_id.prodMk continuous_id).continuousOn
  have hdiagderiv : ContinuousOn (fun y => fderiv ℝ J (y, y)) A.target :=
    hderiv.comp hdiag (fun _ hy => ⟨hy, hy⟩)
  have hpartial : ContinuousOn (fun y => (fderiv ℝ J (y, y)).comp ι₂) A.target :=
    continuous_id.clm_comp_const ι₂ |>.comp_continuousOn hdiagderiv
  exact continuous_abs.comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn hpartial)

/-- The varying-center matrix coefficient is continuous on the exact common
target-coordinate subtype. -/
theorem continuous_specialFormPreservingSmoothRealChartCenterCoefficient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Continuous (specialFormPreservingSmoothRealChartCenterCoefficient F hF hdet g) := by
  have hqOn : ContinuousOn
      (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
      (Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two) :=
    (Matrix.contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two).continuousOn
  rw [← specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g] at hqOn
  have hq : Continuous
      (fun y : (specialFormPreservingSmoothRealChart F hF hdet g).target ↦
        specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet y.1) :=
    continuousOn_iff_continuous_restrict.mp hqOn
  apply Continuous.congr hq.matrix_adjugate
  intro y
  exact (specialFormPreservingSmoothRealChartCenterCoefficient_eq_adjugate
    F hF hdet g y).symm

/-- The absolute coefficient of the invariant top form in a fixed centered
chart, evaluated at a represented point of that chart source. It is the
Jacobian from the fixed chart to the preferred chart centered at the point. -/
def specialFormPreservingSmoothRealChartDensityAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) : ℝ :=
  |(fderiv ℝ
    ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet x.1))
    (specialFormPreservingSmoothRealChart F hF hdet g x.1)).det|

/-- The pointwise invariant-form coefficient expressed on the exact target
coordinate subtype of one fixed centered chart. -/
def specialFormPreservingSmoothRealChartCoordinateDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) : ℝ :=
  specialFormPreservingSmoothRealChartDensityAt F hF hdet g
    ⟨(specialFormPreservingSmoothRealChart F hF hdet g).symm y.1,
      (specialFormPreservingSmoothRealChart F hF hdet g).symm.map_source y.2⟩

/-- On target coordinates, the pointwise density is the absolute determinant
of the transition to the chart centered at the represented point. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensity_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g y =
      |(fderiv ℝ
        ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
          (specialFormPreservingSmoothRealChart F hF hdet
            ((specialFormPreservingSmoothRealChart F hF hdet g).symm y.1)))
        y.1).det| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity,
    specialFormPreservingSmoothRealChartDensityAt]
  rw [(specialFormPreservingSmoothRealChart F hF hdet g).right_inv y.2]

/-- The coordinate of a represented source point lies in the exact transition
source from its fixed chart to the chart centered at that point. -/
theorem specialFormPreservingSmoothRealChart_coordinate_mem_transition_to_self_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    specialFormPreservingSmoothRealChart F hF hdet g x.1 ∈
      ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
        (specialFormPreservingSmoothRealChart F hF hdet x.1)).source := by
  apply openPartialHomeomorph_apply_mem_symm_trans_source
  · exact x.2
  · exact
      self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two x.1

/-- The transition from a real chart to the chart centered at a
represented source point sends that point's coordinate to zero. -/
@[simp]
theorem specialFormPreservingSmoothRealChart_transition_to_self_apply_coordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet x.1))
        (specialFormPreservingSmoothRealChart F hF hdet g x.1) =
      0 := by
  rw [OpenPartialHomeomorph.trans_apply,
    (specialFormPreservingSmoothRealChart F hF hdet g).left_inv x.2,
    specialFormPreservingSmoothRealChart_center]

/-- The pointwise coordinate density is the diagonal absolute Jacobian of the
joint transition's second-variable derivative. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g y =
      specialFormPreservingSmoothRealDiagonalPartialJacobian F hF hdet y.1 := by
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let x : A.source := ⟨A.symm y.1, A.symm.map_source y.2⟩
  have hsource : y.1 ∈
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g (A.symm y.1)).source := by
    have hx :=
      specialFormPreservingSmoothRealChart_coordinate_mem_transition_to_self_source
        F hF hdet g x
    let s := (A.symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet (A.symm y.1))).source
    change y.1 ∈ s
    have hx' : A (A.symm y.1) ∈ s := by
      simpa only [s, A, x] using hx
    rw [← A.right_inv y.2]
    exact hx'
  rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq]
  change |(fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g (A.symm y.1)) y.1).det| = _
  rw [fderiv_specialFormPreservingSmoothRealTransition_eq_joint_comp_secondFactor
    F hF hdet g y y.1 hsource]
  rfl

/-- The invariant-form coordinate density is continuous on every exact real
chart target subtype. -/
theorem continuous_specialFormPreservingSmoothRealChartCoordinateDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Continuous
      (specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g) := by
  have hpartial : Continuous (fun y :
      (specialFormPreservingSmoothRealChart F hF hdet g).target =>
        specialFormPreservingSmoothRealDiagonalPartialJacobian
          F hF hdet y.1) :=
    continuousOn_iff_continuous_restrict.mp
      (continuousOn_specialFormPreservingSmoothRealDiagonalPartialJacobian
        F hF hdet g)
  apply Continuous.congr hpartial
  intro y
  exact (specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian
    F hF hdet g y).symm

/-- The invariant-form coordinate density in the nonnegative extended reals,
as required by `Measure.withDensity`. -/
def specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) : ENNReal :=
  ENNReal.ofReal
    (specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g y)

/-- The extended-real coordinate density is continuous on the exact chart
target subtype. -/
theorem continuous_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Continuous
      (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet g) :=
  ENNReal.continuous_ofReal.comp
    (continuous_specialFormPreservingSmoothRealChartCoordinateDensity
      F hF hdet g)

/-- The extended-real coordinate density is measurable on the exact chart
target subtype. -/
theorem measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable
      (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet g) :=
  (continuous_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    F hF hdet g).measurable

/-- The invariant-form measure in one exact real chart target, obtained by
weighting the fixed coordinate measure by the chart's continuous density. -/
def specialFormPreservingSmoothRealChartTargetDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChart F hF hdet g).target :=
  (Measure.comap Subtype.val
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).withDensity
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g)

/-- On a measurable target set, the chart-local density measure is the
corresponding lower integral against the fixed coordinate measure. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    {s : Set (specialFormPreservingSmoothRealChart F hF hdet g).target}
    (hs : MeasurableSet s) :
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g s =
      ∫⁻ y in s,
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet g y
        ∂(Measure.comap Subtype.val
          (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure,
    withDensity_apply _ hs]

/-- Each chart-local density measure is absolutely continuous with respect to
the fixed coordinate measure on the exact target subtype. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_absolutelyContinuous
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g ≪
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  exact withDensity_absolutelyContinuous _ _

set_option backward.isDefEq.respectTransparency false in
/-- Each chart-local density measure is locally finite, stated without
installing a measure instance. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) := by
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  letI : IsLocallyFiniteMeasure
      (Measure.comap
        ((↑) : (specialFormPreservingSmoothRealChart F hF hdet g).target →
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule) μ) := by
    refine ⟨fun y ↦ ?_⟩
    rcases μ.exists_isOpen_measure_lt_top y.1 with ⟨U, hyU, hU, hμU⟩
    refine ⟨Subtype.val ⁻¹' U,
      hU.preimage continuous_subtype_val |>.mem_nhds hyU, ?_⟩
    rw [comap_subtype_coe_apply
      (specialFormPreservingSmoothRealChart F hF hdet g).open_target.measurableSet]
    apply (measure_mono ?_).trans_lt hμU
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  simpa only [specialFormPreservingSmoothRealChartCoordinateDensityENNReal] using
    IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g)

set_option backward.isDefEq.respectTransparency false in
/-- Each chart-local density measure is sigma-finite, stated without
installing a measure instance. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_sigmaFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    SigmaFinite
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) := by
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_isLocallyFinite
      F hF hdet g
  infer_instance

/-- Each chart-local density measure is finite on compact sets, stated
without installing a measure instance. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_isFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsFiniteMeasureOnCompacts
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) := by
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_isLocallyFinite
      F hF hdet g
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Each chart-local density measure is regular, stated without installing a
measure instance. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_regular
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.Regular
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) := by
  letI : LocallyCompactSpace
      (specialFormPreservingSmoothRealChart F hF hdet g).target :=
    (specialFormPreservingSmoothRealChart F hF hdet g).open_target.locallyCompactSpace
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_isLocallyFinite
      F hF hdet g
  infer_instance

/-- The exact left overlap-coordinate image, expressed in the native target
subtype of the left centered chart. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingSmoothRealChart F hF hdet g).target :=
  specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet g ⁻¹'
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h

/-- The exact right overlap-coordinate image, expressed in the native target
subtype of the right centered chart. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingSmoothRealChart F hF hdet h).target :=
  specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet h ⁻¹'
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
      F hF hdet g h

/-- The native left target image of an exact overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h) :=
  (specialFormPreservingSmoothRealChartTargetHomeomorph
    F hF hdet g).continuous.measurable
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h)

/-- The native right target image of an exact overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h) :=
  (specialFormPreservingSmoothRealChartTargetHomeomorph
    F hF hdet h).continuous.measurable
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h)

/-- Restricting a chart-local density measure to a measurable target set is
the same as first restricting the fixed coordinate measure and then applying
the same density. -/
theorem restrict_specialFormPreservingSmoothRealChartTargetDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    {s : Set (specialFormPreservingSmoothRealChart F hF hdet g).target}
    (hs : MeasurableSet s) :
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet g).restrict s =
      ((Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).restrict s).withDensity
        (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet g) := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure,
    restrict_withDensity hs]

/-- The left chart-local density measure has the expected with-density form
after restriction to the exact native left overlap-coordinate image. -/
theorem restrict_specialFormPreservingSmoothRealChartTargetDensityMeasure_overlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet g).restrict
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h) =
      ((Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).restrict
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
            F hF hdet g h)).withDensity
        (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet g) :=
  restrict_specialFormPreservingSmoothRealChartTargetDensityMeasure
    F hF hdet g
      (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h)

/-- The right chart-local density measure has the expected with-density form
after restriction to the exact native right overlap-coordinate image. -/
theorem restrict_specialFormPreservingSmoothRealChartTargetDensityMeasure_overlapCoordinateImageFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet h).restrict
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
          F hF hdet g h) =
      ((Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).restrict
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
            F hF hdet g h)).withDensity
        (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet h) :=
  restrict_specialFormPreservingSmoothRealChartTargetDensityMeasure
    F hF hdet h
      (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h)

/-- The native left target image is homeomorphic to its realization in the
fixed identity-chart target. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h :=
  (specialFormPreservingSmoothRealChartTargetHomeomorph
    F hF hdet g).sets rfl

/-- The native right target image is homeomorphic to its realization in the
fixed identity-chart target. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h :=
  (specialFormPreservingSmoothRealChartTargetHomeomorph
    F hF hdet h).sets rfl

/-- The native-to-fixed left image homeomorphism does not change the
underlying coordinate point. -/
private theorem coe_specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h y).1.1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1.1 := by
  exact coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
    F hF hdet g y.1

/-- The native-to-fixed right image homeomorphism does not change the
underlying coordinate point. -/
private theorem coe_specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
      F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h y).1.1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1.1 := by
  exact coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
    F hF hdet h y.1

private theorem map_comap_comap_measurableEquiv
    {A A' B B' X : Type*}
    [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace B]
    [MeasurableSpace B'] [MeasurableSpace X]
    (e : A ≃ᵐ B)
    (i : A → A') (j : A' → X)
    (k : B → B') (l : B' → X)
    (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (hk : MeasurableEmbedding k) (hl : MeasurableEmbedding l)
    (hcomm : ∀ a, l (k (e a)) = j (i a))
    (μ : Measure X) :
    Measure.map e (Measure.comap i (Measure.comap j μ)) =
      Measure.comap k (Measure.comap l μ) := by
  ext s hs
  rw [e.map_apply, hi.comap_apply, hj.comap_apply,
    hk.comap_apply, hl.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨k (e a), ⟨e a, ha, rfl⟩, hcomm a⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    let a := e.symm b
    refine ⟨i a, ⟨a, ?_, rfl⟩, ?_⟩
    · simpa [a] using hb
    · rw [← hcomm a]
      simp [a]

/-- Pushing the native left coordinate-base measure to the fixed target image
gives the existing fixed coordinate-image measure. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateBaseMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h)
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :
          Measure
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
              F hF hdet g h)) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft,
    specialFormPreservingSmoothRealIdentityChartTargetMeasure]
  apply map_comap_comap_measurableEquiv
    (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h).toMeasurableEquiv
    Subtype.val Subtype.val Subtype.val Subtype.val
  · exact MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h)
  · exact MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealChart F hF hdet g).open_target.measurableSet
  · exact MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h)
  · exact MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet
  · exact
      coe_specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph_apply
        F hF hdet g h

/-- Pushing the native right coordinate-base measure to the fixed target image
gives the existing fixed coordinate-image measure. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateBaseMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
          F hF hdet g h)
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :
          Measure
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
              F hF hdet g h)) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight,
    specialFormPreservingSmoothRealIdentityChartTargetMeasure]
  apply map_comap_comap_measurableEquiv
    (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h).toMeasurableEquiv
    Subtype.val Subtype.val Subtype.val Subtype.val
  · exact MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h)
  · exact MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealChart F hF hdet h).open_target.measurableSet
  · exact MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h)
  · exact MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet
  · exact
      coe_specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph_apply
        F hF hdet g h

/-- The exact coordinate transition between the native left and right target
images, obtained by conjugating the common-target transition. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h :=
  (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
    F hF hdet g h).trans
      ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h).trans
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
            F hF hdet g h).symm)

/-- Conjugating the native target-image transition back to the fixed target
recovers the established common-target image homeomorphism. -/
theorem specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
        F hF hdet g h
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
          F hF hdet g h y) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h y) := by
  simp [specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph]

/-- After identifying the native images with the fixed target, the native
homeomorphism is pointwise the established common smooth chart transition. -/
theorem coe_specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph_eq_transition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
        F hF hdet g h y)).1.1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) =
      specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h
        ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h y).1.1 :
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  rw [specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph_apply]
  exact
    coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_eq_transition
      F hF hdet g h
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h y)

/-- The left chart-density measure pulled back to its exact native overlap
coordinate-image subtype. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h) :=
  Measure.comap Subtype.val
    (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g)

/-- The right chart-density measure pulled back to its exact native overlap
coordinate-image subtype. -/
def specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h) :=
  Measure.comap Subtype.val
    (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet h)

/-- Mapping the native left image measure back to the full centered target
recovers the left chart-density measure restricted to that exact image. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g).restrict
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft]
  exact map_comap_subtype_coe
    (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h) _

/-- Mapping the native right image measure back to the full centered target
recovers the right chart-density measure restricted to that exact image. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet h).restrict
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight]
  exact map_comap_subtype_coe
    (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
      F hF hdet g h) _

/-- The native transition pushforward, expressed after returning its values to
the fixed target, is the pushforward by the established common-target
transition after first returning the source values to that target. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_fixedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (fun y =>
          specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
            F hF hdet g h
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
              F hF hdet g h y))
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) =
      Measure.map
        (fun y =>
          specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
            F hF hdet g h
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
              F hF hdet g h y))
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) := by
  apply Measure.map_congr
  filter_upwards [] with y
  exact
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph_apply
      F hF hdet g h y

private theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : α → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

private theorem comap_subtype_withDensity
    {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (f : α → ENNReal) :
    Measure.comap Subtype.val (μ.withDensity f) =
      (Measure.comap Subtype.val μ).withDensity
        (f ∘ Subtype.val : s → ENNReal) := by
  ext t ht
  rw [comap_subtype_coe_apply hs, withDensity_apply _
      ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 ht),
    withDensity_apply _ ht]
  change (∫⁻ a in Subtype.val '' t, f a ∂μ) =
    ∫⁻ x : s in t, f x ∂Measure.comap Subtype.val μ
  rw [setLIntegral_subtype hs t f]

/-- The left chart density represented on the exact left coordinate image in
the fixed identity-chart target. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) : ENNReal :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet g
    ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h).symm y).1

/-- The right chart density represented on the exact right coordinate image
in the fixed identity-chart target. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
      F hF hdet g h) : ENNReal :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet h
    ((specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h).symm y).1

/-- The fixed-target representation of the left chart density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
        F hF hdet g h) := by
  exact
    (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g).comp
        (measurable_subtype_coe.comp
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
            F hF hdet g h).symm.measurable)

/-- The fixed-target representation of the right chart density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
        F hF hdet g h) := by
  exact
    (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet h).comp
        (measurable_subtype_coe.comp
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
            F hF hdet g h).symm.measurable)

/-- In fixed-target coordinates, the left native image measure is its pushed
coordinate-base measure weighted by the inverse-pulled left chart density. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_eq_fixedTarget_withDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) =
      (Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h)
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :
          Measure
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
              F hF hdet g h))).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft,
    specialFormPreservingSmoothRealChartTargetDensityMeasure]
  rw [comap_subtype_withDensity
    (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h)]
  let e :=
    (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h).toMeasurableEquiv
  change Measure.map e (Measure.withDensity _ _) = (Measure.map e _).withDensity _
  rw [map_withDensity_measurableEquiv e _
    ((measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g).comp measurable_subtype_coe)]
  rfl

/-- In fixed-target coordinates, the right native image measure is its pushed
coordinate-base measure weighted by the inverse-pulled right chart density. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight_eq_fixedTarget_withDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
          F hF hdet g h) =
      (Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
          F hF hdet g h)
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :
          Measure
            (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
              F hF hdet g h))).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h) := by
  rw [specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight,
    specialFormPreservingSmoothRealChartTargetDensityMeasure]
  rw [comap_subtype_withDensity
    (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
      F hF hdet g h)]
  let e :=
    (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h).toMeasurableEquiv
  change Measure.map e (Measure.withDensity _ _) = (Measure.map e _).withDensity _
  rw [map_withDensity_measurableEquiv e _
    ((measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet h).comp measurable_subtype_coe)]
  rfl

/-- The left native image density measure, in fixed-target coordinates, is the
canonical left coordinate-image measure with the inverse-pulled chart density. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_eq_coordinateImageMeasure_withDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
            F hF hdet g h) := by
  rw [
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_eq_fixedTarget_withDensity,
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateBaseMeasureFromLeft]

/-- The right native image density measure, in fixed-target coordinates, is the
canonical right coordinate-image measure with the inverse-pulled chart density. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight_eq_coordinateImageMeasure_withDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
            F hF hdet g h) := by
  rw [
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight_eq_fixedTarget_withDensity,
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateBaseMeasureFromRight]

/-- The common smooth real transition has its ambient Frechet derivative at
every point of its exact open source. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).source) :
    HasFDerivAt
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h)
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y) y := by
  apply DifferentiableAt.hasFDerivAt
  exact
    ((contDiffOn_infty_specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).differentiableOn (by simp)).differentiableAt
      ((specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).open_source.mem_nhds hy)

/-- For fixed chart centers, the ambient derivative of the real transition is
continuous on its exact open source. This does not vary either center. -/
theorem continuousOn_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    ContinuousOn
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h))
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).source := by
  exact
    (contDiffOn_infty_specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).continuousOn_fderiv_of_isOpen
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h).open_source (by simp)

/-- For fixed chart centers, the absolute Jacobian of the real transition is
continuous on its exact open source. -/
theorem continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    ContinuousOn
      (fun y ↦ |(fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y).det|)
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).source := by
  exact continuous_abs.comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h))

/-- At one represented overlap point, the derivative from a fixed chart to
the chart centered at that point factors through any second fixed chart. -/
theorem fderiv_specialFormPreservingSmoothRealChartTransition_to_self_cocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    fderiv ℝ
        ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
          (specialFormPreservingSmoothRealChart F hF hdet x.1))
        (specialFormPreservingSmoothRealChart F hF hdet g x.1) =
      (fderiv ℝ
        ((specialFormPreservingSmoothRealChart F hF hdet h).symm.trans
          (specialFormPreservingSmoothRealChart F hF hdet x.1))
        (specialFormPreservingSmoothRealChart F hF hdet h x.1)).comp
        (fderiv ℝ
          ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
            (specialFormPreservingSmoothRealChart F hF hdet h))
          (specialFormPreservingSmoothRealChart F hF hdet g x.1)) := by
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let B := specialFormPreservingSmoothRealChart F hF hdet h
  let C := specialFormPreservingSmoothRealChart F hF hdet x.1
  have hxC : x.1 ∈ C.source :=
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two x.1
  have hsourceAB : A x.1 ∈ (A.symm.trans B).source :=
    openPartialHomeomorph_apply_mem_symm_trans_source
      A B x.1 x.2.1 x.2.2
  have hsourceBC : B x.1 ∈ (B.symm.trans C).source :=
    openPartialHomeomorph_apply_mem_symm_trans_source
      B C x.1 x.2.2 hxC
  have hsourceAC : A x.1 ∈ (A.symm.trans C).source :=
    openPartialHomeomorph_apply_mem_symm_trans_source
      A C x.1 x.2.1 hxC
  apply fderiv_openPartialHomeomorph_chartTransition_cocycle
    A B C x.1 x.2.1 x.2.2 hxC
  · exact hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet g h (A x.1) hsourceAB
  · exact hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet h x.1 (B x.1) hsourceBC
  · exact hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet g x.1 (A x.1) hsourceAC

/-- The pointwise chart density transforms by the absolute ambient Jacobian
of a fixed-center transition. -/
theorem specialFormPreservingSmoothRealChartDensityAt_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    specialFormPreservingSmoothRealChartDensityAt F hF hdet g ⟨x.1, x.2.1⟩ =
      specialFormPreservingSmoothRealChartDensityAt F hF hdet h ⟨x.1, x.2.2⟩ *
        |(fderiv ℝ
          ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
            (specialFormPreservingSmoothRealChart F hF hdet h))
          (specialFormPreservingSmoothRealChart F hF hdet g x.1)).det| := by
  rw [specialFormPreservingSmoothRealChartDensityAt,
    specialFormPreservingSmoothRealChartDensityAt,
    fderiv_specialFormPreservingSmoothRealChartTransition_to_self_cocycle
      F hF hdet g h x]
  let d₁ := fderiv ℝ
    ((specialFormPreservingSmoothRealChart F hF hdet h).symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet x.1))
    (specialFormPreservingSmoothRealChart F hF hdet h x.1)
  let d₂ := fderiv ℝ
    ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet h))
    (specialFormPreservingSmoothRealChart F hF hdet g x.1)
  have hdet : (d₁.comp d₂).det = d₁.det * d₂.det := by
    change LinearMap.det (d₁.toLinearMap.comp d₂.toLinearMap) =
      LinearMap.det d₁.toLinearMap * LinearMap.det d₂.toLinearMap
    exact LinearMap.det_comp d₁.toLinearMap d₂.toLinearMap
  simp only [d₁, d₂, hdet, abs_mul]

/-- The same center-change law expressed entirely on the exact target
coordinate subtypes of the two fixed charts. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensity_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g
        ⟨specialFormPreservingSmoothRealChart F hF hdet g x.1,
          (specialFormPreservingSmoothRealChart F hF hdet g).map_source x.2.1⟩ =
      specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet h
          ⟨specialFormPreservingSmoothRealChart F hF hdet h x.1,
            (specialFormPreservingSmoothRealChart F hF hdet h).map_source x.2.2⟩ *
        |(fderiv ℝ
          ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
            (specialFormPreservingSmoothRealChart F hF hdet h))
          (specialFormPreservingSmoothRealChart F hF hdet g x.1)).det| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity,
    specialFormPreservingSmoothRealChartCoordinateDensity]
  have hg :
      (⟨(specialFormPreservingSmoothRealChart F hF hdet g).symm
          (specialFormPreservingSmoothRealChart F hF hdet g x.1),
        (specialFormPreservingSmoothRealChart F hF hdet g).symm.map_source
          ((specialFormPreservingSmoothRealChart F hF hdet g).map_source x.2.1)⟩ :
        (specialFormPreservingSmoothRealChart F hF hdet g).source) =
        ⟨x.1, x.2.1⟩ := by
    apply Subtype.ext
    exact (specialFormPreservingSmoothRealChart F hF hdet g).left_inv x.2.1
  have hh :
      (⟨(specialFormPreservingSmoothRealChart F hF hdet h).symm
          (specialFormPreservingSmoothRealChart F hF hdet h x.1),
        (specialFormPreservingSmoothRealChart F hF hdet h).symm.map_source
          ((specialFormPreservingSmoothRealChart F hF hdet h).map_source x.2.2)⟩ :
        (specialFormPreservingSmoothRealChart F hF hdet h).source) =
        ⟨x.1, x.2.2⟩ := by
    apply Subtype.ext
    exact (specialFormPreservingSmoothRealChart F hF hdet h).left_inv x.2.2
  rw [hg, hh]
  exact specialFormPreservingSmoothRealChartDensityAt_center_change
    F hF hdet g h x

/-- On the exact fixed-target overlap images, the inverse-pulled `ENNReal`
densities transform by the absolute ambient Jacobian of the common transition. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensity_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
        F hF hdet g h y =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
            F hF hdet g h y) *
        ENNReal.ofReal |(fderiv ℝ
          (specialFormPreservingSmoothSkewAdjointTransition
            (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
            (realChart_det_map_algebraMap_ne_zero F hdet)
            realChart_ringChar_ne_two g h)
          y.1.1).det| := by
  let e :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph
  let eR :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).toHomeomorph
  let uL :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h
  let uR :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h
  let T := specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
    F hF hdet g h
  let A := specialFormPreservingSmoothRealChart F hF hdet g
  let B := specialFormPreservingSmoothRealChart F hF hdet h
  let x := e.symm y
  have hex : e x = y := e.apply_symm_apply y
  have heLcoord : (e x).1 =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h x :=
    coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft_toHomeomorph_apply
      F hF hdet g h x
  have hcoordL :
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
        F hF hdet g h x).1 = A x.1 := by
    change ((specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet g
      ⟨A x.1, A.map_source x.2.1⟩).1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = A x.1
    exact coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
      F hF hdet g _
  have hyA : A x.1 = y.1.1 := by
    calc
      A x.1 = (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h x).1 := hcoordL.symm
      _ = (e x).1.1 := congrArg Subtype.val heLcoord.symm
      _ = y.1.1 := congrArg (fun z => z.1.1) hex
  have huL : (uL.symm y).1.1 = y.1.1 := by
    calc
      (uL.symm y).1.1 =
          (specialFormPreservingSmoothRealChartTargetHomeomorph
            F hF hdet g (uL.symm y).1).1 :=
        (coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
          F hF hdet g _).symm
      _ = y.1.1 := by
        exact congrArg (fun z => z.1.1) (uL.apply_symm_apply y)
  have hxL : (uL.symm y).1 =
      ⟨A x.1, A.map_source x.2.1⟩ := by
    apply Subtype.ext
    exact huL.trans hyA.symm
  have hTy : T y = eR x := by
    rw [← hex]
    exact specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply
      F hF hdet g h x
  have heRcoord : (eR x).1 =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h x :=
    coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight_toHomeomorph_apply
      F hF hdet g h x
  have hcoordR :
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
        F hF hdet g h x).1 = B x.1 := by
    change ((specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet h
      ⟨B x.1, B.map_source x.2.2⟩).1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = B x.1
    exact coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
      F hF hdet h _
  have hyB : B x.1 = (T y).1.1 := by
    calc
      B x.1 = (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
          F hF hdet g h x).1 := hcoordR.symm
      _ = (eR x).1.1 := congrArg Subtype.val heRcoord.symm
      _ = (T y).1.1 := congrArg (fun z => z.1.1) hTy.symm
  have huR : (uR.symm (T y)).1.1 = (T y).1.1 := by
    calc
      (uR.symm (T y)).1.1 =
          (specialFormPreservingSmoothRealChartTargetHomeomorph
            F hF hdet h (uR.symm (T y)).1).1 :=
        (coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
          F hF hdet h _).symm
      _ = (T y).1.1 := by
        exact congrArg (fun z => z.1.1) (uR.apply_symm_apply (T y))
  have hxR : (uR.symm (T y)).1 =
      ⟨B x.1, B.map_source x.2.2⟩ := by
    apply Subtype.ext
    exact huR.trans hyB.symm
  have hx := specialFormPreservingSmoothRealChartCoordinateDensity_center_change
    F hF hdet g h x
  have hx' := congrArg ENNReal.ofReal hx
  have hnonneg : 0 ≤ specialFormPreservingSmoothRealChartCoordinateDensity
      F hF hdet h ⟨B x.1, B.map_source x.2.2⟩ := by
    rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq]
    exact abs_nonneg _
  rw [ENNReal.ofReal_mul hnonneg] at hx'
  change ENNReal.ofReal
      (specialFormPreservingSmoothRealChartCoordinateDensity
        F hF hdet g (uL.symm y).1) =
    ENNReal.ofReal
        (specialFormPreservingSmoothRealChartCoordinateDensity
          F hF hdet h (uR.symm (T y)).1) *
      ENNReal.ofReal |(fderiv ℝ (A.symm.trans B) y.1.1).det|
  rw [← hxL, ← hxR, hyA] at hx'
  exact hx'

/-- The exact left common-target image is the source of the ambient smooth
transition, with only the nested chart-target subtype forgotten. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
        F hF hdet g h ≃ₜ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).source where
  toFun y := ⟨y.1.1, by
    rcases y.2 with ⟨x, hx⟩
    let A := specialFormPreservingSmoothRealChart F hF hdet g
    let B := specialFormPreservingSmoothRealChart F hF hdet h
    have hcoord :
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
          F hF hdet g h x).1 = A x.1 := rfl
    rw [← hx, hcoord]
    exact openPartialHomeomorph_apply_mem_symm_trans_source
      A B x.1 x.2.1 x.2.2⟩
  invFun y := ⟨⟨y.1, by
    let A := specialFormPreservingSmoothRealChart F hF hdet g
    let B := specialFormPreservingSmoothRealChart F hF hdet h
    have hy := y.2
    change y.1 ∈ (A.symm.trans B).source at hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    have htargetA : A.target =
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
      (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g).trans
        (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two 1).symm
    rw [← htargetA]
    exact hy.1⟩, by
    let A := specialFormPreservingSmoothRealChart F hF hdet g
    let B := specialFormPreservingSmoothRealChart F hF hdet h
    have hy := y.2
    change y.1 ∈ (A.symm.trans B).source at hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    let x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h :=
      ⟨A.symm y.1, A.map_target hy.1, hy.2⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change A x.1 = y.1
    exact A.right_inv hy.1⟩
  left_inv y := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h y).1 = y.1.1 :=
  rfl

/-- The exact right common-target image is the target of the ambient smooth
transition. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
        F hF hdet g h ≃ₜ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).target :=
  (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
    F hF hdet g h).symm.trans
      ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
        F hF hdet g h).trans
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h).toHomeomorphSourceTarget)

/-- The right image-to-target homeomorphism only forgets the nested target
subtype. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
      F hF hdet g h) :
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
      F hF hdet g h y).1 = y.1.1 := by
  let T := specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
    F hF hdet g h
  let z := T.symm y
  change (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h) z.1.1 = y.1.1
  rw [← coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_eq_transition
    F hF hdet g h z]
  exact congrArg (fun w => w.1.1) (T.apply_symm_apply y)

/-- The source and target bridges intertwine the exact image transition with
the ambient transition restricted to its source and target. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageHomeomorph_commute
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
        F hF hdet g h
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
          F hF hdet g h y) =
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
          F hF hdet g h y) := by
  apply Subtype.ext
  calc
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
        F hF hdet g h
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
          F hF hdet g h y)).1 =
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
          F hF hdet g h y).1.1 :=
      coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget_apply
        F hF hdet g h _
    _ = specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h y.1.1 :=
      coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_eq_transition
        F hF hdet g h y
    _ = specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
            F hF hdet g h y).1 := by
      rw [coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource_apply]
    _ = ((specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h).toHomeomorphSourceTarget
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
            F hF hdet g h y)).1 := rfl

/-- The ambient absolute derivative determinant on the exact left overlap
coordinate image. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) : ENNReal :=
  ENNReal.ofReal |(fderiv ℝ
    (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h) y.1.1).det|

/-- The same ambient Jacobian represented directly on the exact transition
source subtype. -/
def specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).source) : ENNReal :=
  ENNReal.ofReal |(fderiv ℝ
    (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h) y.1).det|

/-- The exact-image transition Jacobian is measurable. -/
theorem measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measurable
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
        F hF hdet g h) := by
  let eL :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h
  have hsource : Measurable
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
        F hF hdet g h) :=
    (ENNReal.continuous_ofReal.comp
      (continuousOn_iff_continuous_restrict.mp
        (continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition
          F hF hdet g h))).measurable
  exact hsource.comp eL.continuous.measurable

/-- Pulling the left-image Jacobian through the source bridge recovers the
ambient Jacobian on the exact transition source. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian_comp_source_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
        F hF hdet g h ∘
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
          F hF hdet g h).symm =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
        F hF hdet g h := by
  let eL :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h
  funext y
  have hcoe :=
    coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource_apply
      F hF hdet g h (eL.symm y)
  have happ := congrArg Subtype.val (eL.apply_symm_apply y)
  have hy : (eL.symm y).1.1 = y.1 := hcoe.symm.trans happ
  change ENNReal.ofReal |(fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h) (eL.symm y).1.1).det| = _
  rw [hy]
  rfl

/-- After forgetting the nested identity-chart target, the left coordinate
image base measure is the ambient coordinate measure pulled back to the exact
transition source. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
          F hF hdet g h) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft,
    specialFormPreservingSmoothRealIdentityChartTargetMeasure]
  let e :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h).toMeasurableEquiv
  calc
    Measure.map e
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0))) =
        Measure.comap Subtype.val
          (Measure.comap id
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :=
      map_comap_comap_measurableEquiv e
        Subtype.val Subtype.val Subtype.val id
        (MeasurableEmbedding.subtype_coe
          (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
            F hF hdet g h))
        (MeasurableEmbedding.subtype_coe
          (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet)
        (MeasurableEmbedding.subtype_coe
          (specialFormPreservingSmoothSkewAdjointTransition
            (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
            (realChart_det_map_algebraMap_ne_zero F hdet)
            realChart_ringChar_ne_two g h).open_source.measurableSet)
        MeasurableEmbedding.id
        (fun y =>
          coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource_apply
            F hF hdet g h y)
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)
    _ = Measure.comap Subtype.val
          (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
      rw [show (id :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = fun x => x by rfl,
        Measure.comap_id]

/-- After forgetting the nested identity-chart target, the right coordinate
image base measure is the ambient coordinate measure pulled back to the exact
transition target. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
          F hF hdet g h) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  rw [specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight,
    specialFormPreservingSmoothRealIdentityChartTargetMeasure]
  let e :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
      F hF hdet g h).toMeasurableEquiv
  calc
    Measure.map e
        (Measure.comap Subtype.val
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0))) =
        Measure.comap Subtype.val
          (Measure.comap id
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) :=
      map_comap_comap_measurableEquiv e
        Subtype.val Subtype.val Subtype.val id
        (MeasurableEmbedding.subtype_coe
          (measurableSet_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRight
            F hF hdet g h))
        (MeasurableEmbedding.subtype_coe
          (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet)
        (MeasurableEmbedding.subtype_coe
          (specialFormPreservingSmoothSkewAdjointTransition
            (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
            (realChart_det_map_algebraMap_ne_zero F hdet)
            realChart_ringChar_ne_two g h).open_target.measurableSet)
        MeasurableEmbedding.id
        (fun y =>
          coe_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget_apply
            F hF hdet g h y)
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)
    _ = Measure.comap Subtype.val
          (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
      rw [show (id :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = fun x => x by rfl,
        Measure.comap_id]

set_option maxHeartbeats 10000 in
/-- The source bridge carries the left coordinate measure weighted by the
transition Jacobian to the corresponding weighted ambient source-subtype
measure. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_withDensity_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
          F hF hdet g h)
        ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
          F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
            F hF hdet g h)) =
      (Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
          F hF hdet g h) := by
  let eL :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h
  let mL := eL.toMeasurableEquiv
  have hbase : Measure.map mL
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) :=
    map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_source
      F hF hdet g h
  have hfun :
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
          F hF hdet g h ∘ mL.symm =
        specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
          F hF hdet g h :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian_comp_source_symm
      F hF hdet g h
  have hmap := map_withDensity_measurableEquiv mL
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
      F hF hdet g h)
    (measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
      F hF hdet g h)
  rw [← hfun]
  change Measure.map mL
      ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
          F hF hdet g h)) = _
  exact hmap.trans (congrArg (fun ν => ν.withDensity
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
      F hF hdet g h ∘ mL.symm)) hbase)

/-- The ambient derivative of the swapped-center transition is the inverse of
the original transition derivative at corresponding points. -/
theorem fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_comp
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).source) :
    (fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two h g)
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y)).comp
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y) =
      ContinuousLinearMap.id ℝ
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule := by
  let t := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g h
  let u := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two h g
  have hty : t y ∈ u.source := by
    change t y ∈ t.target
    exact t.map_source hy
  have hcomp : HasFDerivAt (u ∘ t)
      ((fderiv ℝ u (t y)).comp (fderiv ℝ t y)) y :=
    (hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet h g (t y) hty).comp y
        (hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
          F hF hdet g h y hy)
  have heq : (u ∘ t) =ᶠ[nhds y] id := by
    filter_upwards [t.open_source.mem_nhds hy] with z hz
    change u (t z) = z
    exact t.left_inv hz
  have hid : HasFDerivAt (u ∘ t)
      (ContinuousLinearMap.id ℝ
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) y :=
    (hasFDerivAt_id y).congr_of_eventuallyEq heq
  simpa [t, u] using hcomp.unique hid

/-- The Jacobian determinants of a real transition and its swapped-center
inverse multiply to one. This does not assert that either determinant itself
is one in the fixed ambient chart coordinates. -/
theorem det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_mul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).source) :
    (fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two h g)
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y)).det *
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y).det = 1 := by
  rw [← LinearMap.det_comp]
  change
    ((fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two h g)
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y)).comp
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y)).det = 1
  rw [fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_comp
    F hF hdet g h y hy]
  exact LinearMap.det_id

/-- The absolute Jacobian densities of a real transition and its
swapped-center inverse multiply to one. -/
theorem abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_mul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
      (realChart_det_map_algebraMap_ne_zero F hdet)
      realChart_ringChar_ne_two g h).source) :
    |(fderiv ℝ
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two h g)
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h y)).det| *
      |(fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h) y).det| = 1 := by
  rw [← abs_mul,
    det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_mul
      F hF hdet g h y hy, abs_one]

/-- Every pointwise chart density is strictly positive because its transition
derivative has the swapped-center derivative as an inverse. -/
theorem specialFormPreservingSmoothRealChartDensityAt_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    0 < specialFormPreservingSmoothRealChartDensityAt F hF hdet g x := by
  rw [specialFormPreservingSmoothRealChartDensityAt]
  apply abs_pos.mpr
  have hsource :=
    specialFormPreservingSmoothRealChart_coordinate_mem_transition_to_self_source
      F hF hdet g x
  have hmul :=
    det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_swap_mul
      F hF hdet g x.1
        (specialFormPreservingSmoothRealChart F hF hdet g x.1) hsource
  have hforward :
      (fderiv ℝ
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g x.1)
        (specialFormPreservingSmoothRealChart F hF hdet g x.1)).det =
      (fderiv ℝ
        ((specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
          (specialFormPreservingSmoothRealChart F hF hdet x.1))
        (specialFormPreservingSmoothRealChart F hF hdet g x.1)).det := rfl
  intro hzero
  rw [hforward, hzero, mul_zero] at hmul
  exact zero_ne_one hmul

/-- The transported density on an exact target-coordinate subtype is strictly
positive. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensity_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    0 < specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet g y := by
  exact specialFormPreservingSmoothRealChartDensityAt_pos F hF hdet g _

/-- The extended-real coordinate density is strictly positive at every point
of the exact chart target. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensityENNReal_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    0 < specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g y := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensityENNReal,
    ENNReal.ofReal_pos]
  exact specialFormPreservingSmoothRealChartCoordinateDensity_pos
    F hF hdet g y

/-- The fixed coordinate measure on an exact chart target is absolutely
continuous with respect to the chart-local density measure. Together with
`specialFormPreservingSmoothRealChartTargetDensityMeasure_absolutelyContinuous`,
this gives same-chart mutual absolute continuity. -/
theorem specialFormPreservingSmoothRealChartCoordinateMeasure_absolutelyContinuous
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) ≪
      specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  exact withDensity_absolutelyContinuous'
    (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g).aemeasurable
    (ae_of_all _ fun y ↦ ne_of_gt
      (specialFormPreservingSmoothRealChartCoordinateDensityENNReal_pos
        F hF hdet g y))

/-- Weighting a chart-local density measure by the reciprocal of its strictly
positive density recovers the fixed coordinate measure on that exact target. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_withDensity_inv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g).withDensity
        (fun y ↦
          (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            F hF hdet g y)⁻¹) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  exact withDensity_inv_same
    (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g)
    (ae_of_all _ fun y ↦ ne_of_gt
      (specialFormPreservingSmoothRealChartCoordinateDensityENNReal_pos
        F hF hdet g y))
    (ae_of_all _ fun y ↦ by
      simp [specialFormPreservingSmoothRealChartCoordinateDensityENNReal])

/-- Each chart-local density measure is positive on every nonempty open set,
stated without installing a measure instance. -/
theorem specialFormPreservingSmoothRealChartTargetDensityMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.IsOpenPosMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) := by
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  letI : Measure.IsOpenPosMeasure
      (Measure.comap
        ((↑) : (specialFormPreservingSmoothRealChart F hF hdet g).target →
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule) μ) :=
    Measure.IsOpenPosMeasure.comap μ
      (specialFormPreservingSmoothRealChart F hF hdet g).open_target.isOpenEmbedding_subtypeVal
  exact
    (specialFormPreservingSmoothRealChartCoordinateMeasure_absolutelyContinuous
      F hF hdet g).isOpenPosMeasure

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's nonlinear change-of-variables theorem applies to the exact real
coordinate transition. The remaining density is the absolute determinant of
its ambient Frechet derivative; no Jacobian-one claim is made here. -/
theorem map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothSkewAdjointTransition
            (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
            (realChart_det_map_algebraMap_ne_zero F hdet)
            realChart_ringChar_ne_two g h).source).withDensity
          fun y => ENNReal.ofReal
            |(fderiv ℝ
              (specialFormPreservingSmoothSkewAdjointTransition
                (F.map (algebraMap ℚ ℝ))
                (realChart_isSymm_map_algebraMap F hF)
                (realChart_det_map_algebraMap_ne_zero F hdet)
                realChart_ringChar_ne_two g h) y).det|) =
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h).target := by
  let t := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g h
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  have hderiv : ∀ y ∈ t.source,
      HasFDerivWithinAt t (fderiv ℝ t y) t.source y := by
    intro y hy
    exact
      (hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h y hy).hasFDerivWithinAt
  have hmap := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    μ t.open_source.nullMeasurableSet hderiv t.injOn
  have himage : t '' t.source = t.target :=
    PartialEquiv.image_source_eq_target t.toPartialEquiv
  simpa [t, μ, himage] using hmap

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 50000 in
/-- On the exact source and target subtypes, the ambient transition transports
the coordinate measure weighted by its absolute derivative determinant to the
unweighted target coordinate measure. -/
theorem map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_sourceTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothSkewAdjointTransition
          (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
          (realChart_det_map_algebraMap_ne_zero F hdet)
          realChart_ringChar_ne_two g h).toHomeomorphSourceTarget
        ((Measure.comap Subtype.val
          (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).withDensity
            (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
              F hF hdet g h)) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  let t := specialFormPreservingSmoothSkewAdjointTransition
    (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
    (realChart_det_map_algebraMap_ne_zero F hdet)
    realChart_ringChar_ne_two g h
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let J : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule → ENNReal :=
    fun y => ENNReal.ofReal |(fderiv ℝ t y).det|
  change Measure.map t.toHomeomorphSourceTarget
      ((Measure.comap Subtype.val μ).withDensity (J ∘ Subtype.val)) =
    Measure.comap Subtype.val μ
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  have hderiv : ∀ y ∈ t.source,
      HasFDerivWithinAt t (fderiv ℝ t y) t.source y := by
    intro y hy
    exact
      (hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h y hy).hasFDerivWithinAt
  have hmap :=
    MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar
      μ t.open_source.measurableSet hderiv t.injOn
  have himage : t '' t.source = t.target :=
    PartialEquiv.image_source_eq_target t.toPartialEquiv
  apply (MeasurableEmbedding.subtype_coe
    t.open_target.measurableSet).map_injective
  calc
    Measure.map Subtype.val
        (Measure.map t.toHomeomorphSourceTarget
          ((Measure.comap Subtype.val μ).withDensity (J ∘ Subtype.val))) =
        Measure.map Subtype.val
          (Measure.map t.toHomeomorphSourceTarget
            (Measure.comap Subtype.val (μ.withDensity J))) := by
      rw [comap_subtype_withDensity t.open_source.measurableSet]
    _ = Measure.map (t.source.restrict t)
          (Measure.comap Subtype.val (μ.withDensity J)) := by
      rw [Measure.map_map measurable_subtype_coe
        t.toHomeomorphSourceTarget.continuous.measurable]
      rfl
    _ = μ.restrict t.target := by
      simpa only [J, himage,
        specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian]
        using hmap
    _ = Measure.map Subtype.val (Measure.comap Subtype.val μ) := by
      symm
      exact map_comap_subtype_coe t.open_target.measurableSet μ

set_option maxHeartbeats 50000 in
/-- On the ambient transition source and target subtypes, the exact coordinate
transition is measure preserving from the Jacobian-weighted source measure to
the unweighted target measure. This avoids restating the expensive combined
transport on the nested common-image subtypes. -/
theorem measurePreserving_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_sourceTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    MeasurePreserving
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).toHomeomorphSourceTarget
      ((Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
          F hF hdet g h))
      (Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) := by
  refine ⟨?_, ?_⟩
  · exact
      (specialFormPreservingSmoothSkewAdjointTransition
        (F.map (algebraMap ℚ ℝ)) (realChart_isSymm_map_algebraMap F hF)
        (realChart_det_map_algebraMap_ne_zero F hdet)
        realChart_ringChar_ne_two g h).toHomeomorphSourceTarget.continuous.measurable
  · exact
      map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_sourceTarget
        F hF hdet g h

end PositiveDefiniteIntegralLattice
