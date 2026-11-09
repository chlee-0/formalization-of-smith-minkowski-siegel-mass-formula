import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductTransition
import SMSFormula.SpecialOrthogonalRealIdentityTangentMeasure

/-!
# Change of variables for the identity north-pole product transition

This file identifies the exact open image of the local product transition,
proves injectivity on its higher-chart source, conjugates the transition to a
self-map of the product tangent carrier, and applies Mathlib's real nonlinear
change-of-variables theorem.

The source and target additive Haar measures use the fixed rationally
normalized tangent bases. Their separate linear transport retains the exact
constant comparison determinant.
-/

open scoped Matrix Matrix.Norms.Operator ContDiff NNReal ENNReal

noncomputable section

open Matrix Metric Set MeasureTheory

namespace PositiveDefiniteIntegralLattice

def identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph
    (n : ℕ) :
    identitySpecialOrthogonalRankGroup n ≃ₜ
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) where
  toFun := identitySpecialOrthogonalLiteralIdentityGroupToMapped n
  invFun := identitySpecialOrthogonalMappedIdentityGroupToLiteral n
  left_inv :=
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse n
  right_inv :=
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse n
  continuous_toFun :=
    continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped n
  continuous_invFun :=
    continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral n

def identitySpecialOrthogonalNorthPoleProductCommonLiteralGroupSet
    (n : ℕ) :
    Set (identitySpecialOrthogonalRankGroup (n + 1)) :=
  Subtype.val ''
    identitySpecialOrthogonalNorthPoleCommonDomainSet n

theorem
    identitySpecialOrthogonalNorthPoleProductCommonLiteralGroupSet_isOpen
    (n : ℕ) :
    IsOpen
      (identitySpecialOrthogonalNorthPoleProductCommonLiteralGroupSet n) := by
  exact
    (isOpen_identitySpecialOrthogonalNorthPoleGroupSet n
      ).isOpenMap_subtype_val _
        (isOpen_identitySpecialOrthogonalNorthPoleCommonDomainSet n)

def identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet
    (n : ℕ) :
    Set (specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ))) :=
  identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1) ''
    identitySpecialOrthogonalNorthPoleProductCommonLiteralGroupSet n

theorem
    identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet_isOpen
    (n : ℕ) :
    IsOpen
      (identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet n) :=
  (identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1)
    ).isOpen_image.mpr
    (identitySpecialOrthogonalNorthPoleProductCommonLiteralGroupSet_isOpen n)

def identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n : ℕ) :
    Set (specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ))) :=
  identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet n ∩
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).source

theorem identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen
    (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) :=
  (identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet_isOpen n).inter
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).open_source

def identitySpecialOrthogonalNorthPoleProductTransitionTargetSet
    (n : ℕ) :
    Set (identitySpecialOrthogonalMappedTangent (n + 1)) :=
  specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero ''
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n

theorem identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_isOpen
    (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) := by
  apply
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).isOpen_image_of_subset_source
  · exact identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
  · exact inter_subset_right

theorem
    identitySpecialOrthogonalNorthPoleProductMappedGroup_mem_commonMappedGroupSet
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleProductMappedGroup n p ∈
      identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet n := by
  refine
    ⟨identitySpecialOrthogonalNorthPoleProduct n p, ?_, rfl⟩
  refine
    ⟨identitySpecialOrthogonalNorthPoleProductToGroupDomain n p, ?_, rfl⟩
  exact
    (identitySpecialOrthogonalNorthPoleProductToCommon n p).2

theorem
    exists_identitySpecialOrthogonalNorthPoleProductMappedGroup_eq_of_mem_commonMappedGroupSet
    (n : ℕ)
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ)))
    (hg : g ∈ identitySpecialOrthogonalNorthPoleProductCommonMappedGroupSet n) :
    ∃ p : identitySpecialOrthogonalNorthPoleProductDomain n,
      identitySpecialOrthogonalNorthPoleProductMappedGroup n p = g := by
  rcases hg with ⟨l, ⟨c, hc, rfl⟩, rfl⟩
  let q : identitySpecialOrthogonalNorthPoleCommonDomain n := ⟨c, hc⟩
  let p := identitySpecialOrthogonalNorthPoleCommonToProduct n q
  refine ⟨p, ?_⟩
  have h :=
    identitySpecialOrthogonalNorthPoleProductToCommon_commonToProduct n q
  change
    identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1)
        (identitySpecialOrthogonalNorthPoleProduct n p) =
      identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1) c.1
  exact congrArg
    (identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1))
    (congrArg (fun x => x.1.1) h)

theorem identitySpecialOrthogonalNorthPoleProductMappedGroup_injective (n : ℕ) :
    Function.Injective
      (identitySpecialOrthogonalNorthPoleProductMappedGroup n) := by
  intro p q h
  have hgroup :
      identitySpecialOrthogonalNorthPoleProduct n p =
        identitySpecialOrthogonalNorthPoleProduct n q :=
    (identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph (n + 1)
      ).injective h
  apply (identitySpecialOrthogonalNorthPoleProductHomeomorph n).injective
  apply Subtype.ext
  apply Subtype.ext
  exact hgroup

theorem injOn_identitySpecialOrthogonalNorthPoleProductTransition (n : ℕ) :
    Set.InjOn
      (identitySpecialOrthogonalNorthPoleProductTransition n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  intro x hx y hy hxy
  rcases hx with ⟨px, hpx, rfl⟩
  rcases hy with ⟨py, hpy, rfl⟩
  have hgroup :
      identitySpecialOrthogonalNorthPoleProductMappedGroup n px =
        identitySpecialOrthogonalNorthPoleProductMappedGroup n py := by
    apply
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).injOn hpx hpy
    simpa only [
      identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
        n px hpx,
      identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
        n py hpy] using hxy
  exact congrArg Subtype.val (identitySpecialOrthogonalNorthPoleProductMappedGroup_injective n hgroup)

theorem image_identitySpecialOrthogonalNorthPoleProductTransition_source (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransition n ''
        identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n =
      identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n := by
  ext y
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine
      ⟨identitySpecialOrthogonalNorthPoleProductMappedGroup n p, ?_, ?_⟩
    · exact
        ⟨identitySpecialOrthogonalNorthPoleProductMappedGroup_mem_commonMappedGroupSet
          n p, hp⟩
    · exact
        identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
          n p hp |>.symm
  · rintro ⟨g, ⟨hgcommon, hgsource⟩, rfl⟩
    rcases
      exists_identitySpecialOrthogonalNorthPoleProductMappedGroup_eq_of_mem_commonMappedGroupSet
        n g hgcommon with
      ⟨p, hp⟩
    have hpsource :
        p ∈
          identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
            n := by
      simpa [identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet,
        hp] using hgsource
    refine ⟨p.1, ⟨p, hpsource, rfl⟩, ?_⟩
    rw [
      identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
        n p hpsource,
      hp]

def identitySpecialOrthogonalNorthPoleProductTransitionSquareMap (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n) :=
  (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n).symm
    (identitySpecialOrthogonalNorthPoleProductTransition n p)

noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :=
  (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
    ).symm.toContinuousLinearMap.comp
      (fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransition n) p)

theorem
    hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp :
      p ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    HasFDerivWithinAt
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n)
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative n p)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) p := by
  exact
    (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
      ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt p
      ((((contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition_higherChartSource
        n).contDiffAt
          ((identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen
            n).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
              ).hasFDerivWithinAt

theorem
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_injOn
    (n : ℕ) :
    Set.InjOn (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  intro x hx y hy hxy
  exact injOn_identitySpecialOrthogonalNorthPoleProductTransition n hx hy
    ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
      ).symm.injective hxy)

theorem
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_image
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n ''
        identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n =
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
        ).symm '' identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n := by
  change
    ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
      ).symm ∘
      identitySpecialOrthogonalNorthPoleProductTransition n) ''
        identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n = _
  calc
    _ =
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
          ).symm ''
          (identitySpecialOrthogonalNorthPoleProductTransition n ''
            identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
      simpa using
        (Set.image_image
          (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
            ).symm
          (identitySpecialOrthogonalNorthPoleProductTransition n)
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
            )).symm
    _ = _ := by
      rw [image_identitySpecialOrthogonalNorthPoleProductTransition_source]

local instance identityNorthPoleTransitionMappedTangentMeasurableSpace (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleTransitionMappedTangentBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleTransitionProductBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :=
  @Prod.borelSpace _ _ _
    (identityNorthPoleTransitionMappedTangentMeasurableSpace n)
    (identityNorthPoleTransitionMappedTangentBorelSpace n) _ _ _ _

def identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
    (n : ℕ) :
    Measure (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :=
  @Module.Basis.addHaar _ _ _ _ _ _
    (identityNorthPoleTransitionProductBorelSpace n)
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n)

def identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
    (n : ℕ) :
    Measure (identitySpecialOrthogonalMappedTangent (n + 1)) :=
  @Module.Basis.addHaar _ _ _ _ _
    (identityNorthPoleTransitionMappedTangentMeasurableSpace (n + 1))
    (identityNorthPoleTransitionMappedTangentBorelSpace (n + 1))
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n)

theorem
    map_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_sourceCoordinateMeasure
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n)
        (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
          n := by
  simpa only [
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure,
    identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure,
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar] using
      @Module.Basis.map_addHaar_eq_inv_abs_det_map_smul _
        (identitySpecialOrthogonalMappedTangent n × EuclideanSpace ℝ (Fin n))
        (identitySpecialOrthogonalMappedTangent (n + 1)) _ _ _ _ _ _ _
        (identityNorthPoleTransitionProductBorelSpace n)
        (identityNorthPoleTransitionMappedTangentMeasurableSpace (n + 1))
        (identityNorthPoleTransitionMappedTangentBorelSpace (n + 1)) _ _
        (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n)
        (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n)
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n)

theorem
    map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
            )).withDensity
          fun p => ENNReal.ofReal
            |LinearMap.det
              (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
                n p).toLinearMap|) =
      (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
        n).restrict
        ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
          ).symm '' identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) := by
  let μ :=
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n
  let U :=
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
  let f := identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n
  let f' := identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative n
  letI : μ.IsAddHaarMeasure := by
    exact @isAddHaarMeasure_basis_addHaar _ _ _ _ _ _
      (identityNorthPoleTransitionProductBorelSpace n)
      (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n)
  have hmap := @MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (identitySpecialOrthogonalMappedTangent n × EuclideanSpace ℝ (Fin n))
    _ _ _ U f f' _ (identityNorthPoleTransitionProductBorelSpace n) μ
    ‹μ.IsAddHaarMeasure›
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
      ).measurableSet.nullMeasurableSet
    (fun p hp =>
      hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
        n hp)
    (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_injOn n)
  rw [identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_image] at hmap
  simpa [μ, U, f, f'] using hmap

end PositiveDefiniteIntegralLattice
