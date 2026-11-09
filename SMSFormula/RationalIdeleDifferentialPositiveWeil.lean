import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveIdeleQuotient
import SMSFormula.RationalIdeleDifferentialHaar

/-!
# Differential Weil normalization on the positive ideles

The full rational-idele differential fundamental domain is folded into the
open subgroup of ideles positive at the real place.  The negative half is
translated by the rational diagonal idele `-1`.  Translation invariance and
the fact that this diagonal is invisible in the idele-class quotient show
that this folding has coefficient one, rather than two.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance rationalIdelePositiveWeilPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The rational diagonal idele used to fold the negative real branch into
the positive branch. -/
def rationalIdeleNegativeOne : RationalAdeleˣ :=
  rationalUnitFullAdelicDiagonalHom (-1 : ℚˣ)

theorem rationalIdeleNegativeOne_ne_one : rationalIdeleNegativeOne ≠ 1 := by
  intro h
  have hreal := congrArg
    (fun a : RationalAdeleˣ ↦
      (((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ))) h
  unfold rationalIdeleNegativeOne at hreal
  dsimp only at hreal
  rw [rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal] at hreal
  norm_num at hreal

/-- Ideles positive at the real place form an open subgroup. -/
theorem isOpen_positiveRationalAdeleUnitsSubgroup :
    IsOpen (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ) := by
  rw [show (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ) =
      (fun a : RationalAdeleˣ ↦
        (((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ))) ⁻¹' Ioi 0 by
    ext a
    exact mem_positiveRationalAdeleUnitsSubgroup_iff a]
  exact isOpen_Ioi.preimage
    (Units.continuous_val.comp
      (continuous_fst.comp
        rationalAdeleUnitsRealFiniteContinuousEquiv.continuous))

theorem measurableSet_positiveRationalAdeleUnitsSubgroup :
    MeasurableSet (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ) :=
  isOpen_positiveRationalAdeleUnitsSubgroup.measurableSet

/-- Multiplication by the rational diagonal `-1` exchanges the negative and
positive real branches. -/
theorem rationalIdeleNegativeOne_mul_mem_positive_iff
    (a : RationalAdeleˣ) :
    rationalIdeleNegativeOne * a ∈ positiveRationalAdeleUnitsSubgroup ↔
      a ∉ positiveRationalAdeleUnitsSubgroup := by
  rw [mem_positiveRationalAdeleUnitsSubgroup_iff,
    mem_positiveRationalAdeleUnitsSubgroup_iff]
  rw [map_mul]
  simp only [Prod.fst_mul, Units.val_mul]
  have hnegOne :
      (((rationalAdeleUnitsRealFiniteContinuousEquiv
          rationalIdeleNegativeOne).1 : ℝ)) = -1 := by
    unfold rationalIdeleNegativeOne
    rw [rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal]
    norm_num
  rw [hnegOne]
  rw [neg_one_mul, neg_pos]
  constructor
  · exact fun h => not_lt_of_ge h.le
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h)
      (rationalAdeleUnitsRealFiniteContinuousEquiv a).1.ne_zero

/-- The sign-folding map into the positive ideles. -/
def rationalIdelePositiveNormalize (a : RationalAdeleˣ) : RationalAdeleˣ :=
  if a ∈ positiveRationalAdeleUnitsSubgroup then a
  else rationalIdeleNegativeOne * a

theorem measurable_rationalIdelePositiveNormalize :
    Measurable rationalIdelePositiveNormalize := by
  unfold rationalIdelePositiveNormalize
  exact measurable_id.piecewise
    measurableSet_positiveRationalAdeleUnitsSubgroup
    (measurable_const.mul measurable_id)

theorem rationalIdelePositiveNormalize_mem (a : RationalAdeleˣ) :
    rationalIdelePositiveNormalize a ∈ positiveRationalAdeleUnitsSubgroup := by
  by_cases ha : a ∈ positiveRationalAdeleUnitsSubgroup
  · simp [rationalIdelePositiveNormalize, ha]
  · simp only [rationalIdelePositiveNormalize, if_neg ha]
    exact (rationalIdeleNegativeOne_mul_mem_positive_iff a).2 ha

theorem rationalIdeleClassQuotientMap_positiveNormalize
    (a : RationalAdeleˣ) :
    rationalIdeleClassQuotientMap (rationalIdelePositiveNormalize a) =
      rationalIdeleClassQuotientMap a := by
  by_cases ha : a ∈ positiveRationalAdeleUnitsSubgroup
  · simp [rationalIdelePositiveNormalize, ha]
  · rw [rationalIdelePositiveNormalize, if_neg ha]
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (rationalIdeleNegativeOne * a) =
      QuotientGroup.mk' rationalIdeleDiagonalSubgroup a
    rw [map_mul]
    rw [show QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        rationalIdeleNegativeOne = 1 by
      exact (QuotientGroup.eq_one_iff _).2 ⟨-1, rfl⟩]
    exact one_mul (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a)

/-- The existing exact full-idele fundamental domain folded into the positive
real branch. -/
def positiveRationalIdeleMeasurableFundamentalDomain : Set RationalAdeleˣ :=
  (rationalIdeleMeasurableFundamentalDomain ∩
      (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ)) ∪
    (fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) ''
      (rationalIdeleMeasurableFundamentalDomain \
        (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ))

theorem measurableSet_positiveRationalIdeleMeasurableFundamentalDomain :
    MeasurableSet positiveRationalIdeleMeasurableFundamentalDomain := by
  apply MeasurableSet.union
  · exact measurableSet_rationalIdeleMeasurableFundamentalDomain.inter
      measurableSet_positiveRationalAdeleUnitsSubgroup
  · exact (measurableEmbedding_mulLeft rationalIdeleNegativeOne).measurableSet_image.2
      (measurableSet_rationalIdeleMeasurableFundamentalDomain.diff
        measurableSet_positiveRationalAdeleUnitsSubgroup)

theorem positiveRationalIdeleMeasurableFundamentalDomain_subset_positive :
    positiveRationalIdeleMeasurableFundamentalDomain ⊆
      positiveRationalAdeleUnitsSubgroup := by
  rintro a (ha | ha)
  · exact ha.2
  · rcases ha with ⟨b, hb, rfl⟩
    exact (rationalIdeleNegativeOne_mul_mem_positive_iff b).2 hb.2

theorem disjoint_positiveRationalIdeleFundamentalDomain_branches :
    Disjoint
      (rationalIdeleMeasurableFundamentalDomain ∩
        (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ))
      ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) ''
        (rationalIdeleMeasurableFundamentalDomain \
          (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ))) := by
  rw [Set.disjoint_left]
  intro x hx htranslated
  rcases htranslated with ⟨b, hb, rfl⟩
  let delta : rationalIdeleDiagonalSubgroup :=
    ⟨rationalIdeleNegativeOne, ⟨-1, rfl⟩⟩
  have hdelta :
      (delta : RationalAdeleˣ) * b ∈ rationalIdeleMeasurableFundamentalDomain :=
    hx.1
  have hone :
      ((1 : rationalIdeleDiagonalSubgroup) : RationalAdeleˣ) * b ∈
        rationalIdeleMeasurableFundamentalDomain := by
    simpa using hb.1
  rcases existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain b with
    ⟨gamma, hgamma, hunique⟩
  have heq : delta = 1 :=
    (hunique delta hdelta).trans (hunique 1 hone).symm
  apply rationalIdeleNegativeOne_ne_one
  exact congrArg Subtype.val heq

/-- Differential Haar transports the negative part of the old domain onto
the folded positive branch with coefficient one. -/
theorem map_rationalIdeleNegativeOne_restrict_negativeFundamentalDomain :
    Measure.map (Homeomorph.mulLeft rationalIdeleNegativeOne)
        (rationalIdeleDifferentialHaarMeasure.restrict
          (rationalIdeleMeasurableFundamentalDomain \
            (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ))) =
      rationalIdeleDifferentialHaarMeasure.restrict
        ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) ''
          (rationalIdeleMeasurableFundamentalDomain \
            (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ))) := by
  let N := rationalIdeleMeasurableFundamentalDomain \
    (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ)
  have hN : MeasurableSet N :=
    measurableSet_rationalIdeleMeasurableFundamentalDomain.diff
      measurableSet_positiveRationalAdeleUnitsSubgroup
  have hTN : MeasurableSet
      ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) '' N) :=
    (measurableEmbedding_mulLeft rationalIdeleNegativeOne).measurableSet_image.2 hN
  have hpre :
      (Homeomorph.mulLeft rationalIdeleNegativeOne) ⁻¹'
          ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) '' N) = N := by
    exact Set.preimage_image_eq _
      (measurableEmbedding_mulLeft rationalIdeleNegativeOne).injective
  calc
    Measure.map (Homeomorph.mulLeft rationalIdeleNegativeOne)
        (rationalIdeleDifferentialHaarMeasure.restrict N) =
        (Measure.map (Homeomorph.mulLeft rationalIdeleNegativeOne)
          rationalIdeleDifferentialHaarMeasure).restrict
            ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) '' N) := by
      symm
      rw [Measure.restrict_map
        (Homeomorph.mulLeft rationalIdeleNegativeOne).measurable hTN]
      rw [hpre]
    _ = rationalIdeleDifferentialHaarMeasure.restrict
          ((fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) '' N) := by
      have hmap :
          Measure.map (Homeomorph.mulLeft rationalIdeleNegativeOne)
              rationalIdeleDifferentialHaarMeasure =
            rationalIdeleDifferentialHaarMeasure := by
        simpa only [Homeomorph.coe_mulLeft] using
          (Measure.IsMulLeftInvariant.map_mul_left_eq_self
            (μ := rationalIdeleDifferentialHaarMeasure)
            rationalIdeleNegativeOne)
      rw [hmap]

/-- The folded differential measure is literally differential Haar restricted
to the folded positive fundamental domain. -/
theorem map_rationalIdelePositiveNormalize_restrict_fundamentalDomain :
    Measure.map rationalIdelePositiveNormalize
        (rationalIdeleDifferentialHaarMeasure.restrict
          rationalIdeleMeasurableFundamentalDomain) =
      rationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalIdeleMeasurableFundamentalDomain := by
  let P : Set RationalAdeleˣ := positiveRationalAdeleUnitsSubgroup
  let F : Set RationalAdeleˣ := rationalIdeleMeasurableFundamentalDomain
  let A : Set RationalAdeleˣ := F ∩ P
  let N : Set RationalAdeleˣ := F \ P
  let T : Set RationalAdeleˣ :=
    (fun a : RationalAdeleˣ ↦ rationalIdeleNegativeOne * a) '' N
  have hA : MeasurableSet A :=
    measurableSet_rationalIdeleMeasurableFundamentalDomain.inter
      measurableSet_positiveRationalAdeleUnitsSubgroup
  have hN : MeasurableSet N :=
    measurableSet_rationalIdeleMeasurableFundamentalDomain.diff
      measurableSet_positiveRationalAdeleUnitsSubgroup
  have hT : MeasurableSet T :=
    (measurableEmbedding_mulLeft rationalIdeleNegativeOne).measurableSet_image.2 hN
  have hAN : Disjoint A N := by
    rw [Set.disjoint_left]
    exact fun _ ha hn ↦ hn.2 ha.2
  have hF : F = A ∪ N := by
    ext a
    simp [A, N, F, P]
  have hmapA :
      Measure.map rationalIdelePositiveNormalize
          (rationalIdeleDifferentialHaarMeasure.restrict A) =
        rationalIdeleDifferentialHaarMeasure.restrict A := by
    calc
      Measure.map rationalIdelePositiveNormalize
          (rationalIdeleDifferentialHaarMeasure.restrict A) =
          Measure.map id
            (rationalIdeleDifferentialHaarMeasure.restrict A) := by
        apply Measure.map_congr
        filter_upwards [MeasureTheory.ae_restrict_mem hA] with a ha
        have hapos : a ∈ positiveRationalAdeleUnitsSubgroup := by
          exact ha.2
        simp [rationalIdelePositiveNormalize, hapos]
      _ = rationalIdeleDifferentialHaarMeasure.restrict A :=
        Measure.map_id
  have hmapN :
      Measure.map rationalIdelePositiveNormalize
          (rationalIdeleDifferentialHaarMeasure.restrict N) =
        rationalIdeleDifferentialHaarMeasure.restrict T := by
    calc
      Measure.map rationalIdelePositiveNormalize
          (rationalIdeleDifferentialHaarMeasure.restrict N) =
          Measure.map (Homeomorph.mulLeft rationalIdeleNegativeOne)
            (rationalIdeleDifferentialHaarMeasure.restrict N) := by
        apply Measure.map_congr
        filter_upwards [MeasureTheory.ae_restrict_mem hN] with a ha
        have haneg : a ∉ positiveRationalAdeleUnitsSubgroup := by
          exact ha.2
        simp [rationalIdelePositiveNormalize, haneg]
      _ = rationalIdeleDifferentialHaarMeasure.restrict T := by
        exact map_rationalIdeleNegativeOne_restrict_negativeFundamentalDomain
  rw [show rationalIdeleMeasurableFundamentalDomain = F by rfl, hF,
    Measure.restrict_union hAN hN,
    Measure.map_add _ _ measurable_rationalIdelePositiveNormalize,
    hmapA, hmapN]
  rw [show positiveRationalIdeleMeasurableFundamentalDomain = A ∪ T by rfl]
  exact (Measure.restrict_union
    disjoint_positiveRationalIdeleFundamentalDomain_branches hT).symm

/-- Differential Haar on the positive ideles, obtained by restricting the
fixed full-idele differential Haar to the open subgroup and pulling it back
along the subgroup inclusion. -/
noncomputable def positiveRationalIdeleDifferentialHaarMeasure :
    Measure positiveRationalAdeleUnitsSubgroup :=
  Measure.comap (fun a : positiveRationalAdeleUnitsSubgroup ↦
    (a : RationalAdeleˣ)) rationalIdeleDifferentialHaarMeasure

theorem map_positiveRationalIdeleDifferentialHaarMeasure_subtype :
    Measure.map (fun a : positiveRationalAdeleUnitsSubgroup ↦
        (a : RationalAdeleˣ)) positiveRationalIdeleDifferentialHaarMeasure =
      rationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalAdeleUnitsSubgroup := by
  unfold positiveRationalIdeleDifferentialHaarMeasure
  exact map_comap_subtype_coe
    measurableSet_positiveRationalAdeleUnitsSubgroup _

/-- The folded positive fundamental domain as a set in the positive-idele
subgroup. -/
def positiveRationalIdeleMeasurableFundamentalDomainSubtype :
    Set positiveRationalAdeleUnitsSubgroup :=
  (fun a : positiveRationalAdeleUnitsSubgroup ↦ (a : RationalAdeleˣ)) ⁻¹'
    positiveRationalIdeleMeasurableFundamentalDomain

theorem measurableSet_positiveRationalIdeleMeasurableFundamentalDomainSubtype :
    MeasurableSet positiveRationalIdeleMeasurableFundamentalDomainSubtype :=
  measurableSet_positiveRationalIdeleMeasurableFundamentalDomain.preimage
    measurable_subtype_coe

theorem map_restrict_positiveRationalIdeleDifferentialHaarMeasure_subtype :
    Measure.map (fun a : positiveRationalAdeleUnitsSubgroup ↦
        (a : RationalAdeleˣ))
        (positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) =
      rationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalIdeleMeasurableFundamentalDomain := by
  calc
    Measure.map (fun a : positiveRationalAdeleUnitsSubgroup ↦
        (a : RationalAdeleˣ))
        (positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) =
        (Measure.map (fun a : positiveRationalAdeleUnitsSubgroup ↦
            (a : RationalAdeleˣ))
          positiveRationalIdeleDifferentialHaarMeasure).restrict
            positiveRationalIdeleMeasurableFundamentalDomain := by
      symm
      exact Measure.restrict_map measurable_subtype_coe
        measurableSet_positiveRationalIdeleMeasurableFundamentalDomain
    _ = (rationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalAdeleUnitsSubgroup).restrict
            positiveRationalIdeleMeasurableFundamentalDomain := by
      rw [map_positiveRationalIdeleDifferentialHaarMeasure_subtype]
    _ = rationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomain :=
      Measure.restrict_restrict_of_subset
        positiveRationalIdeleMeasurableFundamentalDomain_subset_positive

/-- The sign-folding map, with its codomain restricted to the actual positive
idele subgroup. -/
def rationalIdelePositiveNormalizeSubtype (a : RationalAdeleˣ) :
    positiveRationalAdeleUnitsSubgroup :=
  ⟨rationalIdelePositiveNormalize a, rationalIdelePositiveNormalize_mem a⟩

theorem measurable_rationalIdelePositiveNormalizeSubtype :
    Measurable rationalIdelePositiveNormalizeSubtype :=
  Measurable.subtype_mk measurable_rationalIdelePositiveNormalize

/-- The differential fundamental-domain measure on positive ideles is the
coefficient-one sign fold of the already certified full-idele domain. -/
noncomputable def positiveRationalIdeleDifferentialFundamentalDomainMeasure :
    Measure positiveRationalAdeleUnitsSubgroup :=
  Measure.map rationalIdelePositiveNormalizeSubtype
    (rationalIdeleDifferentialHaarMeasure.restrict
      rationalIdeleMeasurableFundamentalDomain)

/-- The folded measure is not a surrogate: it is exactly the restriction of
the inherited differential Haar measure to the positive fundamental domain. -/
theorem positiveRationalIdeleDifferentialFundamentalDomainMeasure_eq_restrict :
    positiveRationalIdeleDifferentialFundamentalDomainMeasure =
      positiveRationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalIdeleMeasurableFundamentalDomainSubtype := by
  apply (MeasurableEmbedding.subtype_coe
    measurableSet_positiveRationalAdeleUnitsSubgroup).map_injective
  calc
    Measure.map Subtype.val
        positiveRationalIdeleDifferentialFundamentalDomainMeasure =
        rationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomain := by
      unfold positiveRationalIdeleDifferentialFundamentalDomainMeasure
      rw [Measure.map_map measurable_subtype_coe
        measurable_rationalIdelePositiveNormalizeSubtype]
      exact map_rationalIdelePositiveNormalize_restrict_fundamentalDomain
    _ = Measure.map Subtype.val
        (positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) := by
      symm
      exact map_restrict_positiveRationalIdeleDifferentialHaarMeasure_subtype

/-- The positive-idele class map is measurable in the inherited subgroup
measurable structure. -/
theorem measurable_positiveRationalIdeleToIdeleClassHom :
    Measurable positiveRationalIdeleToIdeleClassHom := by
  change Measurable (fun a : positiveRationalAdeleUnitsSubgroup ↦
    rationalIdeleClassQuotientMap (a : RationalAdeleˣ))
  exact rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable.comp
    measurable_subtype_coe

/-- Differential Weil on the positive branch.  Folding by the rational
diagonal `-1` leaves the quotient point unchanged, so the positive-idele
fundamental-domain measure maps to the ordinary differential Weil quotient
with coefficient exactly one. -/
theorem map_positiveRationalIdeleDifferentialFundamentalDomainMeasure :
    Measure.map positiveRationalIdeleToIdeleClassHom
        positiveRationalIdeleDifferentialFundamentalDomainMeasure =
      rationalIdeleClassDifferentialWeilQuotientMeasure := by
  unfold positiveRationalIdeleDifferentialFundamentalDomainMeasure
  rw [Measure.map_map measurable_positiveRationalIdeleToIdeleClassHom
    measurable_rationalIdelePositiveNormalizeSubtype]
  unfold rationalIdeleClassDifferentialWeilQuotientMeasure
  apply Measure.map_congr
  filter_upwards [] with a
  exact rationalIdeleClassQuotientMap_positiveNormalize a

/-- The actual positive-idele differential Haar restriction maps to the
ordinary differential idele-class Weil quotient with coefficient one. -/
theorem map_positiveRationalIdeleDifferentialHaar_restrict_fundamentalDomain :
    Measure.map positiveRationalIdeleToIdeleClassHom
        (positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) =
      rationalIdeleClassDifferentialWeilQuotientMeasure := by
  rw [← positiveRationalIdeleDifferentialFundamentalDomainMeasure_eq_restrict]
  exact map_positiveRationalIdeleDifferentialFundamentalDomainMeasure

/-- Measure-preserving form of the positive-idele differential Weil
identity. -/
theorem measurePreserving_positiveRationalIdeleToIdeleClassHom_differentialDomain :
    MeasurePreserving positiveRationalIdeleToIdeleClassHom
      (positiveRationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalIdeleMeasurableFundamentalDomainSubtype)
      rationalIdeleClassDifferentialWeilQuotientMeasure where
  measurable := measurable_positiveRationalIdeleToIdeleClassHom
  map_eq := map_positiveRationalIdeleDifferentialHaar_restrict_fundamentalDomain

end RationalQuadraticSpaceMatrix
