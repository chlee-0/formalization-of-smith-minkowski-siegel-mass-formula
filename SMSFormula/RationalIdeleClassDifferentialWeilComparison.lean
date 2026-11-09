import SMSFormula.RationalIdeleDifferentialHaar
import SMSFormula.RationalIdeleClassHaarMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Independent idele-class Haar versus the differential Weil quotient

The independently selected Mathlib Haar measure on rational idele classes is
compared with the Weil quotient induced from compact-normalized differential
idele Haar.  The quotient is not finite: its Haar regularity is proved from
the exact measurable fundamental domain, not from Mathlib's finite-quotient
Haar theorem.

The restriction of differential idele Haar to the exact transversal is
sigma-finite.  On that transversal the quotient map is a measurable
embedding, so its pushforward is sigma-finite.  Fundamental-domain
nonvanishing and the quotient Weil identity give a nonzero left-invariant
measure.  Sigma-finite Haar uniqueness then upgrades it to a genuine Haar
measure and supplies the unique positive finite comparison scalar.

No local chart normalization, Euler product, sheet factor, or scalar-one
assertion is used.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleClassDifferentialComparisonFiniteAdeleT2 :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance rationalIdeleClassDifferentialComparisonInfiniteAdeleT2 :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance rationalIdeleClassDifferentialComparisonAdeleT2 :
    T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

local instance rationalIdeleClassDifferentialComparisonAction :
    MulAction RationalAdeleˣ RationalAdeleˣ :=
  Monoid.toMulAction RationalAdeleˣ

local instance rationalIdeleClassDifferentialComparisonDiagonalAction :
    MulAction rationalIdeleDiagonalSubgroup RationalAdeleˣ :=
  Subgroup.instMulAction

local instance rationalIdeleClassDifferentialComparisonDiagonalCountable :
    Countable rationalIdeleDiagonalSubgroup :=
  rationalIdeleDiagonalSubgroup_countable

local instance rationalIdeleClassDifferentialComparisonDiagonalOpCountable :
    Countable rationalIdeleDiagonalSubgroup.op := by
  let unopEquiv : rationalIdeleDiagonalSubgroup.op →
      rationalIdeleDiagonalSubgroup := fun gamma ↦
    ⟨MulOpposite.unop (gamma : RationalAdeleˣᵐᵒᵖ), gamma.2⟩
  apply Function.Injective.countable (f := unopEquiv)
  intro gamma delta h
  apply Subtype.ext
  exact MulOpposite.unop_injective (congrArg Subtype.val h)

/-! ## Sigma-finiteness and nonvanishing of the differential quotient -/

/-- The exact quotient map restricted to the measurable rational-idele
fundamental domain is a measurable embedding. -/
theorem measurableEmbedding_rationalIdeleClassQuotientMap_fundamentalDomain :
    MeasurableEmbedding
      (fun x : rationalIdeleMeasurableFundamentalDomain ↦
        rationalIdeleClassQuotientMap x) := by
  let F := rationalIdeleMeasurableFundamentalDomain
  let q := rationalIdeleClassQuotientMap
  have hF : MeasurableSet F :=
    measurableSet_rationalIdeleMeasurableFundamentalDomain
  refine
    { injective := ?_
      measurable :=
        rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable.comp
          measurable_subtype_coe
      measurableSet_image' := ?_ }
  · intro x y hxy
    exact Subtype.ext
      (rationalIdeleClassQuotientMap_injOn_fundamentalDomain x.2 y.2 hxy)
  · intro u hu
    let A : Set RationalAdeleˣ := ((↑) : F → RationalAdeleˣ) '' u
    have hA : MeasurableSet A :=
      (MeasurableEmbedding.subtype_coe hF).measurableSet_image.mpr hu
    have hsaturation :
        q ⁻¹' (q '' A) =
          ⋃ gamma : rationalIdeleDiagonalSubgroup,
            (fun a : RationalAdeleˣ ↦ (gamma : RationalAdeleˣ) * a) '' A := by
      ext x
      constructor
      · rintro ⟨a, ha, hax⟩
        let gamma : rationalIdeleDiagonalSubgroup :=
          ⟨x * a⁻¹, QuotientGroup.eq_iff_div_mem.mp hax.symm⟩
        refine Set.mem_iUnion.mpr ⟨gamma, a, ha, ?_⟩
        simp [gamma]
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨gamma, a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        unfold q rationalIdeleClassQuotientMap
        rw [map_mul]
        have hgamma :
            QuotientGroup.mk' rationalIdeleDiagonalSubgroup
                (gamma : RationalAdeleˣ) = 1 :=
          QuotientGroup.eq_one_iff _ |>.mpr gamma.2
        rw [hgamma]
        exact
          (one_mul
            (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a)).symm
    have hpreimage : MeasurableSet (q ⁻¹' (q '' A)) := by
      rw [hsaturation]
      exact MeasurableSet.iUnion fun gamma ↦
        (measurableEmbedding_mulLeft (gamma : RationalAdeleˣ))
          |>.measurableSet_image.mpr hA
    have hmapBorel :
        MeasurableSpace.map q (borel RationalAdeleˣ) =
          borel RationalIdeleClassGroup :=
      MeasurableSpace.map_borel_eq_borel_of_covering
        rationalIdeleClassQuotientMap_isCoveringMap
        (QuotientGroup.mk'_surjective rationalIdeleDiagonalSubgroup)
    have himage :
        (fun x : F ↦ q x) '' u = q '' A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
        exact ⟨z, hz, congrArg q hzx⟩
    rw [himage]
    rw [rationalIdeleClassGroup_measurableSpace_eq_borel]
    rw [← hmapBorel]
    exact hpreimage

/-- The differential Weil quotient is sigma-finite even though its total mass
need not be finite.  The proof uses injectivity on the exact transversal. -/
noncomputable instance rationalIdeleClassDifferentialWeilQuotientMeasure_sigmaFinite :
    SigmaFinite rationalIdeleClassDifferentialWeilQuotientMeasure := by
  let F := rationalIdeleMeasurableFundamentalDomain
  let μ := rationalIdeleDifferentialHaarMeasure
  let μF : Measure F := Measure.comap ((↑) : F → RationalAdeleˣ) μ
  have hF : MeasurableSet F :=
    measurableSet_rationalIdeleMeasurableFundamentalDomain
  have hmapCoe : Measure.map ((↑) : F → RationalAdeleˣ) μF = μ.restrict F := by
    exact map_comap_subtype_coe hF μ
  letI : SigmaFinite (μ.restrict F) := by infer_instance
  letI : SigmaFinite μF := by
    apply SigmaFinite.of_map μF measurable_subtype_coe.aemeasurable
    rw [hmapCoe]
    infer_instance
  have hqSigma : SigmaFinite
      (Measure.map
        (fun x : F ↦ rationalIdeleClassQuotientMap x) μF) :=
    measurableEmbedding_rationalIdeleClassQuotientMap_fundamentalDomain.sigmaFinite_map
  rw [rationalIdeleClassDifferentialWeilQuotientMeasure]
  rw [← hmapCoe, Measure.map_map]
  · exact hqSigma
  · exact rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable
  · exact measurable_subtype_coe

/-- Differential idele Haar gives the exact rational-diagonal transversal
nonzero mass. -/
theorem rationalIdeleDifferentialHaarMeasure_fundamentalDomain_ne_zero :
    rationalIdeleDifferentialHaarMeasure
        rationalIdeleMeasurableFundamentalDomain ≠ 0 := by
  letI : Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure
  have hμ : rationalIdeleDifferentialHaarMeasure ≠ 0 := by
    intro hzero
    have huniv : rationalIdeleDifferentialHaarMeasure Set.univ ≠ 0 :=
      isOpen_univ.measure_ne_zero rationalIdeleDifferentialHaarMeasure
        Set.univ_nonempty
    rw [hzero] at huniv
    exact huniv rfl
  exact rationalIdeleDifferentialHaar_isFundamentalDomain.measure_ne_zero
    hμ

/-- The induced differential quotient is nonzero. -/
theorem rationalIdeleClassDifferentialWeilQuotientMeasure_ne_zero :
    rationalIdeleClassDifferentialWeilQuotientMeasure ≠ 0 := by
  intro hzero
  have huniv := congrArg
    (fun μ : Measure RationalIdeleClassGroup ↦ μ Set.univ) hzero
  unfold rationalIdeleClassDifferentialWeilQuotientMeasure at huniv
  change
    (Measure.map rationalIdeleClassQuotientMap
      (rationalIdeleDifferentialHaarMeasure.restrict
        rationalIdeleMeasurableFundamentalDomain)) Set.univ = 0 at huniv
  rw [Measure.map_apply
      rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable
      MeasurableSet.univ] at huniv
  simp only [preimage_univ, Measure.restrict_apply_univ] at huniv
  exact rationalIdeleDifferentialHaarMeasure_fundamentalDomain_ne_zero huniv

/-! ## Haar regularity of the induced quotient -/

/-- Translation of rational idele classes by an ambient idele preserves the
differential Weil quotient.  This is the specialized fundamental-domain
calculation that avoids the unavailable `PolishSpace RationalAdeleˣ`
assumption of Mathlib's general quotient theorem. -/
theorem rationalIdeleClassDifferentialWeilQuotientMeasure_preimage_smul
    (g : RationalAdeleˣ) (A : Set RationalIdeleClassGroup)
    (hA : MeasurableSet A) :
    rationalIdeleClassDifferentialWeilQuotientMeasure
        ((fun c : RationalIdeleClassGroup ↦ g • c) ⁻¹' A) =
      rationalIdeleClassDifferentialWeilQuotientMeasure A := by
  let q := rationalIdeleClassQuotientMap
  let F := rationalIdeleMeasurableFundamentalDomain
  have hF : IsFundamentalDomain rationalIdeleDiagonalSubgroup.op F
      rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaar_isFundamentalDomain_op
  have hgF : IsFundamentalDomain rationalIdeleDiagonalSubgroup.op (g • F)
      rationalIdeleDifferentialHaarMeasure :=
    hF.smul_of_comm g
  have hpreA : MeasurableSet
      ((fun c : RationalIdeleClassGroup ↦ g • c) ⁻¹' A) :=
    hA.preimage (continuous_const_smul g).measurable
  erw [hF.projection_respects_measure_apply
      rationalIdeleClassDifferentialWeilQuotientMeasure hpreA,
    hgF.projection_respects_measure_apply
      rationalIdeleClassDifferentialWeilQuotientMeasure hA]
  change rationalIdeleDifferentialHaarMeasure
      (q ⁻¹' ((fun c : RationalIdeleClassGroup ↦ g • c) ⁻¹' A) ∩ F) =
    rationalIdeleDifferentialHaarMeasure (q ⁻¹' A ∩ g • F)
  have hpre :
      q ⁻¹' ((fun c : RationalIdeleClassGroup ↦ g • c) ⁻¹' A) =
        (g * ·) ⁻¹' (q ⁻¹' A) := by
    ext x
    simp [q, rationalIdeleClassQuotientMap, QuotientGroup.mk']
  rw [hpre]
  have hinter :
      rationalIdeleDifferentialHaarMeasure
          ((g * ·) ⁻¹' (q ⁻¹' A) ∩ F) =
        rationalIdeleDifferentialHaarMeasure
          (q ⁻¹' A ∩ (g⁻¹ * ·) ⁻¹' F) := by
    trans rationalIdeleDifferentialHaarMeasure
      ((g * ·) ⁻¹' (q ⁻¹' A ∩ (g⁻¹ * ·) ⁻¹' F))
    · rw [preimage_inter]
      congr 2
      simp [Set.preimage]
    rw [measure_preimage_mul]
  rw [hinter, ← preimage_smul_inv]
  rfl

/-- The differential Weil quotient is left invariant. -/
noncomputable instance
    rationalIdeleClassDifferentialWeilQuotientMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant
      rationalIdeleClassDifferentialWeilQuotientMeasure where
  map_mul_left_eq_self c := by
    ext A hA
    obtain ⟨g, hg⟩ := @Quotient.exists_rep RationalAdeleˣ
      (QuotientGroup.leftRel rationalIdeleDiagonalSubgroup) c
    rw [Measure.map_apply (measurable_const_mul c) hA]
    have hpreimage :
        (fun z : RationalIdeleClassGroup ↦ c * z) ⁻¹' A =
          (fun z : RationalIdeleClassGroup ↦ g • z) ⁻¹' A := by
      ext z
      simp [← hg, ← MulAction.Quotient.coe_smul_out, ← Quotient.mk''_eq_mk]
    rw [hpreimage]
    exact rationalIdeleClassDifferentialWeilQuotientMeasure_preimage_smul g A hA

/-- The nonzero sigma-finite differential quotient is a genuine Haar measure
on the noncompact rational idele-class group. -/
noncomputable instance rationalIdeleClassDifferentialWeilQuotientMeasure_isHaarMeasure :
    Measure.IsHaarMeasure rationalIdeleClassDifferentialWeilQuotientMeasure := by
  let μ := rationalIdeleClassDifferentialWeilQuotientMeasure
  let K : PositiveCompacts RationalIdeleClassGroup := Classical.arbitrary _
  have heq : μ = μ K • Measure.haarMeasure K :=
    Measure.haarMeasure_unique μ K
  have hμ : μ ≠ 0 :=
    rationalIdeleClassDifferentialWeilQuotientMeasure_ne_zero
  have hK_ne : μ K ≠ 0 := by
    intro hK
    apply hμ
    rw [heq, hK, zero_smul]
  have hK_top : μ K ≠ ∞ := by
    by_contra hK_top
    have hexists : ∃ m : ℕ, μ (spanningSets μ m) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hμ
      apply Measure.measure_univ_eq_zero.mp
      rw [← iUnion_spanningSets μ]
      exact measure_iUnion_null h
    obtain ⟨m, hm_ne⟩ := hexists
    have hmeasure := congrArg
      (fun ν : Measure RationalIdeleClassGroup ↦ ν (spanningSets μ m)) heq
    change μ (spanningSets μ m) =
      (μ K • Measure.haarMeasure K) (spanningSets μ m) at hmeasure
    rw [Measure.smul_apply, hK_top] at hmeasure
    have hhaar_ne :
        Measure.haarMeasure K (spanningSets μ m) ≠ 0 := by
      intro hhaar
      apply hm_ne
      simpa [hhaar] using hmeasure
    have hm_top : μ (spanningSets μ m) = ∞ := by
      simpa [hhaar_ne] using hmeasure
    exact (measure_spanningSets_lt_top μ m).ne hm_top
  change Measure.IsHaarMeasure μ
  rw [heq]
  exact Measure.IsHaarMeasure.smul (Measure.haarMeasure K) hK_ne hK_top

/-! ## The independent class-Haar conversion scalar -/

/-- The unique positive finite scalar carrying the differential Weil quotient
to the independently selected Mathlib Haar measure on rational idele classes. -/
noncomputable def rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0 :=
  Measure.haarScalarFactor rationalIdeleClassHaarMeasure
    rationalIdeleClassDifferentialWeilQuotientMeasure

/-- The independent class-Haar conversion scalar is strictly positive. -/
theorem rationalIdeleClassHaarToDifferentialWeilScalar_pos :
    0 < rationalIdeleClassHaarToDifferentialWeilScalar := by
  unfold rationalIdeleClassHaarToDifferentialWeilScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Exact global comparison of the independently chosen idele-class Haar with
the differential Weil quotient.  The scalar remains explicit and is not
identified with one. -/
theorem rationalIdeleClassHaarMeasure_eq_smul_differentialWeilQuotient :
    rationalIdeleClassHaarMeasure =
      rationalIdeleClassHaarToDifferentialWeilScalar •
        rationalIdeleClassDifferentialWeilQuotientMeasure := by
  exact Measure.isMulLeftInvariant_eq_smul
    rationalIdeleClassHaarMeasure
    rationalIdeleClassDifferentialWeilQuotientMeasure

end RationalQuadraticSpaceMatrix
