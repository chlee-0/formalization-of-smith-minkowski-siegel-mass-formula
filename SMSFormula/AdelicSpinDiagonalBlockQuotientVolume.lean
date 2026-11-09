import SMSFormula.RationalCliffordSpinDiagonalBlockGroup
import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor

/-!
# The block quotient volume is the square

If the block isomorphism `Φ_𝔸 : Spin(T)(𝔸)² ≃ₜ* Spin(U)(𝔸)` carries the product of two raw
differential Spin measures of `T` to the raw differential Spin measure of `U`, then the raw
Spin quotient volume of `U` is the square of that of `T`.

No Tonelli argument and no comparison of fundamental domains is made: `Φ_𝔸(F_T × F_T)` is an
exact measurable fundamental domain for the rational diagonal subgroup of `U` (the rational
diagonals correspond), and fundamental-domain uniqueness of measurable Weil quotient
measures accepts any exact measurable fundamental domain.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 400000

local instance diagonalBlockQuotientDiagonalCountable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
  V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable

theorem fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_sFinite {n : ℕ}
    (V : RationalQuadraticSpaceMatrix n) (s : ℝ≥0) :
    SFinite (V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure s) := by
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  haveI := V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  infer_instance

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

/-- The full-adelic block isomorphism. -/
abbrev diagonalBlockFullAdelicEquiv :=
  T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ RationalAdele

/-- The transported fundamental domain `Φ_𝔸(F_T × F_T)`. -/
def diagonalBlockFundamentalDomain :
    Set (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).FullAdelicCliffordSpinCandidateGroup :=
  (T.diagonalBlockFullAdelicEquiv hT hδ).symm ⁻¹'
    (T.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain ×ˢ
      T.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain)

theorem measurableSet_diagonalBlockFundamentalDomain :
    MeasurableSet (T.diagonalBlockFundamentalDomain hT hδ) :=
  (T.diagonalBlockFullAdelicEquiv hT hδ).symm.continuous.measurable
    (T.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain.prod
      T.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain)

theorem diagonalBlock_mem_diagonalSubgroup_iff
    (δ : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).FullAdelicCliffordSpinCandidateGroup) :
    δ ∈ (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup ↔
      ((T.diagonalBlockFullAdelicEquiv hT hδ).symm δ).1 ∈
          T.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup ∧
        ((T.diagonalBlockFullAdelicEquiv hT hδ).symm δ).2 ∈
          T.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  rw [← T.diagonalBlockSpinGroup_diagonalSubgroup_map hT hδ, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have : (T.diagonalBlockFullAdelicEquiv hT hδ).symm
        ((T.diagonalBlockSpinGroupMulEquiv hT hδ RationalAdele).toMonoidHom p) = p :=
      (T.diagonalBlockFullAdelicEquiv hT hδ).symm_apply_apply p
    rw [this]
    exact Subgroup.mem_prod.1 hp
  · intro h
    exact ⟨(T.diagonalBlockFullAdelicEquiv hT hδ).symm δ, Subgroup.mem_prod.2 h,
      (T.diagonalBlockFullAdelicEquiv hT hδ).apply_symm_apply δ⟩

/-- `Φ_𝔸(F_T × F_T)` is an exact fundamental domain for the rational diagonal of `U`. -/
theorem existsUnique_diagonalSubgroup_mul_mem_diagonalBlockFundamentalDomain
    (z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).FullAdelicCliffordSpinCandidateGroup) :
    ∃! γ : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
      (γ : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).FullAdelicCliffordSpinCandidateGroup) * z ∈
        T.diagonalBlockFundamentalDomain hT hδ := by
  let E := T.diagonalBlockFullAdelicEquiv hT hδ
  obtain ⟨γ₁, hγ₁, hu₁⟩ :=
    T.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain (E.symm z).1
  obtain ⟨γ₂, hγ₂, hu₂⟩ :=
    T.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain (E.symm z).2
  have hmem : E ((γ₁ : T.FullAdelicCliffordSpinCandidateGroup), (γ₂ : T.FullAdelicCliffordSpinCandidateGroup)) ∈
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
    rw [T.diagonalBlock_mem_diagonalSubgroup_iff hT hδ, E.symm_apply_apply]
    exact ⟨γ₁.2, γ₂.2⟩
  have hsymm_mul : ∀ w, E.symm (w * z) = ((E.symm w).1 * (E.symm z).1, (E.symm w).2 * (E.symm z).2) :=
    fun w ↦ by rw [map_mul]; rfl
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · simp only [diagonalBlockFundamentalDomain, Set.mem_preimage]
    rw [hsymm_mul, E.symm_apply_apply]
    exact ⟨hγ₁, hγ₂⟩
  · rintro ⟨w, hwmem⟩ hwz
    rw [T.diagonalBlock_mem_diagonalSubgroup_iff hT hδ] at hwmem
    simp only [diagonalBlockFundamentalDomain, Set.mem_preimage] at hwz
    rw [hsymm_mul] at hwz
    have e₁ := hu₁ ⟨_, hwmem.1⟩ hwz.1
    have e₂ := hu₂ ⟨_, hwmem.2⟩ hwz.2
    apply Subtype.ext
    change w = E (_, _)
    rw [← congrArg Subtype.val e₁, ← congrArg Subtype.val e₂]
    exact (E.apply_symm_apply w).symm

set_option backward.isDefEq.respectTransparency false in
/-- The block quotient volume is the square, given the adelic measure identity. -/
theorem diagonalBlock_quotientVolume_eq_mul_of_map (sT sU : ℝ≥0)
    (hmap : Measure.map (T.diagonalBlockFullAdelicEquiv hT hδ)
        ((T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sT).prod
          (T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sT)) =
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        sU) :
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        sU).quotientVolumeENNReal =
      (T.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData sT).quotientVolumeENNReal *
        (T.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData sT).quotientVolumeENNReal := by
  have hq := ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      sU).isMeasurableWeilQuotientMeasure.eq_leftQuotientFundamentalDomainMeasure _ rfl
    (T.measurableSet_diagonalBlockFundamentalDomain hT hδ)
    (T.existsUnique_diagonalSubgroup_mul_mem_diagonalBlockFundamentalDomain hT hδ)
  rw [CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal_eq, hq,
    leftQuotientFundamentalDomainMeasure_univ_map_mspace
      (Gamma := (T.nonisotropicLastExtension (f 0 * f 1 * f 2)
        hδ).rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup)
      (μG := ((T.nonisotropicLastExtension (f 0 * f 1 * f 2)
        hδ).fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData sU).adelicMeasure)
      (F := T.diagonalBlockFundamentalDomain hT hδ) rfl,
    fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_adelicMeasure, ← hmap,
    Measure.map_apply (map_continuous (T.diagonalBlockFullAdelicEquiv hT hδ)).measurable
      (T.measurableSet_diagonalBlockFundamentalDomain hT hδ)]
  have hpre : (T.diagonalBlockFullAdelicEquiv hT hδ) ⁻¹' T.diagonalBlockFundamentalDomain hT hδ =
      T.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain ×ˢ
        T.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
    ext p
    simp only [diagonalBlockFundamentalDomain, Set.mem_preimage, ContinuousMulEquiv.symm_apply_apply]
  haveI := T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_sFinite sT
  rw [hpre, Measure.prod_prod,
    T.fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_domainMass]

end RationalQuadraticSpaceMatrix
