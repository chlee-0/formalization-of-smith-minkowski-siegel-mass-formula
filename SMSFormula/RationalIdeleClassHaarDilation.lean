import SMSFormula.RationalIdeleClassNormOneCompactness
import SMSFormula.RationalIdeleClassHaarMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation of rational idele-class Haar cutoffs

The logarithmic module has compact kernel and the explicit exponential
section, hence is a proper surjective homomorphism.  Its pushforward of
rational idele-class Haar measure is therefore a Haar measure on the real
line.  Haar uniqueness exposes one common scalar multiple of Lebesgue
measure, and dilation by two contributes exactly the reciprocal factor
`1 / 2`.  The unknown Haar scalar occurs on both sides and is never
normalized separately.
-/

noncomputable section

open MeasureTheory
open Filter Topology
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleLogMultiplicativeMeasureSpace :
    MeasureSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasureSpace ℝ)

local instance rationalIdeleLogMultiplicativeBorelSpace :
    BorelSpace (Multiplicative ℝ) := by
  change BorelSpace ℝ
  infer_instance

local instance rationalIdeleLogMultiplicativeVolumeIsHaarMeasure :
    Measure.IsHaarMeasure (volume : Measure (Multiplicative ℝ)) := by
  letI : IsFiniteMeasureOnCompacts (volume : Measure (Multiplicative ℝ)) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  letI : Measure.IsOpenPosMeasure (volume : Measure (Multiplicative ℝ)) :=
    inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  refine
    { toIsMulLeftInvariant := ?_
      lt_top_of_isCompact := fun K hK => hK.measure_lt_top
      toIsOpenPosMeasure := inferInstance }
  constructor
  intro g
  change Measure.map (fun x : ℝ => g.toAdd + x) volume = volume
  exact MeasureTheory.map_add_left_eq_self volume g.toAdd

theorem rationalIdeleClassLogModuleHom_surjective :
    Function.Surjective rationalIdeleClassLogModuleHom := by
  intro t
  obtain ⟨c, hc⟩ := rationalIdeleClassLogModule_surjective t.toAdd
  refine ⟨c, ?_⟩
  apply Multiplicative.toAdd.injective
  exact hc

theorem rationalIdeleClassLogModuleHom_tendsto_cocompact :
    Filter.Tendsto rationalIdeleClassLogModuleHom
      (cocompact RationalIdeleClassGroup)
      (cocompact (Multiplicative ℝ)) := by
  apply CocompactMap.tendsto_of_forall_preimage
  intro s hs
  let e := rationalIdeleClassLogSplitContinuousMulEquiv
  have heq : rationalIdeleClassLogModuleHom ⁻¹' s =
      e.symm '' ((Set.univ : Set RationalIdeleClassNormOne) ×ˢ s) := by
    ext c
    constructor
    · intro hc
      refine ⟨e c, ⟨Set.mem_univ _, ?_⟩, e.symm_apply_apply c⟩
      have hsecond : (e c).2 = rationalIdeleClassLogModuleHom c := by
        apply Multiplicative.toAdd.injective
        exact rationalIdeleClassLogSplitContinuousMulEquiv_apply_log c
      rw [hsecond]
      exact hc
    · rintro ⟨x, hx, rfl⟩
      have hsecond :
          rationalIdeleClassLogModuleHom (e.symm x) = x.2 := by
        apply Multiplicative.toAdd.injective
        change rationalIdeleClassLogModule (e.symm x) = x.2.toAdd
        rw [← rationalIdeleClassLogSplitContinuousMulEquiv_apply_log
          (e.symm x), e.apply_symm_apply]
      change rationalIdeleClassLogModuleHom (e.symm x) ∈ s
      rw [hsecond]
      exact hx.2
  rw [heq]
  exact (isCompact_univ.prod hs).image e.symm.continuous

noncomputable instance rationalIdeleClassLogModulePushforwardIsHaarMeasure :
    Measure.IsHaarMeasure
      (Measure.map rationalIdeleClassLogModuleHom
        rationalIdeleClassHaarMeasure) :=
  Measure.isHaarMeasure_map rationalIdeleClassHaarMeasure
    rationalIdeleClassLogModuleHom
    continuous_rationalIdeleClassLogModuleHom
    rationalIdeleClassLogModuleHom_surjective
    rationalIdeleClassLogModuleHom_tendsto_cocompact

/-- The scalar relating the logarithmic pushforward of the chosen
idele-class Haar measure to Lebesgue measure. -/
noncomputable def rationalIdeleClassLogHaarScalar : ℝ≥0∞ :=
  Measure.haarScalarFactor
    (Measure.map rationalIdeleClassLogModuleHom
      rationalIdeleClassHaarMeasure)
    (volume : Measure (Multiplicative ℝ))

theorem map_rationalIdeleClassLogModuleHom_haar :
    Measure.map rationalIdeleClassLogModuleHom
        rationalIdeleClassHaarMeasure =
      rationalIdeleClassLogHaarScalar •
        (volume : Measure (Multiplicative ℝ)) := by
  exact Measure.isMulLeftInvariant_eq_smul
    (Measure.map rationalIdeleClassLogModuleHom
      rationalIdeleClassHaarMeasure)
    (volume : Measure (Multiplicative ℝ))

theorem rationalIdeleClassLogCutoffLIntegral_eq_real
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    rationalIdeleClassLogCutoffLIntegral f =
      rationalIdeleClassLogHaarScalar * ∫⁻ t : ℝ, f t := by
  unfold rationalIdeleClassLogCutoffLIntegral
  let g : Multiplicative ℝ → ℝ≥0∞ := fun t => f t.toAdd
  have hg : Measurable g := hf
  change (∫⁻ c : RationalIdeleClassGroup,
      g (rationalIdeleClassLogModuleHom c)
        ∂rationalIdeleClassHaarMeasure) = _
  calc
    (∫⁻ c : RationalIdeleClassGroup,
      g (rationalIdeleClassLogModuleHom c)
        ∂rationalIdeleClassHaarMeasure) =
        ∫⁻ t, g t ∂Measure.map rationalIdeleClassLogModuleHom
          rationalIdeleClassHaarMeasure := by
      exact (lintegral_map' hg.aemeasurable
        continuous_rationalIdeleClassLogModuleHom.measurable.aemeasurable).symm
    _ = rationalIdeleClassLogHaarScalar * ∫⁻ t : ℝ, f t := by
      rw [map_rationalIdeleClassLogModuleHom_haar,
        lintegral_smul_measure]
      rfl

theorem lintegral_comp_two_mul
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : ℝ, f (2 * t)) = (2 : ℝ≥0∞)⁻¹ * ∫⁻ t : ℝ, f t := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  calc
    (∫⁻ t : ℝ, f (2 * t)) =
        ∫⁻ t : ℝ, f t ∂Measure.map (fun t : ℝ => 2 * t) volume := by
      exact (lintegral_map' hf.aemeasurable
        (measurable_const.mul measurable_id).aemeasurable).symm
    _ = (2 : ℝ≥0∞)⁻¹ * ∫⁻ t : ℝ, f t := by
      rw [show (fun t : ℝ => 2 * t) = fun t => (2 : ℝ) • t by
          funext t; simp,
        Measure.map_addHaar_smul (volume : Measure ℝ) htwo,
        lintegral_smul_measure]
      simp only [Module.finrank_self, pow_one, abs_inv]
      norm_num only [abs_of_nonneg]
      rw [smul_eq_mul,
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- The full rational idele-class Haar cutoff obeys the literal
squaring-Jacobian formula. -/
theorem rationalIdeleClassLogCutoffLIntegral_two_mul
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    rationalIdeleClassLogCutoffLIntegral (fun t => f (2 * t)) =
      (2 : ℝ≥0∞)⁻¹ * rationalIdeleClassLogCutoffLIntegral f := by
  let g : ℝ → ℝ≥0∞ := fun t => f (2 * t)
  change rationalIdeleClassLogCutoffLIntegral g = _
  rw [rationalIdeleClassLogCutoffLIntegral_eq_real g
      (hf.comp (measurable_const.mul measurable_id)),
    rationalIdeleClassLogCutoffLIntegral_eq_real f hf,
    lintegral_comp_two_mul f hf]
  ac_rfl

end RationalQuadraticSpaceMatrix
