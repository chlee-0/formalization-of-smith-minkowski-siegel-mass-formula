import SMSFormula.PadicScalarFactorization
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Instances.ZMod

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal Pointwise

namespace Padic

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩
local instance : MeasurableSpace ℤ_[prime] := borel _
local instance : BorelSpace ℤ_[prime] := ⟨rfl⟩

def scalarIntegralSet : Set ℚ_[prime] := Set.range (fun value : ℤ_[prime] ↦ (value : ℚ_[prime]))

theorem mem_scalarIntegralSet (value : ℚ_[prime]) :
    value ∈ scalarIntegralSet prime ↔ ‖value‖ ≤ 1 := by
  constructor
  · rintro ⟨value, rfl⟩
    exact value.property
  · intro hvalue
    exact ⟨⟨value, hvalue⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem isCompact_scalarIntegralSet : IsCompact (scalarIntegralSet prime) :=
  isCompact_range PadicInt.isOpenEmbedding_coe.continuous

theorem isOpen_scalarIntegralSet : IsOpen (scalarIntegralSet prime) :=
  PadicInt.isOpenEmbedding_coe.isOpen_range

variable (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]

theorem scalarIntegralSet_measure_ne_zero : haar (scalarIntegralSet prime) ≠ 0 :=
  ((isOpen_scalarIntegralSet prime).measure_pos haar ⟨0, ⟨0, rfl⟩⟩).ne'

theorem scalarIntegralSet_measure_ne_top : haar (scalarIntegralSet prime) ≠ ∞ :=
  (isCompact_scalarIntegralSet prime).measure_ne_top

include haar in
theorem distribHaarChar_eq_one_of_norm_eq_one (unit : ℚ_[prime]ˣ)
    (hunit : ‖(unit : ℚ_[prime])‖ = 1) :
    distribHaarChar ℚ_[prime] unit = 1 := by
  have hset : unit • scalarIntegralSet prime = scalarIntegralSet prime := by
    ext value
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_scalarIntegralSet,
      mem_scalarIntegralSet]
    simp [Units.smul_def, norm_mul, hunit]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (scalarIntegralSet_measure_ne_zero prime haar)
    (scalarIntegralSet_measure_ne_top prime haar)
  rw [hset]
  simp

private def integerInclusion : ℤ_[prime] →+ ℚ_[prime] where
  toFun value := value
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem integerReduction_kernel_measure (level : ℕ) :
    (Measure.comap (integerInclusion prime) haar)
        ((PadicInt.toZModPow (p := prime) level).toAddMonoidHom.ker : Set ℤ_[prime]) =
      (prime ^ level : ℝ≥0∞)⁻¹ * haar (scalarIntegralSet prime) := by
  let integerHaar := Measure.comap (integerInclusion prime) haar
  let reduction := (PadicInt.toZModPow (p := prime) level).toAddMonoidHom
  letI : integerHaar.IsAddLeftInvariant :=
    Measure.IsAddLeftInvariant.comap haar
      (show IsOpenEmbedding (integerInclusion prime) from
        PadicInt.isOpenEmbedding_coe).measurableEmbedding
  have hkernel : (reduction.ker : Set ℤ_[prime]) =
      Metric.closedBall 0 ((prime : ℝ) ^ (-level : ℤ)) := by
    ext value
    change PadicInt.toZModPow level value = 0 ↔ _
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (PadicInt.norm_le_pow_iff_mem_span_pow value level).symm
  have hopen : IsOpen (reduction.ker : Set ℤ_[prime]) := by
    rw [hkernel]
    exact IsUltrametricDist.isOpen_closedBall
      (x := (0 : ℤ_[prime])) (r := (prime : ℝ) ^ (-level : ℤ))
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : prime.Prime).ne_zero))
  have hrange : reduction.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (ZMod.ringHom_surjective (PadicInt.toZModPow level))
  have hindex : reduction.ker.index = prime ^ level := by
    rw [AddSubgroup.index_ker, hrange]
    simp
  letI : reduction.ker.FiniteIndex := inferInstance
  have hmeasure := AddSubgroup.index_mul_measure reduction.ker hopen.measurableSet integerHaar
  have htotal : integerHaar Set.univ = haar (scalarIntegralSet prime) := by
    rw [(show IsOpenEmbedding (integerInclusion prime) from
      PadicInt.isOpenEmbedding_coe).measurableEmbedding.comap_apply, Set.image_univ]
    rfl
  rw [hindex, htotal, Nat.cast_pow] at hmeasure
  have hnonzero : (prime ^ level : ℝ≥0∞) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : prime.Prime).ne_zero)
  have hfinite : (prime ^ level : ℝ≥0∞) ≠ ∞ := by simp
  calc
    integerHaar (reduction.ker : Set ℤ_[prime]) =
        (prime ^ level : ℝ≥0∞)⁻¹ *
          ((prime ^ level : ℝ≥0∞) * integerHaar (reduction.ker : Set ℤ_[prime])) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hnonzero hfinite, one_mul]
    _ = _ := by rw [hmeasure]

theorem scalarIntegralSet_prime_pow_measure (level : ℕ) :
    haar ((fun value : ℚ_[prime] ↦ (prime : ℚ_[prime]) ^ level * value) ''
      scalarIntegralSet prime) =
      (prime ^ level : ℝ≥0∞)⁻¹ * haar (scalarIntegralSet prime) := by
  have hset : (fun value : ℚ_[prime] ↦ (prime : ℚ_[prime]) ^ level * value) ''
      scalarIntegralSet prime =
      integerInclusion prime ''
        ((PadicInt.toZModPow (p := prime) level).toAddMonoidHom.ker : Set ℤ_[prime]) := by
    ext value
    constructor
    · rintro ⟨_, ⟨integer, rfl⟩, rfl⟩
      refine ⟨(prime : ℤ_[prime]) ^ level * integer, ?_, ?_⟩
      · change PadicInt.toZModPow level _ = 0
        rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _
      · simp [integerInclusion]
    · rintro ⟨integer, hinteger, rfl⟩
      change PadicInt.toZModPow level integer = 0 at hinteger
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hinteger
      obtain ⟨quotient, hquotient⟩ := hinteger
      refine ⟨quotient, ⟨quotient, rfl⟩, ?_⟩
      simp [integerInclusion, hquotient]
  rw [hset, ← (show IsOpenEmbedding (integerInclusion prime) from
    PadicInt.isOpenEmbedding_coe).measurableEmbedding.comap_apply]
  exact integerReduction_kernel_measure prime haar level

def scalarPrimeUnit : ℚ_[prime]ˣ :=
  Units.mk0 (prime : ℚ_[prime]) (by exact_mod_cast (Fact.out : prime.Prime).ne_zero)

include haar in
theorem distribHaarChar_scalarPrimeUnit :
    distribHaarChar ℚ_[prime] (scalarPrimeUnit prime) = (prime : ℝ≥0)⁻¹ := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (scalarIntegralSet_measure_ne_zero prime haar)
    (scalarIntegralSet_measure_ne_top prime haar)
  change haar ((fun value : ℚ_[prime] ↦ (prime : ℚ_[prime]) * value) ''
    scalarIntegralSet prime) = _
  rw [ENNReal.coe_inv (by exact_mod_cast (Fact.out : prime.Prime).ne_zero)]
  simpa using
    scalarIntegralSet_prime_pow_measure prime haar 1

include haar in
theorem distribHaarChar_eq_nnnorm (unit : ℚ_[prime]ˣ) :
    distribHaarChar ℚ_[prime] unit = ‖(unit : ℚ_[prime])‖₊ := by
  let integralUnit := integralUnitPart prime (unit : ℚ_[prime]) unit.ne_zero
  let fieldUnit : ℚ_[prime]ˣ :=
    Units.mk0 ((integralUnit : ℤ_[prime]) : ℚ_[prime])
      (norm_ne_zero_iff.mp (by
        rw [show ‖((integralUnit : ℤ_[prime]) : ℚ_[prime])‖ = 1 from
          norm_integralUnitPart prime (unit : ℚ_[prime]) unit.ne_zero]
        exact one_ne_zero))
  have hfactor : unit = fieldUnit * (scalarPrimeUnit prime) ^ (unit : ℚ_[prime]).valuation := by
    apply Units.ext
    simpa [fieldUnit, scalarPrimeUnit, integralUnit] using
      (integralUnitPart_mul_p_zpow prime (unit : ℚ_[prime]) unit.ne_zero).symm
  have hunit : distribHaarChar ℚ_[prime] fieldUnit = 1 :=
    distribHaarChar_eq_one_of_norm_eq_one prime haar fieldUnit (by
      simpa [fieldUnit, integralUnit] using
        norm_integralUnitPart prime (unit : ℚ_[prime]) unit.ne_zero)
  calc
    distribHaarChar ℚ_[prime] unit =
        ((prime : ℝ≥0)⁻¹) ^ (unit : ℚ_[prime]).valuation := by
      conv_lhs => rw [hfactor, map_mul, map_zpow, hunit,
        distribHaarChar_scalarPrimeUnit prime haar, one_mul]
    _ = ‖(unit : ℚ_[prime])‖₊ := by
      apply NNReal.eq
      simp only [NNReal.coe_zpow, NNReal.coe_natCast,
        coe_nnnorm, inv_zpow, ← zpow_neg]
      exact (norm_eq_zpow_neg_valuation unit.ne_zero).symm

theorem map_additiveHaar_mul_unit (unit : ℚ_[prime]ˣ) :
    Measure.map (fun value : ℚ_[prime] ↦ (unit : ℚ_[prime]) * value) haar =
      ‖(unit : ℚ_[prime])‖₊⁻¹ • haar := by
  change (DomMulAct.mk unit⁻¹) • haar = _
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular
    ((DomMulAct.mk unit⁻¹) • haar) haar,
    addHaarScalarFactor_smul_eq_distribHaarChar haar,
    map_inv, distribHaarChar_eq_nnnorm prime haar]

theorem map_additiveHaar_affine_restrict (offset coefficient : ℚ_[prime])
    (hcoefficient : coefficient ≠ 0) (source : Set ℚ_[prime]) :
    Measure.map (fun value : ℚ_[prime] ↦ offset + coefficient * value)
      (‖coefficient‖₊ • haar.restrict source) =
      haar.restrict ((fun value : ℚ_[prime] ↦ offset + coefficient * value) '' source) := by
  let affine := (Homeomorph.mulLeft₀ coefficient hcoefficient).trans (Homeomorph.addLeft offset)
  have hglobal : Measure.map affine haar = ‖coefficient‖₊⁻¹ • haar := by
    change Measure.map ((fun value : ℚ_[prime] ↦ offset + value) ∘
      (fun value : ℚ_[prime] ↦ coefficient * value)) haar = _
    rw [← Measure.map_map (g := fun value : ℚ_[prime] ↦ offset + value)
      (f := fun value : ℚ_[prime] ↦ coefficient * value)
      (continuous_const.add continuous_id).measurable (continuous_const.mul continuous_id).measurable]
    rw [show Measure.map (fun value : ℚ_[prime] ↦ coefficient * value) haar =
      ‖coefficient‖₊⁻¹ • haar from map_additiveHaar_mul_unit prime haar (Units.mk0 coefficient hcoefficient),
      Measure.map_smul, Measure.IsAddLeftInvariant.map_add_left_eq_self]
  have hrestrict := affine.measurableEmbedding.restrict_map haar (affine '' source)
  rw [Set.preimage_image_eq _ affine.injective, hglobal, Measure.restrict_smul] at hrestrict
  change Measure.map affine (‖coefficient‖₊ • haar.restrict source) = _
  rw [Measure.map_smul, ← hrestrict, smul_smul,
    mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hcoefficient), one_smul]
  rfl

end Padic
