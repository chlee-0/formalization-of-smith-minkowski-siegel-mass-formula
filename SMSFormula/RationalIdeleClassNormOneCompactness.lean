import SMSFormula.RationalIdeleClassLogSplitting

/-!
# Compactness input for norm-one rational idele classes

The everywhere-integral finite ideles whose inverses are also integral form
the unit group of the compact integral finite-adele subring.  This compact
subgroup is the finite component of the compact representative set for the
kernel of the rational idele-class logarithmic module.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped NNReal

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleNormOneFiniteT2 : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

/-- Everywhere-integral finite ideles with integral inverse form a compact
subgroup of the finite idele group. -/
theorem isCompact_integralFiniteIdeleUnits :
    IsCompact integralFiniteIdeleUnits := by
  change IsCompact
    ((integralFiniteAdeleSubring.toSubmonoid).units : Set RationalFiniteAdeleˣ)
  exact Submonoid.units_isCompact isCompact_integralFiniteAdeleSubring

local instance rationalIdeleNormOnePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleNormOneDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) := Classical.decEq _

private theorem padicValRat_prime_zpow
    (p : {p : ℕ // p.Prime}) (k : ℤ) :
    padicValRat p.1 ((p.1 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  cases k with
  | ofNat m =>
      change padicValRat p.1 ((p.1 : ℚ) ^ m) = (m : ℤ)
      rw [padicValRat.pow]
      · rw [padicValRat.of_nat, padicValNat.self p.2.one_lt]
        simp
      · exact_mod_cast p.2.ne_zero
  | negSucc m =>
      change padicValRat p.1 ((p.1 : ℚ) ^ (Int.negSucc m)) = -(m + 1 : ℕ)
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow]
      · rw [padicValRat.of_nat, padicValNat.self p.2.one_lt]
        simp
      · exact_mod_cast p.2.ne_zero

private theorem padicValRat_other_prime_zpow
    (p q : {p : ℕ // p.Prime}) (hpq : p ≠ q) (k : ℤ) :
    padicValRat p.1 ((q.1 : ℚ) ^ k) = 0 := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hpq' : padicValNat p.1 q.1 = 0 :=
    padicValNat_primes (fun h => hpq (Subtype.ext h))
  cases k with
  | ofNat m =>
      change padicValRat p.1 ((q.1 : ℚ) ^ m) = 0
      rw [padicValRat.pow]
      · rw [padicValRat.of_nat, hpq']
        simp
      · exact_mod_cast q.2.ne_zero
  | negSucc m =>
      change padicValRat p.1 ((q.1 : ℚ) ^ (Int.negSucc m)) = 0
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow]
      · rw [padicValRat.of_nat, hpq']
        simp
      · exact_mod_cast q.2.ne_zero

/-- The rational scalar whose valuation cancels every nonintegral valuation
of a finite idele. -/
def finiteIdeleValuationNormalizer (a : RationalFiniteAdeleˣ) : ℚ :=
  ∏ v ∈ finiteIdeleNormSupport a,
    ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℚ) ^
      (-(finiteAdelicUnitHeightOneComponentHom v a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).valuation)

theorem finiteIdeleValuationNormalizer_ne_zero
    (a : RationalFiniteAdeleˣ) :
    finiteIdeleValuationNormalizer a ≠ 0 := by
  unfold finiteIdeleValuationNormalizer
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact zpow_ne_zero _ (by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).2.ne_zero)

theorem padicValRat_finiteIdeleValuationNormalizer
    (a : RationalFiniteAdeleˣ)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    padicValRat (Rat.HeightOneSpectrum.primesEquiv v).1
        (finiteIdeleValuationNormalizer a) =
      if v ∈ finiteIdeleNormSupport a then
        -(finiteAdelicUnitHeightOneComponentHom v a :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).valuation
      else 0 := by
  classical
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let f : IsDedekindDomain.HeightOneSpectrum ℤ → ℚ := fun w =>
    ((Rat.HeightOneSpectrum.primesEquiv w).1 : ℚ) ^
      (-(finiteAdelicUnitHeightOneComponentHom w a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).1]).valuation)
  have hf (w : IsDedekindDomain.HeightOneSpectrum ℤ) : f w ≠ 0 :=
    zpow_ne_zero _ (by
      exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv w).2.ne_zero)
  have hprod : ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      padicValRat p.1 (∏ w ∈ T, f w) =
        ∑ w ∈ T, padicValRat p.1 (f w) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert w T hw ih =>
        rw [Finset.prod_insert hw,
          padicValRat.mul (hf w)
            (Finset.prod_ne_zero_iff.mpr fun q _ => hf q),
          Finset.sum_insert hw, ih]
  rw [finiteIdeleValuationNormalizer, show
    (∏ w ∈ finiteIdeleNormSupport a,
      ((Rat.HeightOneSpectrum.primesEquiv w).1 : ℚ) ^
        (-(finiteAdelicUnitHeightOneComponentHom w a :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).1]).valuation)) =
      ∏ w ∈ finiteIdeleNormSupport a, f w by rfl,
    hprod]
  by_cases hv : v ∈ finiteIdeleNormSupport a
  · rw [if_pos hv, Finset.sum_eq_single v]
    · exact padicValRat_prime_zpow p _
    · intro w hw hwv
      exact padicValRat_other_prime_zpow p
        (Rat.HeightOneSpectrum.primesEquiv w)
        (fun h => hwv (Rat.HeightOneSpectrum.primesEquiv.injective h.symm)) _
    · exact fun h => False.elim (h hv)
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro w hw
    exact padicValRat_other_prime_zpow p
      (Rat.HeightOneSpectrum.primesEquiv w)
      (fun h => by
        apply hv
        have hvw : v = w :=
          Rat.HeightOneSpectrum.primesEquiv.injective h
        simpa [hvw] using hw) _

/-- The valuation normalizer as a rational unit. -/
def finiteIdeleValuationNormalizerUnit (a : RationalFiniteAdeleˣ) : ℚˣ :=
  Units.mk0 (finiteIdeleValuationNormalizer a)
    (finiteIdeleValuationNormalizer_ne_zero a)

theorem valuation_normalized_finiteIdele_component
    (a : RationalFiniteAdeleˣ)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ((finiteAdelicUnitHeightOneComponentHom v
      (rationalUnitFiniteAdelicDiagonalHom
        (finiteIdeleValuationNormalizerUnit a) * a) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])).valuation = 0 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have ha0 : (finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1]) ≠ 0 :=
    by exact Units.ne_zero _
  have hdiag : ((finiteAdelicUnitHeightOneComponentHom v
        (rationalUnitFiniteAdelicDiagonalHom
          (finiteIdeleValuationNormalizerUnit a)) : ℚ_[p.1])) =
        (finiteIdeleValuationNormalizer a : ℚ_[p.1]) := by
    change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (algebraMap ℚ RationalFiniteAdele
          (finiteIdeleValuationNormalizer a)) = _
    rw [(finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes]
    simp
  have hq0 : (finiteAdelicUnitHeightOneComponentHom v
        (rationalUnitFiniteAdelicDiagonalHom
          (finiteIdeleValuationNormalizerUnit a)) : ℚ_[p.1]) ≠ 0 := by
    rw [hdiag]
    exact_mod_cast finiteIdeleValuationNormalizer_ne_zero a
  rw [map_mul, Units.val_mul, Padic.valuation_mul hq0 ha0,
      hdiag,
      Padic.valuation_ratCast,
      padicValRat_finiteIdeleValuationNormalizer]
  by_cases hv : v ∈ finiteIdeleNormSupport a
  · rw [if_pos hv]
    omega
  · rw [if_neg hv, zero_add]
    have hvInt := (not_mem_finiteIdeleNormSupport_iff a v).1 hv
    have hnorm : ‖(finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])‖ = 1 := by
      have hxle := (mem_adicCompletionIntegers_iff_padic v _).1 hvInt.1
      have hile := (mem_adicCompletionIntegers_iff_padic v _).1 hvInt.2
      change ‖(finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])‖ ≤ 1 at hxle
      have hinvcomp :
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
              (((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v) =
            (finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])⁻¹ := by
        change (finiteAdelicUnitHeightOneComponentHom v a⁻¹ : ℚ_[p.1]) = _
        simpa only [Units.val_inv_eq_inv_val] using congrArg Units.val
          ((finiteAdelicUnitHeightOneComponentHom v).map_inv a)
      rw [hinvcomp] at hile
      change ‖((finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])⁻¹)‖ ≤ 1 at hile
      have hprod :
          ‖(finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])‖ *
            ‖((finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])⁻¹)‖ = 1 := by
        rw [← norm_mul]
        simp
      nlinarith [norm_nonneg
        (finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1]),
        norm_nonneg
          ((finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1])⁻¹)]
    rw [Padic.norm_eq_zpow_neg_valuation ha0] at hnorm
    have hpgt : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hpow : (p.1 : ℝ) ^
        (-(finiteAdelicUnitHeightOneComponentHom v a : ℚ_[p.1]).valuation) =
        (p.1 : ℝ) ^ (0 : ℤ) := by
      simpa using hnorm
    have hneg := (zpow_right_strictMono₀ hpgt).injective hpow
    omega

/-- Multiplying a finite idele by its rational valuation normalizer makes it
integral together with its inverse. -/
theorem normalized_finiteIdele_mem_integralFiniteIdeleUnits
    (a : RationalFiniteAdeleˣ) :
    rationalUnitFiniteAdelicDiagonalHom
        (finiteIdeleValuationNormalizerUnit a) * a ∈
      integralFiniteIdeleUnits := by
  let b := rationalUnitFiniteAdelicDiagonalHom
        (finiteIdeleValuationNormalizerUnit a) * a
  have hlocal (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      finiteAdelicUnitHeightOneComponentHom v b ∈
        padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [mem_padicIntegralUnitsSubgroup_iff]
    let x := (finiteAdelicUnitHeightOneComponentHom v b :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    have hx0 : x ≠ 0 := Units.ne_zero _
    have hval : x.valuation = 0 :=
      valuation_normalized_finiteIdele_component a v
    have hnorm : ‖x‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hx0, hval]
      simp
    constructor
    · change ‖x‖ ≤ 1
      rw [hnorm]
    · have hinv : x⁻¹ ∈ PadicInt.subring
          (Rat.HeightOneSpectrum.primesEquiv v).1 := by
        change ‖x⁻¹‖ ≤ 1
        rw [norm_inv, hnorm, inv_one]
      simpa only [Units.val_inv_eq_inv_val] using hinv
  change ((b : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) ∧
    (((b⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) ∈
      integralFiniteAdeleSubring)
  constructor
  · intro v
    exact (mem_adicCompletionIntegers_iff_padic v _).2 (hlocal v).1
  · intro v
    exact (mem_adicCompletionIntegers_iff_padic v _).2 (hlocal v).2

/-- Real units of absolute value one. -/
def realIdeleNormOneUnits : Set ℝˣ :=
  {u | ‖(u : ℝ)‖ = 1}

theorem realIdeleNormOneUnits_eq :
    realIdeleNormOneUnits = ({1, -1} : Set ℝˣ) := by
  ext u
  constructor
  · intro hu
    change ‖(u : ℝ)‖ = 1 at hu
    rw [Real.norm_eq_abs] at hu
    by_cases hnonneg : 0 ≤ (u : ℝ)
    · have huone : (u : ℝ) = 1 := by
        simpa [abs_of_nonneg hnonneg] using hu
      have : u = 1 := Units.ext huone
      simp [this]
    · have huneg : (u : ℝ) < 0 := lt_of_not_ge hnonneg
      have humone : (u : ℝ) = -1 := by
        have := hu
        rw [abs_of_neg huneg] at this
        linarith
      have : u = -1 := Units.ext humone
      simp [this]
  · intro hu
    rcases hu with (rfl | rfl)
    · simp [realIdeleNormOneUnits]
    · simp [realIdeleNormOneUnits]

theorem isCompact_realIdeleNormOneUnits :
    IsCompact realIdeleNormOneUnits := by
  rw [realIdeleNormOneUnits_eq]
  exact isCompact_singleton.union isCompact_singleton

/-- A compact set of full ideles with norm-one real component and integral
finite component. -/
def rationalIdeleNormOneCompactBlock : Set RationalAdeleˣ :=
  rationalAdeleUnitsRealFiniteContinuousEquiv ⁻¹'
    (realIdeleNormOneUnits ×ˢ integralFiniteIdeleUnits)

theorem isCompact_rationalIdeleNormOneCompactBlock :
    IsCompact rationalIdeleNormOneCompactBlock := by
  exact rationalAdeleUnitsRealFiniteContinuousEquiv.toHomeomorph.isCompact_preimage.mpr
    (isCompact_realIdeleNormOneUnits.prod
      isCompact_integralFiniteIdeleUnits)

theorem rationalIdeleClassLogModule_mk_eq_zero_of_mem_compactBlock
    (a : RationalAdeleˣ) (ha : a ∈ rationalIdeleNormOneCompactBlock) :
    rationalIdeleClassLogModule
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) = 0 := by
  rw [rationalIdeleClassLogModule_mk]
  have har :
      ‖((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ)‖ = 1 :=
    ha.1
  have haf : finiteIdeleModuleNNReal
      (rationalAdeleUnitsRealFiniteContinuousEquiv a).2 = 1 :=
    finiteIdeleModuleNNReal_eq_one_of_mem_integralFiniteIdeleUnits _ ha.2
  unfold rationalIdeleLogModule rationalIdeleModuleNNReal
  rw [haf, mul_one]
  change Real.log ‖((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ)‖ = 0
  rw [har, Real.log_one]

theorem exists_compactBlock_representative_of_logModule_eq_zero
    (c : RationalIdeleClassGroup)
    (hc : rationalIdeleClassLogModule c = 0) :
    ∃ a ∈ rationalIdeleNormOneCompactBlock,
      QuotientGroup.mk' rationalIdeleDiagonalSubgroup a = c := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective rationalIdeleDiagonalSubgroup c
  let af : RationalFiniteAdeleˣ :=
    (rationalAdeleUnitsRealFiniteContinuousEquiv a).2
  let q : ℚˣ := finiteIdeleValuationNormalizerUnit af
  let d : RationalAdeleˣ := rationalUnitFullAdelicDiagonalHom q
  let b : RationalAdeleˣ := d * a
  have hbf : (rationalAdeleUnitsRealFiniteContinuousEquiv b).2 ∈
      integralFiniteIdeleUnits := by
    change (rationalAdeleUnitsRealFiniteContinuousEquiv (d * a)).2 ∈ _
    rw [map_mul, rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal]
    exact normalized_finiteIdele_mem_integralFiniteIdeleUnits af
  have hbclass : QuotientGroup.mk' rationalIdeleDiagonalSubgroup b =
      QuotientGroup.mk' rationalIdeleDiagonalSubgroup a := by
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup (d * a) = _
    rw [map_mul]
    have hd : QuotientGroup.mk' rationalIdeleDiagonalSubgroup d = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨q, rfl⟩
    rw [hd]
    exact one_mul
      (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a)
  have hblog : rationalIdeleLogModule b = 0 := by
    rw [← rationalIdeleClassLogModule_mk]
    rw [hbclass]
    exact hc
  have hbmodule : rationalIdeleModuleNNReal b = 1 := by
    have hpos : 0 < (rationalIdeleModuleNNReal b : ℝ) :=
      NNReal.coe_pos.mpr ((pos_iff_ne_zero).2
        (rationalIdeleModuleNNReal_ne_zero b))
    have hexp := congrArg Real.exp hblog
    unfold rationalIdeleLogModule at hexp
    rw [Real.exp_log hpos, Real.exp_zero] at hexp
    exact NNReal.eq hexp
  have hbr : (rationalAdeleUnitsRealFiniteContinuousEquiv b).1 ∈
      realIdeleNormOneUnits := by
    have hbfmodule :=
      finiteIdeleModuleNNReal_eq_one_of_mem_integralFiniteIdeleUnits _ hbf
    rw [rationalIdeleModuleNNReal, hbfmodule, mul_one] at hbmodule
    change ‖((rationalAdeleUnitsRealFiniteContinuousEquiv b).1 : ℝ)‖ = 1
    exact congrArg (fun x : ℝ≥0 => (x : ℝ)) hbmodule
  refine ⟨b, ⟨hbr, hbf⟩, hbclass⟩

/-- The norm-one rational idele-class kernel is the image of the explicit
compact representative block. -/
theorem rationalIdeleClassNormOne_carrier_eq_compactBlock_image :
    (RationalIdeleClassNormOne : Set RationalIdeleClassGroup) =
      (fun a => QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) ''
        rationalIdeleNormOneCompactBlock := by
  ext c
  constructor
  · intro hc
    have hlog : rationalIdeleClassLogModule c = 0 := by
      exact congrArg Multiplicative.toAdd hc
    obtain ⟨a, ha, rfl⟩ :=
      exists_compactBlock_representative_of_logModule_eq_zero c hlog
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    change Multiplicative.ofAdd
        (rationalIdeleClassLogModule
          (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a)) = 1
    apply Multiplicative.toAdd.injective
    simpa using
      rationalIdeleClassLogModule_mk_eq_zero_of_mem_compactBlock a ha

/-- The kernel of the rational idele-class logarithmic module is compact. -/
theorem isCompact_rationalIdeleClassNormOne :
    IsCompact (RationalIdeleClassNormOne : Set RationalIdeleClassGroup) := by
  rw [rationalIdeleClassNormOne_carrier_eq_compactBlock_image]
  exact isCompact_rationalIdeleNormOneCompactBlock.image continuous_quot_mk

noncomputable instance rationalIdeleClassNormOneCompactSpace :
    CompactSpace RationalIdeleClassNormOne := by
  exact isCompact_iff_compactSpace.mp isCompact_rationalIdeleClassNormOne

end RationalQuadraticSpaceMatrix
