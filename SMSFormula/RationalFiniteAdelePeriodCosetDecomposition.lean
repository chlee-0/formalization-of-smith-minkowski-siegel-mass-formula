import SMSFormula.RationalFiniteAdeleIntegralCosetDecomposition

/-!
# The finite adeles as the disjoint union of the cosets `r + N Ẑ`, `r ∈ ℚ ∩ [0, N)`

The period-`N` version of `RationalFiniteAdeleIntegralCosetDecomposition`.  For a positive
integer `N`, every finite adele differs from a rational number by an element of `N Ẑ` (strong
approximation applied to `y / N`), and two rationals are congruent modulo `N Ẑ` exactly when
they are congruent modulo `N ℤ` (`ℚ ∩ Ẑ = ℤ`).  The canonical representatives are
`ℚ ∩ [0, N)`.  Every coset has the volume of `N Ẑ`, and since `Ẑ` is the disjoint union of the `N`
cosets `j + N Ẑ`, `j = 0, …, N - 1`, that volume is `1/N`.  Hence for every `N Ẑ`-periodic
function

`∫_{𝔸_f} f = N⁻¹ ∑_{r ∈ ℚ ∩ [0,N)} f(r)`,

and an `N Ẑ`-periodic function is locally constant, hence continuous, and integrable exactly when
its representative values are absolutely summable.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace PositiveDefiniteIntegralLattice

/-- The canonical representatives `ℚ ∩ [0, N)` of `ℚ / N ℤ`. -/
abbrev RationalPeriodRep (N : ℕ) : Type := {r : ℚ // 0 ≤ r ∧ r < N}

/-- The coset `r + N Ẑ` of the finite adeles. -/
def rationalFiniteAdelePeriodCoset (N : ℕ) (r : ℚ) : Set RationalFiniteAdele :=
  {y | algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
      (y - algebraMap ℚ RationalFiniteAdele r) ∈ integralFiniteAdeleSubring}

variable {N : ℕ}

theorem rationalFiniteAdelePeriodCoset_eq_preimage (N : ℕ) (r : ℚ) :
    rationalFiniteAdelePeriodCoset N r =
      (fun y ↦ -algebraMap ℚ RationalFiniteAdele r + y) ⁻¹' rationalFiniteAdelePeriodCoset N 0 := by
  ext y
  simp only [rationalFiniteAdelePeriodCoset, Set.mem_setOf_eq, Set.mem_preimage, map_zero,
    sub_zero, neg_add_eq_sub]

theorem isOpen_rationalFiniteAdelePeriodCoset (N : ℕ) (r : ℚ) :
    IsOpen (rationalFiniteAdelePeriodCoset N r) :=
  isOpen_integralFiniteAdeleSubring.preimage
    (continuous_const.mul (continuous_id.sub continuous_const))

theorem measurableSet_rationalFiniteAdelePeriodCoset (N : ℕ) (r : ℚ) :
    MeasurableSet (rationalFiniteAdelePeriodCoset N r) :=
  (isOpen_rationalFiniteAdelePeriodCoset N r).measurableSet

theorem algebraMap_natCast_mul_inv_mul (hN : N ≠ 0) (w : RationalFiniteAdele) :
    algebraMap ℚ RationalFiniteAdele (N : ℚ) *
        (algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ * w) = w := by
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hN), map_one, one_mul]

/-- Membership in the coset `r + N Ẑ`, in translated form. -/
theorem mem_rationalFiniteAdelePeriodCoset_iff (hN : N ≠ 0) (r : ℚ) (y : RationalFiniteAdele) :
    y ∈ rationalFiniteAdelePeriodCoset N r ↔
      ∃ z ∈ integralFiniteAdeleSubring,
        y = algebraMap ℚ RationalFiniteAdele r + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z := by
  constructor
  · intro hy
    refine ⟨_, hy, ?_⟩
    rw [algebraMap_natCast_mul_inv_mul hN]
    abel
  · rintro ⟨z, hz, rfl⟩
    change algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
      (algebraMap ℚ RationalFiniteAdele r + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z -
        algebraMap ℚ RationalFiniteAdele r) ∈ integralFiniteAdeleSubring
    rw [add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hN),
      map_one, one_mul]
    exact hz

/-- The period cosets over the canonical representatives cover the finite adeles. -/
theorem exists_mem_rationalFiniteAdelePeriodCoset (hN : N ≠ 0) (y : RationalFiniteAdele) :
    ∃ r : RationalPeriodRep N, y ∈ rationalFiniteAdelePeriodCoset N r.1 := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring
    (algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ * y)
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨⟨(N : ℚ) * Int.fract q, mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg q), ?_⟩, ?_⟩
  · calc (N : ℚ) * Int.fract q < (N : ℚ) * 1 :=
          mul_lt_mul_of_pos_left (Int.fract_lt_one q) hNpos
      _ = N := mul_one _
  · have hsplit : algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
        (y - algebraMap ℚ RationalFiniteAdele ((N : ℚ) * Int.fract q)) =
        (algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ * y - algebraMap ℚ RationalFiniteAdele q) +
          algebraMap ℚ RationalFiniteAdele (⌊q⌋ : ℚ) := by
      have hc : (N : ℚ)⁻¹ * ((N : ℚ) * Int.fract q) = q - ⌊q⌋ := by
        rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul, Int.fract]
      rw [mul_sub, ← map_mul, hc, map_sub]
      ring
    change algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
      (y - algebraMap ℚ RationalFiniteAdele ((N : ℚ) * Int.fract q)) ∈ integralFiniteAdeleSubring
    rw [hsplit]
    exact add_mem hq (algebraMap_intCast_mem_integralFiniteAdeleSubring _)

/-- The period cosets over the canonical representatives are pairwise disjoint. -/
theorem eq_of_mem_rationalFiniteAdelePeriodCoset (hN : N ≠ 0) {r s : RationalPeriodRep N}
    {y : RationalFiniteAdele} (hr : y ∈ rationalFiniteAdelePeriodCoset N r.1)
    (hs : y ∈ rationalFiniteAdelePeriodCoset N s.1) : r = s := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hdiff : algebraMap ℚ RationalFiniteAdele ((N : ℚ)⁻¹ * (s.1 - r.1)) ∈
      integralFiniteAdeleSubring := by
    have hEq : algebraMap ℚ RationalFiniteAdele ((N : ℚ)⁻¹ * (s.1 - r.1)) =
        algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ * (y - algebraMap ℚ RationalFiniteAdele r.1) -
          algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
            (y - algebraMap ℚ RationalFiniteAdele s.1) := by
      rw [map_mul, map_sub]
      ring
    rw [hEq]
    exact sub_mem hr hs
  obtain ⟨k, hk⟩ := (rational_mem_integralFiniteAdeleSubring_iff _).1 hdiff
  have hcast : algebraMap ℤ ℚ k = (k : ℚ) := rfl
  rw [hcast] at hk
  have hk' : s.1 - r.1 = (N : ℚ) * k := by
    rw [hk, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  have hlt : (N : ℚ) * k < N * 1 := by
    rw [mul_one, ← hk']
    linarith [r.2.1, s.2.2]
  have hgt : (N : ℚ) * (-1) < N * k := by
    rw [← hk']
    linarith [r.2.2, s.2.1]
  have hk1 : (k : ℚ) < 1 := lt_of_mul_lt_mul_left hlt hNpos.le
  have hk2 : (-1 : ℚ) < k := lt_of_mul_lt_mul_left hgt hNpos.le
  have hk0 : k = 0 := by
    have h1 : k < 1 := by exact_mod_cast hk1
    have h2 : -1 < k := by exact_mod_cast hk2
    omega
  apply Subtype.ext
  rw [hk0, Int.cast_zero, mul_zero, sub_eq_zero] at hk'
  exact hk'.symm

theorem iUnion_rationalFiniteAdelePeriodCoset (hN : N ≠ 0) :
    (⋃ r : RationalPeriodRep N, rationalFiniteAdelePeriodCoset N r.1) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ?_
  obtain ⟨r, hr⟩ := exists_mem_rationalFiniteAdelePeriodCoset hN y
  exact Set.mem_iUnion.2 ⟨r, hr⟩

theorem pairwise_disjoint_rationalFiniteAdelePeriodCoset (hN : N ≠ 0) :
    Pairwise (Function.onFun Disjoint fun r : RationalPeriodRep N ↦
      rationalFiniteAdelePeriodCoset N r.1) := by
  intro r s hrs
  exact Set.disjoint_left.2 fun _ hr hs ↦ hrs (eq_of_mem_rationalFiniteAdelePeriodCoset hN hr hs)

/-- An `N Ẑ`-periodic function is constant on each period coset. -/
theorem eq_of_mem_rationalFiniteAdelePeriodCoset_of_periodic (hN : N ≠ 0) {E : Type*}
    (f : RationalFiniteAdele → E)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring →
      f (y + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z) = f y) (r : ℚ)
    {y : RationalFiniteAdele} (hy : y ∈ rationalFiniteAdelePeriodCoset N r) :
    f y = f (algebraMap ℚ RationalFiniteAdele r) := by
  obtain ⟨z, hz, rfl⟩ := (mem_rationalFiniteAdelePeriodCoset_iff hN r y).1 hy
  exact hf _ z hz

/-- An `N Ẑ`-periodic function is continuous (it is locally constant). -/
theorem continuous_of_periodPeriodic (hN : N ≠ 0) {E : Type*} [TopologicalSpace E]
    (f : RationalFiniteAdele → E)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring →
      f (y + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z) = f y) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  have hopen : IsOpen {y' : RationalFiniteAdele | algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
      (y' - y) ∈ integralFiniteAdeleSubring} :=
    isOpen_integralFiniteAdeleSubring.preimage
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hmem : y ∈ {y' : RationalFiniteAdele | algebraMap ℚ RationalFiniteAdele (N : ℚ)⁻¹ *
      (y' - y) ∈ integralFiniteAdeleSubring} := by
    simp only [Set.mem_setOf_eq, sub_self, mul_zero]
    exact zero_mem _
  have hev : (fun _ ↦ f y) =ᶠ[𝓝 y] f := by
    filter_upwards [hopen.mem_nhds hmem] with y' hy'
    have h := hf y _ hy'
    rw [algebraMap_natCast_mul_inv_mul hN, add_sub_cancel] at h
    exact h.symm
  exact (continuousAt_const).congr hev

/-! ## The volume of `N Ẑ` -/

/-- The common volume of the period cosets. -/
theorem rationalFiniteAdeleAddHaarMeasure_periodCoset (N : ℕ) (r : ℚ) :
    rationalFiniteAdeleAddHaarMeasure (rationalFiniteAdelePeriodCoset N r) =
      rationalFiniteAdeleAddHaarMeasure (rationalFiniteAdelePeriodCoset N 0) := by
  rw [rationalFiniteAdelePeriodCoset_eq_preimage, measure_preimage_add]

/-- The integer representatives `0, …, N - 1`. -/
def rationalPeriodRepOfFin (N : ℕ) (j : Fin N) : RationalPeriodRep N :=
  ⟨(j : ℚ), by positivity, by exact_mod_cast j.2⟩

/-- `Ẑ` is the union of the `N` cosets `j + N Ẑ`. -/
theorem integralFiniteAdeleSubring_eq_iUnion_periodCoset (hN : N ≠ 0) :
    (integralFiniteAdeleSubring : Set RationalFiniteAdele) =
      ⋃ j : Fin N, rationalFiniteAdelePeriodCoset N (j : ℚ) := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  ext y
  simp only [SetLike.mem_coe, Set.mem_iUnion]
  constructor
  · intro hy
    obtain ⟨r, hr⟩ := exists_mem_rationalFiniteAdelePeriodCoset hN y
    obtain ⟨z, hz, hyz⟩ := (mem_rationalFiniteAdelePeriodCoset_iff hN r.1 y).1 hr
    have hrint : algebraMap ℚ RationalFiniteAdele r.1 ∈ integralFiniteAdeleSubring := by
      have : algebraMap ℚ RationalFiniteAdele r.1 =
          y - algebraMap ℚ RationalFiniteAdele (N : ℚ) * z := by
        rw [hyz]; ring
      rw [this]
      exact sub_mem hy (Subring.mul_mem _
        (by exact_mod_cast algebraMap_intCast_mem_integralFiniteAdeleSubring (N : ℤ)) hz)
    obtain ⟨k, hk⟩ := (rational_mem_integralFiniteAdeleSubring_iff _).1 hrint
    have hcast : algebraMap ℤ ℚ k = (k : ℚ) := rfl
    rw [hcast] at hk
    have hk0 : 0 ≤ k := by
      have : (0 : ℚ) ≤ k := hk ▸ r.2.1
      exact_mod_cast this
    have hkN : k < N := by
      have : (k : ℚ) < N := hk ▸ r.2.2
      exact_mod_cast this
    refine ⟨⟨k.toNat, by omega⟩, ?_⟩
    have hkq : ((⟨k.toNat, by omega⟩ : Fin N) : ℚ) = r.1 := by
      rw [← hk]
      simp only
      exact_mod_cast Int.toNat_of_nonneg hk0
    rw [hkq]
    exact hr
  · rintro ⟨j, hj⟩
    obtain ⟨z, hz, rfl⟩ := (mem_rationalFiniteAdelePeriodCoset_iff hN _ y).1 hj
    exact add_mem (by exact_mod_cast algebraMap_intCast_mem_integralFiniteAdeleSubring (j : ℤ))
      (Subring.mul_mem _
        (by exact_mod_cast algebraMap_intCast_mem_integralFiniteAdeleSubring (N : ℤ)) hz)

/-- The volume of `N Ẑ` is `1/N`. -/
theorem rationalFiniteAdeleAddHaarMeasure_periodCoset_zero (hN : N ≠ 0) :
    rationalFiniteAdeleAddHaarMeasure (rationalFiniteAdelePeriodCoset N 0) = (N : ENNReal)⁻¹ := by
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin N ↦
      rationalFiniteAdelePeriodCoset N (j : ℚ)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun y hi hj ↦ hij ?_
    have h := eq_of_mem_rationalFiniteAdelePeriodCoset hN
      (r := rationalPeriodRepOfFin N i) (s := rationalPeriodRepOfFin N j) hi hj
    have h' : ((i : ℕ) : ℚ) = ((j : ℕ) : ℚ) := congrArg Subtype.val h
    exact Fin.ext (by exact_mod_cast h')
  have hone := rationalFiniteAdeleAddHaarMeasure_integral
  rw [integralFiniteAdeleSubring_eq_iUnion_periodCoset hN,
    measure_iUnion hdisj (fun j ↦ measurableSet_rationalFiniteAdelePeriodCoset N _),
    tsum_fintype] at hone
  simp_rw [rationalFiniteAdeleAddHaarMeasure_periodCoset N] at hone
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hone
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hone)).trans rfl

@[simp]
theorem rationalFiniteAdeleAddHaarMeasure_periodCoset_eq (hN : N ≠ 0) (r : ℚ) :
    rationalFiniteAdeleAddHaarMeasure (rationalFiniteAdelePeriodCoset N r) = (N : ENNReal)⁻¹ := by
  rw [rationalFiniteAdeleAddHaarMeasure_periodCoset, rationalFiniteAdeleAddHaarMeasure_periodCoset_zero hN]

/-! ## Integrals of periodic functions -/

/-- The period coset decomposition, Lebesgue form. -/
theorem lintegral_eq_tsum_of_periodPeriodic (hN : N ≠ 0) (f : RationalFiniteAdele → ENNReal)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring →
      f (y + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z) = f y) :
    ∫⁻ y, f y ∂rationalFiniteAdeleAddHaarMeasure =
      ∑' r : RationalPeriodRep N, f (algebraMap ℚ RationalFiniteAdele r.1) * (N : ENNReal)⁻¹ := by
  have hU := lintegral_iUnion (μ := rationalFiniteAdeleAddHaarMeasure)
    (s := fun r : RationalPeriodRep N ↦ rationalFiniteAdelePeriodCoset N r.1)
    (fun r ↦ measurableSet_rationalFiniteAdelePeriodCoset N r.1)
    (pairwise_disjoint_rationalFiniteAdelePeriodCoset hN) f
  rw [iUnion_rationalFiniteAdelePeriodCoset hN, setLIntegral_univ] at hU
  rw [hU]
  refine tsum_congr fun r ↦ ?_
  rw [setLIntegral_congr_fun (measurableSet_rationalFiniteAdelePeriodCoset N r.1)
      (fun y hy ↦ eq_of_mem_rationalFiniteAdelePeriodCoset_of_periodic hN f hf r.1 hy),
    setLIntegral_const, rationalFiniteAdeleAddHaarMeasure_periodCoset_eq hN]

/-- A periodic function with absolutely summable representative values is integrable. -/
theorem integrable_of_periodPeriodic (hN : N ≠ 0) (f : RationalFiniteAdele → ℂ)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring →
      f (y + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z) = f y)
    (hsum : Summable fun r : RationalPeriodRep N ↦ ‖f (algebraMap ℚ RationalFiniteAdele r.1)‖) :
    Integrable f rationalFiniteAdeleAddHaarMeasure := by
  refine ⟨(continuous_of_periodPeriodic hN f hf).aestronglyMeasurable, ?_⟩
  change ∫⁻ y, ‖f y‖ₑ ∂rationalFiniteAdeleAddHaarMeasure < ⊤
  rw [lintegral_eq_tsum_of_periodPeriodic hN (fun y ↦ ‖f y‖ₑ)
    (fun y z hz ↦ by simp only [hf y z hz]), ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ (ENNReal.inv_lt_top.2 (by exact_mod_cast Nat.pos_of_ne_zero hN))
  have hne : (∑' r : RationalPeriodRep N,
      ((‖f (algebraMap ℚ RationalFiniteAdele r.1)‖₊ : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.2 (by simpa only [coe_nnnorm] using hsum)
  simpa only [enorm_eq_nnnorm] using lt_top_iff_ne_top.2 hne

/-- The period coset decomposition, Bochner form:
`∫_{𝔸_f} f = N⁻¹ ∑_{r ∈ ℚ ∩ [0,N)} f(r)` for integrable `N Ẑ`-periodic `f`. -/
theorem integral_eq_tsum_of_periodPeriodic (hN : N ≠ 0) (f : RationalFiniteAdele → ℂ)
    (hint : Integrable f rationalFiniteAdeleAddHaarMeasure)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring →
      f (y + algebraMap ℚ RationalFiniteAdele (N : ℚ) * z) = f y) :
    ∫ y, f y ∂rationalFiniteAdeleAddHaarMeasure =
      ((N : ℂ))⁻¹ * ∑' r : RationalPeriodRep N, f (algebraMap ℚ RationalFiniteAdele r.1) := by
  have hU := integral_iUnion (μ := rationalFiniteAdeleAddHaarMeasure) (f := f)
    (s := fun r : RationalPeriodRep N ↦ rationalFiniteAdelePeriodCoset N r.1)
    (fun r ↦ measurableSet_rationalFiniteAdelePeriodCoset N r.1)
    (pairwise_disjoint_rationalFiniteAdelePeriodCoset hN) hint.integrableOn
  rw [iUnion_rationalFiniteAdelePeriodCoset hN, setIntegral_univ] at hU
  rw [hU, ← tsum_mul_left]
  refine tsum_congr fun r ↦ ?_
  rw [setIntegral_congr_fun (measurableSet_rationalFiniteAdelePeriodCoset N r.1)
      (fun y hy ↦ eq_of_mem_rationalFiniteAdelePeriodCoset_of_periodic hN f hf r.1 hy),
    setIntegral_const, Measure.real, rationalFiniteAdeleAddHaarMeasure_periodCoset_eq hN,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  ring

end PositiveDefiniteIntegralLattice
