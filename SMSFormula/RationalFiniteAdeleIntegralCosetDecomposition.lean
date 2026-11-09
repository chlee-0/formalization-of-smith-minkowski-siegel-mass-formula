import SMSFormula.RationalAdeleFiniteLocalIntegralVanishing

/-!
# The finite adeles are the disjoint union of the integral cosets `r + Ẑ`, `r ∈ ℚ ∩ [0,1)`

Every finite adele differs from a rational number by an everywhere-integral finite adele (old
strong approximation `exists_rational_sub_mem_integralFiniteAdeleSubring`), and a rational number
is everywhere integral exactly when it is an integer (old
`rational_mem_integralFiniteAdeleSubring_iff`).  So the cosets `r + Ẑ` indexed by the canonical
fractional-part representatives `r = fract r` of `ℚ/ℤ` cover `𝔸_f` and are pairwise disjoint.
Each has volume one for the finite Haar measure (normalized by `vol(Ẑ) = 1`), so for every
`Ẑ`-periodic function

`∫_{𝔸_f} f = ∑_{r ∈ ℚ ∩ [0,1)} f(r)`

(Lebesgue form for nonnegative `f`; Bochner form for integrable `f`), and integrability forces
absolute summability of the representative values.

Applied to the finite quadratic Gauss integral `G` of an integral lattice (Ẑ-periodic, and
integrable in rank at least five) this gives `∑_r ‖G(r)‖ < ∞` and, at every integral frequency
`t`, the finite local Fourier integral as the absolutely convergent character sum
`∫ ψ_f(t y) G(y) dy = ∑_r e(t r)⁻¹ G(r)`.  The representatives are the canonical fractional
parts, so nothing is chosen.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

/-- The canonical fractional-part representatives of `ℚ/ℤ`. -/
abbrev RationalFractionalRep : Type := {r : ℚ // Int.fract r = r}

/-- The integral coset `r + Ẑ` of the finite adeles. -/
def rationalFiniteAdeleIntegralCoset (r : ℚ) : Set RationalFiniteAdele :=
  {y | y - algebraMap ℚ RationalFiniteAdele r ∈ integralFiniteAdeleSubring}

theorem rationalFiniteAdeleIntegralCoset_eq_preimage (r : ℚ) :
    rationalFiniteAdeleIntegralCoset r =
      (fun y ↦ -algebraMap ℚ RationalFiniteAdele r + y) ⁻¹'
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  ext y
  simp only [rationalFiniteAdeleIntegralCoset, Set.mem_setOf_eq, Set.mem_preimage,
    SetLike.mem_coe, neg_add_eq_sub]

theorem measurableSet_rationalFiniteAdeleIntegralCoset (r : ℚ) :
    MeasurableSet (rationalFiniteAdeleIntegralCoset r) := by
  rw [rationalFiniteAdeleIntegralCoset_eq_preimage]
  exact (isOpen_integralFiniteAdeleSubring.preimage
    (continuous_const.add continuous_id)).measurableSet

/-- Every integral coset has volume one. -/
@[simp]
theorem rationalFiniteAdeleAddHaarMeasure_integralCoset (r : ℚ) :
    rationalFiniteAdeleAddHaarMeasure (rationalFiniteAdeleIntegralCoset r) = 1 := by
  rw [rationalFiniteAdeleIntegralCoset_eq_preimage, measure_preimage_add]
  exact rationalFiniteAdeleAddHaarMeasure_integral

/-- An integer is an everywhere-integral finite adele. -/
theorem algebraMap_intCast_mem_integralFiniteAdeleSubring (k : ℤ) :
    algebraMap ℚ RationalFiniteAdele (k : ℚ) ∈ integralFiniteAdeleSubring :=
  (rational_mem_integralFiniteAdeleSubring_iff _).2 ⟨k, rfl⟩

/-- The integral cosets over the canonical representatives cover the finite adeles. -/
theorem exists_mem_rationalFiniteAdeleIntegralCoset (y : RationalFiniteAdele) :
    ∃ r : RationalFractionalRep, y ∈ rationalFiniteAdeleIntegralCoset r.1 := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring y
  refine ⟨⟨Int.fract q, Int.fract_fract q⟩, ?_⟩
  have hsplit : y - algebraMap ℚ RationalFiniteAdele (Int.fract q) =
      (y - algebraMap ℚ RationalFiniteAdele q) +
        algebraMap ℚ RationalFiniteAdele (⌊q⌋ : ℚ) := by
    rw [Int.fract, map_sub]
    ring
  change y - algebraMap ℚ RationalFiniteAdele (Int.fract q) ∈ integralFiniteAdeleSubring
  rw [hsplit]
  exact add_mem hq (algebraMap_intCast_mem_integralFiniteAdeleSubring _)

/-- The integral cosets over the canonical representatives are pairwise disjoint. -/
theorem eq_of_mem_rationalFiniteAdeleIntegralCoset {r s : RationalFractionalRep}
    {y : RationalFiniteAdele} (hr : y ∈ rationalFiniteAdeleIntegralCoset r.1)
    (hs : y ∈ rationalFiniteAdeleIntegralCoset s.1) : r = s := by
  have hdiff : algebraMap ℚ RationalFiniteAdele (s.1 - r.1) ∈ integralFiniteAdeleSubring := by
    have hEq : algebraMap ℚ RationalFiniteAdele (s.1 - r.1) =
        (y - algebraMap ℚ RationalFiniteAdele r.1) -
          (y - algebraMap ℚ RationalFiniteAdele s.1) := by
      rw [map_sub]
      ring
    rw [hEq]
    exact sub_mem hr hs
  obtain ⟨k, hk⟩ := (rational_mem_integralFiniteAdeleSubring_iff _).1 hdiff
  have hk' : s.1 = r.1 + (k : ℚ) := by
    have hcast : algebraMap ℤ ℚ k = (k : ℚ) := rfl
    rw [hcast] at hk
    linarith
  apply Subtype.ext
  calc r.1 = Int.fract r.1 := r.2.symm
    _ = Int.fract (r.1 + (k : ℚ)) := (Int.fract_add_intCast r.1 k).symm
    _ = Int.fract s.1 := by rw [hk']
    _ = s.1 := s.2

theorem iUnion_rationalFiniteAdeleIntegralCoset :
    (⋃ r : RationalFractionalRep, rationalFiniteAdeleIntegralCoset r.1) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ?_
  obtain ⟨r, hr⟩ := exists_mem_rationalFiniteAdeleIntegralCoset y
  exact Set.mem_iUnion.2 ⟨r, hr⟩

theorem pairwise_disjoint_rationalFiniteAdeleIntegralCoset :
    Pairwise (Function.onFun Disjoint fun r : RationalFractionalRep ↦
      rationalFiniteAdeleIntegralCoset r.1) := by
  intro r s hrs
  exact Set.disjoint_left.2 fun _ hr hs ↦ hrs (eq_of_mem_rationalFiniteAdeleIntegralCoset hr hs)

/-- A `Ẑ`-periodic function is constant on each integral coset. -/
theorem eq_of_mem_rationalFiniteAdeleIntegralCoset_of_periodic {E : Type*}
    (f : RationalFiniteAdele → E)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring → f (y + z) = f y) (r : ℚ)
    {y : RationalFiniteAdele} (hy : y ∈ rationalFiniteAdeleIntegralCoset r) :
    f y = f (algebraMap ℚ RationalFiniteAdele r) := by
  have h := hf (algebraMap ℚ RationalFiniteAdele r) _ hy
  rwa [show algebraMap ℚ RationalFiniteAdele r + (y - algebraMap ℚ RationalFiniteAdele r) = y by
    abel] at h

/-- The coset decomposition, Lebesgue form: for every `Ẑ`-periodic nonnegative function,
`∫⁻_{𝔸_f} f = ∑_{r ∈ ℚ ∩ [0,1)} f(r)`. -/
theorem lintegral_eq_tsum_of_integralPeriodic (f : RationalFiniteAdele → ENNReal)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring → f (y + z) = f y) :
    ∫⁻ y, f y ∂rationalFiniteAdeleAddHaarMeasure =
      ∑' r : RationalFractionalRep, f (algebraMap ℚ RationalFiniteAdele r.1) := by
  have hU := lintegral_iUnion (μ := rationalFiniteAdeleAddHaarMeasure)
    (s := fun r : RationalFractionalRep ↦ rationalFiniteAdeleIntegralCoset r.1)
    (fun r ↦ measurableSet_rationalFiniteAdeleIntegralCoset r.1)
    pairwise_disjoint_rationalFiniteAdeleIntegralCoset f
  rw [iUnion_rationalFiniteAdeleIntegralCoset, setLIntegral_univ] at hU
  rw [hU]
  refine tsum_congr fun r ↦ ?_
  rw [setLIntegral_congr_fun (measurableSet_rationalFiniteAdeleIntegralCoset r.1)
      (fun y hy ↦ eq_of_mem_rationalFiniteAdeleIntegralCoset_of_periodic f hf r.1 hy),
    setLIntegral_const, rationalFiniteAdeleAddHaarMeasure_integralCoset, mul_one]

/-- The coset decomposition, Bochner form: for every integrable `Ẑ`-periodic function,
`∫_{𝔸_f} f = ∑_{r ∈ ℚ ∩ [0,1)} f(r)`. -/
theorem integral_eq_tsum_of_integralPeriodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : RationalFiniteAdele → E)
    (hint : Integrable f rationalFiniteAdeleAddHaarMeasure)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring → f (y + z) = f y) :
    ∫ y, f y ∂rationalFiniteAdeleAddHaarMeasure =
      ∑' r : RationalFractionalRep, f (algebraMap ℚ RationalFiniteAdele r.1) := by
  have hU := integral_iUnion (μ := rationalFiniteAdeleAddHaarMeasure) (f := f)
    (s := fun r : RationalFractionalRep ↦ rationalFiniteAdeleIntegralCoset r.1)
    (fun r ↦ measurableSet_rationalFiniteAdeleIntegralCoset r.1)
    pairwise_disjoint_rationalFiniteAdeleIntegralCoset hint.integrableOn
  rw [iUnion_rationalFiniteAdeleIntegralCoset, setIntegral_univ] at hU
  rw [hU]
  refine tsum_congr fun r ↦ ?_
  rw [setIntegral_congr_fun (measurableSet_rationalFiniteAdeleIntegralCoset r.1)
      (fun y hy ↦ eq_of_mem_rationalFiniteAdeleIntegralCoset_of_periodic f hf r.1 hy),
    setIntegral_const, Measure.real, rationalFiniteAdeleAddHaarMeasure_integralCoset,
    ENNReal.toReal_one, one_smul]

/-- An integrable `Ẑ`-periodic function has absolutely summable representative values. -/
theorem summable_norm_of_integralPeriodic {E : Type*} [NormedAddCommGroup E]
    (f : RationalFiniteAdele → E) (hint : Integrable f rationalFiniteAdeleAddHaarMeasure)
    (hf : ∀ y z, z ∈ integralFiniteAdeleSubring → f (y + z) = f y) :
    Summable fun r : RationalFractionalRep ↦ ‖f (algebraMap ℚ RationalFiniteAdele r.1)‖ := by
  have hsum := lintegral_eq_tsum_of_integralPeriodic (fun y ↦ ‖f y‖ₑ)
    (fun y z hz ↦ by simp only [hf y z hz])
  have hfin : ∫⁻ y, ‖f y‖ₑ ∂rationalFiniteAdeleAddHaarMeasure < ⊤ := hint.hasFiniteIntegral
  rw [hsum] at hfin
  have hne : (∑' r : RationalFractionalRep,
      ((‖f (algebraMap ℚ RationalFiniteAdele r.1)‖₊ : NNReal) : ENNReal)) ≠ ⊤ := by
    simpa only [enorm] using hfin.ne
  simpa using ENNReal.tsum_coe_ne_top_iff_summable_coe.1 hne

/-! ## The finite quadratic Gauss integral -/

variable {n : ℕ}

/-- The finite Gauss integral has absolutely summable values on `ℚ/ℤ` in rank at least five. -/
theorem summable_norm_finiteGaussIntegral_fractionalRep (L : PositiveDefiniteIntegralLattice n)
    (hrank : 5 ≤ n) :
    Summable fun r : RationalFractionalRep ↦
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1‖ :=
  summable_norm_of_integralPeriodic _ (L.integrable_finiteGaussIntegral one_pos hrank)
    (fun y z hz ↦
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
        L y z hz)

/-- At an integral frequency the finite local integrand is `Ẑ`-periodic. -/
theorem finiteLocalIntegrand_add_integral (L : PositiveDefiniteIntegralLattice n) {t : ℚ}
    (ht : t ∈ (algebraMap ℤ ℚ).range) (y z : RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleSubring) :
    ((rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele t * (y + z)) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt (y + z) =
      ((rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y := by
  have htz : algebraMap ℚ RationalFiniteAdele t * z ∈ integralFiniteAdeleSubring :=
    Subring.mul_mem _ ((rational_mem_integralFiniteAdeleSubring_iff t).2 ht) hz
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
      L y z hz, mul_add, AddChar.map_add_eq_mul,
    rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ htz, mul_one]

/-- The finite Fourier coefficient as a character sum: at every integral frequency `t`,
`∫_{𝔸_f} ψ_f(t y) G(y) dy = ∑_{r ∈ ℚ ∩ [0,1)} e(t r)⁻¹ G(r)` (rank at least five). -/
theorem integral_finiteLocal_eq_tsum_of_int (L : PositiveDefiniteIntegralLattice n) (hrank : 5 ≤ n) {t : ℚ}
    (ht : t ∈ (algebraMap ℤ ℚ).range) :
    (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) =
      ∑' r : RationalFractionalRep,
        (((Real.fourierChar ((t * r.1 : ℚ) : ℝ))⁻¹ : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1 := by
  have hint := L.integrable_finiteLocalIntegrand one_pos hrank (-t)
  rw [neg_neg] at hint
  rw [integral_eq_tsum_of_integralPeriodic _ hint
    (fun y z hz ↦ L.finiteLocalIntegrand_add_integral ht y z hz)]
  refine tsum_congr fun r ↦ ?_
  rw [← map_mul, rationalFiniteAdeleFourierChar_algebraMap,
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_rationalDiagonal]

end PositiveDefiniteIntegralLattice
