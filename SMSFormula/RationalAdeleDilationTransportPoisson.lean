import SMSFormula.RationalAdeleSubgroupCarrierPoisson

/-!
# The dilation transport: Poisson for a carrier sandwiched between `N Zhat^n` and `N^-1 Zhat^n`

Poisson summation is known for the Gaussian times the indicator of a subgroup carrier inside the
integral vectors.  The carrier of the translated test is only sandwiched between `N Zhat^n` and
`N^-1 Zhat^n`, so it must first be brought inside.

The transport is a reindexing of the rational-diagonal sum, not an operator identity: scaling a
rational coordinate vector by a nonzero natural is a bijection of the index set, so no `m^N` factor
appears on the theta side.  What changes is the width, from `b` to `b / N^2`, and the level, from
`N` to `N * N`.  Both are kept explicit.

Scope: no covariance of either functional follows, and the Weyl/dual side is not rewritten back to
the original width `b` here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Scaling a rational coordinate vector by a nonzero natural is a bijection of the index set. -/
def rationalScaleEquiv (n : ℕ) {N : ℕ} (hN : N ≠ 0) : (Fin n → ℚ) ≃ (Fin n → ℚ) where
  toFun q := fun i ↦ (N : ℚ) * q i
  invFun p := fun i ↦ p i / (N : ℚ)
  left_inv q := by
    funext i
    field_simp
  right_inv p := by
    funext i
    field_simp

theorem tsum_polarGaussian_indicator_scale (L : PositiveDefiniteIntegralLattice n) (b : ℂ) {N : ℕ} (hN : N ≠ 0)
    {K K' : Set (Fin n → RationalFiniteAdele)}
    (hKK' : ∀ y : Fin n → RationalFiniteAdele,
      y ∈ K ↔ (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ K') :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' p : Fin n → ℚ,
        polarRealGaussian L (b / ((N : ℝ) : ℂ) ^ 2) (rationalRealVector n p) *
          K'.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
            (rationalFiniteAdeleVectorDiagonal n p) := by
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [← (rationalScaleEquiv n hN).tsum_eq
    (fun p : Fin n → ℚ ↦ polarRealGaussian L (b / ((N : ℝ) : ℂ) ^ 2) (rationalRealVector n p) *
      K'.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
        (rationalFiniteAdeleVectorDiagonal n p))]
  refine tsum_congr fun q ↦ ?_
  have hreal : polarRealGaussian L (b / ((N : ℝ) : ℂ) ^ 2)
      (rationalRealVector n (rationalScaleEquiv n hN q)) =
      polarRealGaussian L b (rationalRealVector n q) := by
    rw [← polarRealGaussian_div L b hNR]
    congr 1
    funext i
    show ((((N : ℚ) * q i : ℚ) : ℝ)) / ((N : ℝ)) = (((q i : ℚ) : ℝ))
    push_cast
    field_simp
  have hfin : rationalFiniteAdeleVectorDiagonal n (rationalScaleEquiv n hN q) =
      fun i ↦ (N : RationalFiniteAdele) * rationalFiniteAdeleVectorDiagonal n q i := by
    funext i
    show algebraMap ℚ RationalFiniteAdele ((N : ℚ) * q i) = _
    rw [map_mul, map_natCast]
    rfl
  rw [hreal, hfin]
  by_cases h : rationalFiniteAdeleVectorDiagonal n q ∈ K
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem ((hKK' _).mp h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hm ↦ h ((hKK' _).mpr hm))]

/-! ## The scaled carrier -/

/-- Multiplication by a nonzero natural is injective on finite adeles, because that natural is a
unit there. -/
theorem natCast_mul_left_injective {N : ℕ} (hN : N ≠ 0) :
    Function.Injective (fun a : RationalFiniteAdele ↦ (N : RationalFiniteAdele) * a) := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hinv : algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * (N : RationalFiniteAdele) = 1 := by
    rw [show (N : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((N : ℚ)) from
      (map_natCast (algebraMap ℚ RationalFiniteAdele) N).symm, ← map_mul,
      inv_mul_cancel₀ hNQ, map_one]
  intro a c hac
  have := congrArg (fun z ↦ algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * z) hac
  simpa only [← mul_assoc, hinv, one_mul] using this

/-- The carrier scaled by `N`.  It is derived from `K`, not chosen. -/
def scaledCarrier (N : ℕ) (K : Set (Fin n → RationalFiniteAdele)) :
    Set (Fin n → RationalFiniteAdele) :=
  (fun z : Fin n → RationalFiniteAdele ↦ fun i ↦ (N : RationalFiniteAdele) * z i) '' K

theorem mem_scaledCarrier_iff {N : ℕ} (hN : N ≠ 0) {K : Set (Fin n → RationalFiniteAdele)}
    (y : Fin n → RationalFiniteAdele) :
    y ∈ K ↔ (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ scaledCarrier N K := by
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hzy : z = y := by
      funext i
      exact natCast_mul_left_injective hN (congrFun heq i)
    rwa [hzy] at hz

theorem scaledCarrier_subset {N : ℕ} {K : Set (Fin n → RationalFiniteAdele)}
    (hhigh : ∀ y ∈ K, (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ integralFiniteAdeleVectors n) :
    scaledCarrier N K ⊆ integralFiniteAdeleVectors n := by
  rintro _ ⟨z, hz, rfl⟩
  exact hhigh z hz

theorem add_mem_scaledCarrier {N : ℕ} {K : Set (Fin n → RationalFiniteAdele)}
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    {x y : Fin n → RationalFiniteAdele} (hx : x ∈ scaledCarrier N K)
    (hy : y ∈ scaledCarrier N K) : x + y ∈ scaledCarrier N K := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨z + w, hadd hz hw, ?_⟩
  funext i
  show (N : RationalFiniteAdele) * (z i + w i) = _
  show (N : RationalFiniteAdele) * (z i + w i) =
    (N : RationalFiniteAdele) * z i + (N : RationalFiniteAdele) * w i
  ring

theorem neg_mem_scaledCarrier {N : ℕ} {K : Set (Fin n → RationalFiniteAdele)}
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ scaledCarrier N K) :
    -x ∈ scaledCarrier N K := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨-z, hneg hz, ?_⟩
  funext i
  show (N : RationalFiniteAdele) * (-z i) = -((N : RationalFiniteAdele) * z i)
  ring

theorem nsmul_mem_scaledCarrier {N : ℕ} {K : Set (Fin n → RationalFiniteAdele)}
    (hlow : ∀ u ∈ integralFiniteAdeleVectors n,
      (fun i ↦ (N : RationalFiniteAdele) * u i) ∈ K)
    (u : Fin n → RationalFiniteAdele) (hu : u ∈ integralFiniteAdeleVectors n) :
    ((N * N) • u : Fin n → RationalFiniteAdele) ∈ scaledCarrier N K := by
  refine ⟨fun i ↦ (N : RationalFiniteAdele) * u i, hlow u hu, ?_⟩
  funext i
  show (N : RationalFiniteAdele) * ((N : RationalFiniteAdele) * u i) = ((N * N : ℕ)) • u i
  rw [nsmul_eq_mul]
  push_cast
  ring

/-! ## The transported Poisson identity -/

/-- Poisson for the polar Gaussian times the indicator of a subgroup carrier sandwiched between
`N Zhat^n` and `N^-1 Zhat^n` -- the shape the translated test actually has.  The width moves from
`b` to `b / N^2` and the level from `N` to `N * N`; no `m^N` factor appears on the theta side,
because the transport is a reindexing by a bijection of the rational index set. -/
theorem tsum_polarGaussian_wideSandwichCarrier_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero (N * N)]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hlow : ∀ u ∈ integralFiniteAdeleVectors n,
      (fun i ↦ (N : RationalFiniteAdele) * u i) ∈ K)
    (hhigh : ∀ y ∈ K, (fun i ↦ (N : RationalFiniteAdele) * y i) ∈
      integralFiniteAdeleVectors n) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' p : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume
            (polarRealGaussian L (b / ((N : ℝ) : ℂ) ^ 2)) (rationalRealVector n p) *
          ∑ alpha,
            standardFamilyQuotientLift
                ((scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
                (isStandardPeriodic_indicator (add_mem_scaledCarrier hadd)
                  (neg_mem_scaledCarrier hneg) (nsmul_mem_scaledCarrier hlow)) alpha *
              standardFiniteFourier (standardCosetIndicator n (N * N) alpha)
                (rationalFiniteAdeleVectorDiagonal n p) := by
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hb' : 0 < (b / ((N : ℝ) : ℂ) ^ 2).re := by
    have hsq : (((N : ℝ) : ℂ)) ^ 2 = (((N : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hpos : (0 : ℝ) < ((N : ℝ)) ^ 2 := by positivity
    rw [hsq, Complex.div_ofReal_re]
    exact div_pos hb hpos
  rw [tsum_polarGaussian_indicator_scale L b hN (mem_scaledCarrier_iff hN)]
  exact tsum_polarGaussian_subgroupIndicator_poisson L hb' (Nat.mul_ne_zero hN hN)
    (scaledCarrier_subset hhigh) (add_mem_scaledCarrier hadd) (neg_mem_scaledCarrier hneg)
    (nsmul_mem_scaledCarrier hlow)

end RationalQuadraticSpaceMatrix

end
