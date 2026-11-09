import SMSFormula.FiniteFactorIdentification
import SMSFormula.FiniteConductorSummability

/-!
# The finite-adelic `L^1` estimate, assembled

The three measure-theoretic items are closed separately; this file composes them into the single
estimate the finite half of `G_b subset L` asks for: the adelic Bruhat coefficient's finite factor is
integrable over the finite adeles above rank four.

The assembly is the conductor partition.  Every frequency has an exact conductor and it is unique,
so the finite adeles are the disjoint union of the exact-conductor strata; each stratum is a finite
union of classes hence measurable; the integral therefore splits as a sum over conductors, and
mathlib's `lintegral_iUnion` asks only that the sets be measurable -- no measurability of the
integrand is needed anywhere, which is what makes the split free.

On each stratum the integrand is bounded by a constant: exactness of the conductor is injectivity of
the residue character, so the conductor bound applies at every point of the stratum with the same
right side, `(m^n)^(-1/2) |polarDeterminant L|^(n/2)`.  The stratum's mass is `phi(m)`.  So the `m`-th term is at
most `phi(m)` times that constant -- exactly the shape `FiniteConductorSummability` consumes, which
converges above rank four.

Negative scope.  This is the finite factor only.  No archimedean factor is bounded, no Gauss sum is
evaluated, and the estimate is an integrability statement, not an evaluation: nothing computes the
integral or bounds it below.  The integral model is carried as a hypothesis, since a general
rational quadratic space's form matrix need not be the diagonal image of an integer matrix.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix
  RationalQuadraticSpaceMatrix
open scoped ENNReal

variable {n : ℕ}

/-! ## The strata are measurable and partition the finite adeles -/

/-- Each stratum is measurable, being a finite union of classes. -/
theorem measurableSet_exactConductor (m : ℕ) [NeZero m] :
    MeasurableSet {t : RationalFiniteAdele |
      t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧ HasExactConductor t m} := by
  rw [exactConductor_eq_iUnion m]
  exact MeasurableSet.iUnion fun _ ↦ measurableSet_congruenceClass _

/-- The strata at distinct nonzero conductors are disjoint, by uniqueness of the exact
conductor. -/
theorem pairwiseDisjoint_exactConductor :
    Pairwise (Function.onFun Disjoint (fun k : ℕ =>
      {t : RationalFiniteAdele |
        t * ((k + 1 : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
          HasExactConductor t (k + 1)})) := by
  intro k l hkl
  refine Set.disjoint_left.2 fun t ht ht' ↦ hkl ?_
  have := hasExactConductor_unique (m := k + 1) (m' := l + 1) (by omega) (by omega)
    ht.2 ht'.2 ht.1 ht'.1
  omega

/-- And they cover: every frequency has an exact conductor. -/
theorem iUnion_exactConductor_eq_univ :
    (⋃ k : ℕ, {t : RationalFiniteAdele |
        t * ((k + 1 : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
          HasExactConductor t (k + 1)}) = Set.univ := by
  refine Set.eq_univ_of_forall fun t ↦ ?_
  obtain ⟨m, hm, hc, hex⟩ := exists_hasExactConductor t
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  exact Set.mem_iUnion.2 ⟨k, hc, hex⟩

/-! ## The uniform bound on a stratum -/

/-- On the exact-conductor-`m` stratum the finite factor is bounded by a constant: exactness is
injectivity, so the conductor bound applies at every point with the same right side. -/
theorem norm_gaussIntegralAt_le_of_hasExactConductor (L : PositiveDefiniteIntegralLattice n)
    (V : RationalQuadraticSpaceMatrix n)
    (hV : V.finiteAdelicFormMatrix = integralModelMatrix L.pairingMatrix)
    (m : ℕ) [NeZero m] {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hex : HasExactConductor t m) :
    ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖ ≤
      Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n) := by
  have hsq : ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n := by
    rw [gaussIntegralAt_eq_localIntegral, hV]
    exact norm_sq_integral_scaledPhase_le L m htm
      ((hasExactConductor_iff_injective m (NeZero.ne m) htm).1 hex)
  calc ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
      = Real.sqrt (‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-! ## The summable majorant -/

/-- The majorant is summable above rank four -- `FiniteConductorSummability` at the explicit
family. -/
theorem summable_totient_mul_sqrt (d : ℕ) (hn : 4 < n) :
    Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) *
      Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * ((d : ℝ)) ^ n)) := by
  have hkey := summable_totient_mul_norm_of_det_bound hn d
    (fun m : ℕ ↦ ((Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * ((d : ℝ)) ^ n) : ℝ) : ℂ)) ?_
  · refine hkey.congr fun m ↦ ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  · intro q _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity)]

/-! ## The estimate -/

/-- The finite-adelic `L^1` estimate: the adelic Bruhat coefficient's finite factor is integrable
over the finite adeles above rank four -- the conductor partition, the uniform bound on each
stratum, the stratum mass `phi(m)`, and the conductor summability, composed. -/
theorem lintegral_norm_gaussIntegralAt_lt_top (L : PositiveDefiniteIntegralLattice n)
    (V : RationalQuadraticSpaceMatrix n)
    (hV : V.finiteAdelicFormMatrix = integralModelMatrix L.pairingMatrix) (hn : 4 < n) :
    ∫⁻ t, ENNReal.ofReal ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
        ∂rationalFiniteAdeleAddHaarMeasure < ⊤ := by
  set D : ℝ := (L.polarDeterminant.natAbs : ℝ) with hD
  set B : ℕ → ℝ := fun m ↦ Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * D ^ n) with hB
  set S : ℕ → Set RationalFiniteAdele := fun k ↦
    {t : RationalFiniteAdele |
      t * ((k + 1 : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
        HasExactConductor t (k + 1)} with hS
  have hmeas : ∀ k : ℕ, MeasurableSet (S k) := fun k ↦ by
    haveI : NeZero (k + 1) := ⟨by omega⟩
    exact measurableSet_exactConductor (k + 1)
  have hsplit : ∫⁻ t, ENNReal.ofReal ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
        ∂rationalFiniteAdeleAddHaarMeasure =
      ∑' k : ℕ, ∫⁻ t in S k, ENNReal.ofReal
        ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
        ∂rationalFiniteAdeleAddHaarMeasure := by
    rw [← setLIntegral_univ, ← iUnion_exactConductor_eq_univ,
      lintegral_iUnion hmeas pairwiseDisjoint_exactConductor]
  have hterm : ∀ k : ℕ, (∫⁻ t in S k, ENNReal.ofReal
      ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
      ∂rationalFiniteAdeleAddHaarMeasure) ≤
      ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) := by
    intro k
    haveI : NeZero (k + 1) := ⟨by omega⟩
    calc (∫⁻ t in S k, ENNReal.ofReal
          ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
          ∂rationalFiniteAdeleAddHaarMeasure)
        ≤ ∫⁻ _ in S k, ENNReal.ofReal (B (k + 1))
          ∂rationalFiniteAdeleAddHaarMeasure := by
          refine setLIntegral_mono_ae' (hmeas k) ?_
          filter_upwards with t ht
          exact ENNReal.ofReal_le_ofReal
            (norm_gaussIntegralAt_le_of_hasExactConductor L V hV (k + 1) ht.1 ht.2)
      _ = ENNReal.ofReal (B (k + 1)) *
          rationalFiniteAdeleAddHaarMeasure (S k) := setLIntegral_const _ _
      _ = ENNReal.ofReal (B (k + 1)) * (Nat.totient (k + 1) : ℝ≥0∞) := by
          rw [hS, measure_exactConductor_eq_totient (k + 1)]
      _ = ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
  have hsummable : Summable (fun k : ℕ ↦ (Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_totient_mul_sqrt L.polarDeterminant.natAbs hn)
  have hnonneg : ∀ k : ℕ, 0 ≤ (Nat.totient (k + 1) : ℝ) * B (k + 1) := fun k ↦ by
    positivity
  calc ∫⁻ t, ENNReal.ofReal ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
        ∂rationalFiniteAdeleAddHaarMeasure
      = ∑' k : ℕ, ∫⁻ t in S k, ENNReal.ofReal
          ‖V.rationalFiniteAdeleQuadraticGaussIntegralAt t‖
          ∂rationalFiniteAdeleAddHaarMeasure := hsplit
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k : ℕ, (Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
