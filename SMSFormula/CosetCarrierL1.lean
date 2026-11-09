import SMSFormula.ShiftedCarrierLocalBound
import SMSFormula.FiniteAdelicL1Assembly
import SMSFormula.RationalFiniteAdeleStandardFamilySpanning

/-!
# The finite half of `G_b subset L` for every carrier inside the integral vectors

The per-coset bound is proved elsewhere, as is the decomposition of a standard-carried,
standard-periodic finite test into a finite sum of coset indicators, with no representative chosen.
This file sums the per-coset bounds.

The summation costs nothing beyond a constant, and that is the point.  The per-coset bound is
`(m^n)^(-1/2)` times a number depending only on the scale, the rank and the discriminant, and the
conductor `m` is the same for every coset because the coset substitution leaves the frequency
untouched.  So the triangle inequality over the finitely many cosets multiplies the constant by the
sum of the coefficient moduli and changes nothing else; the conductor partition then runs once, on
the whole finite factor.

The partition argument is extracted, not repeated: `lintegral_lt_top_of_conductor_bound` takes any
function bounded on each exact-conductor stratum by a constant times `(m^n)^(-1/2) d^(n/2)` and
concludes integrability above rank four.  The main result of `FiniteAdelicL1Assembly` is the case `K = 1`.
Nothing here needs measurability of the integrand in the frequency: `lintegral_iUnion` asks only
that the strata be measurable.

The interchange is the one place measure theory in `x` enters.  Passing the finite sum through the
ambient integral needs each coset term integrable, which it is: the coset sits inside the integral
vectors, a set of mass one, and the phase has modulus one, so the term is dominated by an indicator
of finite mass.

Negative scope.  The carrier must lie inside the integral vectors -- standard-carried at scale one.
A general compact open carrier has a bounded denominator and is brought inside only by a dilation,
which moves the frequency, and that transport is not performed here.  The estimate stays an upper
bound, the integral model stays a hypothesis, and nothing evaluates a Gauss sum.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory Matrix RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The conductor partition, extracted -/

open scoped ENNReal in
/-- The partition argument, once and for all: a function bounded on each exact-conductor stratum by
a constant times `(m^n)^(-1/2) d^(n/2)` is integrable over the finite adeles above rank four.  No
measurability of the function is used -- `lintegral_iUnion` asks only that the strata be
measurable. -/
theorem lintegral_lt_top_of_conductor_bound (hn : 4 < n) (d : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (F : RationalFiniteAdele → ℂ)
    (hF : ∀ m : ℕ, ∀ _ : NeZero m, ∀ t : RationalFiniteAdele,
      t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring → HasExactConductor t m →
        ‖F t‖ ≤ K * Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * ((d : ℝ)) ^ n)) :
    ∫⁻ t, ENNReal.ofReal ‖F t‖ ∂rationalFiniteAdeleAddHaarMeasure < ⊤ := by
  set B : ℕ → ℝ := fun m ↦ K * Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * ((d : ℝ)) ^ n) with hB
  set S : ℕ → Set RationalFiniteAdele := fun k ↦
    {t : RationalFiniteAdele |
      t * ((k + 1 : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
        HasExactConductor t (k + 1)} with hS
  have hmeas : ∀ k : ℕ, MeasurableSet (S k) := fun k ↦ by
    haveI : NeZero (k + 1) := ⟨by omega⟩
    exact measurableSet_exactConductor (k + 1)
  have hsplit : ∫⁻ t, ENNReal.ofReal ‖F t‖ ∂rationalFiniteAdeleAddHaarMeasure =
      ∑' k : ℕ, ∫⁻ t in S k, ENNReal.ofReal ‖F t‖ ∂rationalFiniteAdeleAddHaarMeasure := by
    rw [← setLIntegral_univ, ← iUnion_exactConductor_eq_univ,
      lintegral_iUnion hmeas pairwiseDisjoint_exactConductor]
  have hterm : ∀ k : ℕ, (∫⁻ t in S k, ENNReal.ofReal ‖F t‖
      ∂rationalFiniteAdeleAddHaarMeasure) ≤
      ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) := by
    intro k
    haveI : NeZero (k + 1) := ⟨by omega⟩
    calc (∫⁻ t in S k, ENNReal.ofReal ‖F t‖ ∂rationalFiniteAdeleAddHaarMeasure)
        ≤ ∫⁻ _ in S k, ENNReal.ofReal (B (k + 1))
          ∂rationalFiniteAdeleAddHaarMeasure := by
          refine setLIntegral_mono_ae' (hmeas k) ?_
          filter_upwards with t ht
          exact ENNReal.ofReal_le_ofReal (hF (k + 1) inferInstance t ht.1 ht.2)
      _ = ENNReal.ofReal (B (k + 1)) *
          rationalFiniteAdeleAddHaarMeasure (S k) := setLIntegral_const _ _
      _ = ENNReal.ofReal (B (k + 1)) * (Nat.totient (k + 1) : ℝ≥0∞) := by
          rw [hS, measure_exactConductor_eq_totient (k + 1)]
      _ = ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
  have hbase : Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) * B m) := by
    have := (summable_totient_mul_sqrt (n := n) d hn).mul_left K
    refine this.congr fun m ↦ ?_
    rw [hB]
    ring
  have hsummable : Summable (fun k : ℕ ↦ (Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
    (summable_nat_add_iff 1).2 hbase
  have hnonneg : ∀ k : ℕ, 0 ≤ (Nat.totient (k + 1) : ℝ) * B (k + 1) := fun k ↦ by
    have : 0 ≤ B (k + 1) := by
      rw [hB]
      exact mul_nonneg hK (Real.sqrt_nonneg _)
    positivity
  calc ∫⁻ t, ENNReal.ofReal ‖F t‖ ∂rationalFiniteAdeleAddHaarMeasure
      = ∑' k : ℕ, ∫⁻ t in S k, ENNReal.ofReal ‖F t‖
          ∂rationalFiniteAdeleAddHaarMeasure := hsplit
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k : ℕ, (Nat.totient (k + 1) : ℝ) * B (k + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## The repository's coset indicator is ours -/

/-- The coset set Lies inside the integral vectors, by its own definition as an image of them. -/
theorem standardCosetSet_subset_integral (r : ℕ)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range) :
    standardCosetSet n r alpha ⊆ integralFiniteAdeleVectors n := by
  rintro x ⟨y, _, rfl⟩
  exact fun i ↦ (y i).property

/-- The repository's coset indicator is the one the shifted-carrier bound uses, at the class's own
representative -- so no representative is chosen in any statement. -/
theorem standardCosetIndicator_eq_cosetIndicator {r : ℕ} (hr : r ≠ 0)
    (y : Fin n → IntegralFiniteAdele) :
    standardCosetIndicator n r (QuotientAddGroup.mk y) = cosetIndicator (coordCoe y) r := by
  funext x
  have hiff : x ∈ standardCosetSet n r (QuotientAddGroup.mk y) ↔
      rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - coordCoe y) ∈
        integralFiniteAdeleVectors n := by
    rw [mem_standardCosetSet_iff_sub_mem, standardDilatedLattice_eq_preimage hr]
    rfl
  by_cases hx : x ∈ standardCosetSet n r (QuotientAddGroup.mk y)
  · rw [standardCosetIndicator, Set.indicator_of_mem hx, cosetIndicator,
      rationalFiniteAdeleVectorIntegralIndicator_of_mem (hiff.1 hx)]
    rfl
  · rw [standardCosetIndicator, Set.indicator_of_notMem hx, cosetIndicator,
      rationalFiniteAdeleVectorIntegralIndicator_of_not_mem (fun h ↦ hx (hiff.2 h))]

/-! ## Measurability and integrability of one coset term -/

/-- The quadratic phase is measurable. -/
theorem measurable_dotQuadraticPhase (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (t : RationalFiniteAdele) :
    Measurable (fun x : Fin n → RationalFiniteAdele ↦
      complexFiniteChar (t * dotQuadratic C x)) := by
  have hc : Continuous (fun x : Fin n → RationalFiniteAdele ↦
      rationalFiniteAdeleFourierChar (t * dotQuadratic C x)) := by
    apply continuous_rationalFiniteAdeleFourierChar.comp
    unfold dotQuadratic Matrix.mulVec dotProduct
    fun_prop
  exact hc.subtype_val.measurable

/-- The integral vectors have mass one, coordinatewise from the repository's own normalisation. -/
theorem measure_integralFiniteAdeleVectors (n : ℕ) :
    rationalFiniteAdeleCoordinateAddHaarMeasure n (integralFiniteAdeleVectors n) = 1 := by
  rw [show integralFiniteAdeleVectors n =
      Set.univ.pi fun _ : Fin n ↦ (integralFiniteAdeleSubring : Set RationalFiniteAdele) from by
    ext x; simp [integralFiniteAdeleVectors, Set.mem_pi]]
  rw [rationalFiniteAdeleCoordinateAddHaarMeasure, Measure.pi_pi]
  simp [rationalFiniteAdeleAddHaarMeasure_integral]

/-- The coset set is measurable. -/
theorem measurableSet_standardCosetSet {r : ℕ} (hr : r ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range) :
    MeasurableSet (standardCosetSet n r alpha) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective alpha
  have hset : standardCosetSet n r (QuotientAddGroup.mk y) =
      (fun x : Fin n → RationalFiniteAdele ↦
        rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - coordCoe y)) ⁻¹'
          integralFiniteAdeleVectors n := by
    ext x
    rw [mem_standardCosetSet_iff_sub_mem, standardDilatedLattice_eq_preimage hr]
    rfl
  rw [hset]
  refine (measurableSet_integralFiniteAdeleVectors n).preimage ?_
  exact ((continuous_rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹).comp
    (continuous_id.sub continuous_const)).measurable

/-- One coset term is integrable: the coset sits inside the integral vectors, of mass one, and the
phase has modulus one. -/
theorem integrable_standardCoset_phase {r : ℕ} (hr : r ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (t : RationalFiniteAdele) :
    Integrable (fun x ↦ standardCosetIndicator n r alpha x *
        complexFiniteChar (t * dotQuadratic C x))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hSmeas := measurableSet_standardCosetSet hr alpha
  have hVmeas := measurableSet_integralFiniteAdeleVectors n
  have hmass : rationalFiniteAdeleCoordinateAddHaarMeasure n (integralFiniteAdeleVectors n) ≠ ⊤ := by
    rw [measure_integralFiniteAdeleVectors n]
    exact ENNReal.one_ne_top
  have hgint : Integrable
      ((integralFiniteAdeleVectors n).indicator (fun _ ↦ (1 : ℝ)))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    (integrable_indicator_iff hVmeas).2 (integrableOn_const hmass)
  refine hgint.mono' ?_ ?_
  · refine (Measurable.mul ?_ (measurable_dotQuadraticPhase C t)).aestronglyMeasurable
    exact measurable_const.indicator hSmeas
  · filter_upwards with x
    have hchar : ‖complexFiniteChar (t * dotQuadratic C x)‖ = 1 := by
      rw [complexFiniteChar_apply]
      exact Circle.norm_coe _
    rw [norm_mul, hchar, mul_one]
    by_cases hx : x ∈ standardCosetSet n r alpha
    · rw [standardCosetIndicator, Set.indicator_of_mem hx,
        Set.indicator_of_mem (standardCosetSet_subset_integral r alpha hx)]
      simp
    · rw [standardCosetIndicator, Set.indicator_of_notMem hx, norm_zero]
      exact Set.indicator_apply_nonneg fun _ ↦ zero_le_one

/-! ## The per-coset bound, indexed by the class -/

/-- The per-coset bound, at the class rather than a representative: the bound does not see the
representative, so nothing is chosen. -/
theorem norm_integral_standardCoset_phase_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    {r : ℕ} (hr : r ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, standardCosetIndicator n r alpha x *
        complexFiniteChar (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖ ≤
      ((r : ℝ))⁻¹ ^ n *
        Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective alpha
  rw [standardCosetIndicator_eq_cosetIndicator hr y]
  refine norm_integral_cosetPhase_le L m hr (coordCoe y) (fun j ↦ ?_) htm hinj
  exact Subring.mul_mem _ (natCast_mem _ r) (y j).property

/-! ## The payoff -/

/-- The per-stratum bound, exposed on its own so a transport can reuse it: at a frequency of exact
conductor `m` the finite factor is at most a constant times `(m^n)^(-1/2)`, the constant depending
only on the coefficients, the level, the rank and the discriminant. -/
theorem norm_finiteFactor_le (L : PositiveDefiniteIntegralLattice n)
    {r : ℕ} [NeZero r] {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic r g)
    (m : ℕ) [NeZero m] {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hex : HasExactConductor t m) :
    ‖∫ x, g x * complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
      ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖ ≤
      ((∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖) * ((r : ℝ))⁻¹ ^ n) *
        Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
          (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by
  have hr : r ≠ 0 := NeZero.ne r
  set K : ℝ := (∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖) * ((r : ℝ))⁻¹ ^ n
    with hK
  have hinj := (hasExactConductor_iff_injective m (NeZero.ne m) htm).1 hex
  have hg : ∀ x, g x =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        standardCosetIndicator n r alpha x := by
    intro x
    conv_lhs => rw [standardScaleOne_eq_sum_cosetIndicator hcarried hperiodic]
  have hsum : ∀ x, g x * complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x) =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        (standardCosetIndicator n r alpha x * complexFiniteChar
          (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)) := by
    intro x
    rw [hg x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun alpha _ ↦ by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsum),
    integral_finset_sum _ (fun alpha _ ↦
      ((integrable_standardCoset_phase hr alpha
        (integralModelMatrix L.pairingMatrix) t).const_mul _))]
  simp only [MeasureTheory.integral_const_mul]
  calc ‖∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        ∫ x, standardCosetIndicator n r alpha x * complexFiniteChar
          (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖
      ≤ ∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha *
          ∫ x, standardCosetIndicator n r alpha x * complexFiniteChar
            (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
            ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖ := norm_sum_le _ _
    _ = ∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖ *
          ‖∫ x, standardCosetIndicator n r alpha x * complexFiniteChar
            (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
            ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖ := by
        simp only [norm_mul]
    _ ≤ ∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖ *
          (((r : ℝ))⁻¹ ^ n *
            Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
              (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n)) :=
        Finset.sum_le_sum fun alpha _ ↦
          mul_le_mul_of_nonneg_left
            (norm_integral_standardCoset_phase_le L m hr alpha htm hinj) (norm_nonneg _)
    _ = (∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖) *
          (((r : ℝ))⁻¹ ^ n *
            Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
              (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n)) := by
        rw [← Finset.sum_mul]
    _ = K * Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
          (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by
        rw [hK]
        ring


/-- The finite half of `G_b subset L` for carriers inside the integral vectors: for every finite
test standard-carried at scale one and standard-periodic at level `r`, the Bruhat coefficient's
finite factor is integrable over the finite adeles above rank four.

The decomposition into cosets is the repository's own, the per-coset bound is the shifted-carrier
bound, and the conductor partition is run once on the sum. -/
theorem lintegral_norm_finiteFactor_lt_top (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {r : ℕ} [NeZero r] {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic r g) :
    ∫⁻ t, ENNReal.ofReal
        ‖∫ x, g x * complexFiniteChar
            (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖
        ∂rationalFiniteAdeleAddHaarMeasure < ⊤ := by
  have hKnonneg : (0 : ℝ) ≤
      (∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖) * ((r : ℝ))⁻¹ ^ n := by
    have : (0 : ℝ) ≤ ∑ alpha, ‖standardFamilyQuotientLift g hperiodic alpha‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    positivity
  refine lintegral_lt_top_of_conductor_bound hn (r ^ (2 * n) * L.polarDeterminant.natAbs) hKnonneg _ ?_
  intro m _ t htm hex
  exact norm_finiteFactor_le L hcarried hperiodic m htm hex

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
