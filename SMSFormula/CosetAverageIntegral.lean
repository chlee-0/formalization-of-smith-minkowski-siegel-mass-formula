import SMSFormula.FiniteConductorSummability

/-!
# A locally constant integral is the normalized finite sum

The conductor bounds (`FiniteQuadraticSumModulusBound`, `FiniteConductorSummability`) bound the
normalized finite quadratic sum, but the analytic admissibility
`G_b subset L` needs a bound on a local integral over a compact open carrier.  This file supplies
the bridge between the two, and it is a statement about compact groups alone -- no quadratic form,
no valuation, nothing `p`-adic.

The content.  A function that is constant on the cosets of a finite-index subgroup is, by
definition, a function `F` on the quotient precomposed with the projection -- so no representative
is ever chosen.  The fibers of the projection are translates of the subgroup, so an invariant
measure gives them all the same mass, and the integral collapses to that one mass times the sum of
`F` over the quotient.  With a probability measure the mass is `1/card`, so the integral is the
normalized sum -- the exact quantity the conductor bounds control.

What is and is not normalized.  The collapse `int = mass * sum` needs no normalization at all and
holds for any invariant finite measure.  Only the identification of the mass with `1/card` uses the
probability hypothesis, and that is recorded separately so the two are never conflated.

The collapse below is also
`PositiveDefiniteIntegralLattice.integral_comp_quotientAddGroupMk_eq_measure_mul_sum`
(`RationalFiniteAdeleIntegralLatticeFiniteQuotient`), in the same shape.  What this file adds is the
identification of the common fiber mass with `1/card` at a probability measure, together with the
normalized and norm forms; for the collapse itself either form may be used.

Negative scope.  Nothing here evaluates a sum, and the quadratic form never appears: this converts a
bound on a finite sum into a bound on an integral and does nothing else.  Finiteness of the quotient
is a hypothesis, not derived from openness here.
-/

namespace SMSFormula.CosetAverage

open MeasureTheory
open scoped ENNReal

variable {G : Type*} [AddGroup G] [MeasurableSpace G]

/-! ## The fibers of the projection -/

omit [MeasurableSpace G] in
/-- The fiber over a class is a translate of the subgroup, written as a preimage so that invariance
applies to it directly. -/
theorem preimage_mk_singleton (K : AddSubgroup G) (g : G) :
    (QuotientAddGroup.mk ⁻¹' {(QuotientAddGroup.mk g : G ⧸ K)}) =
      (fun y ↦ -g + y) ⁻¹' (K : Set G) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    simpa using K.neg_mem h
  · intro h
    simpa using K.neg_mem h

/-- SO all fibers have the same mass, by invariance alone. -/
theorem measure_preimage_mk_singleton [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (K : AddSubgroup G) (q : G ⧸ K) :
    μ (QuotientAddGroup.mk ⁻¹' {q}) = μ (K : Set G) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [preimage_mk_singleton]
  exact measure_preimage_add μ (-g) _

/-- And the measurability hypothesis on the fibers reduces to one fact: measurability of the
subgroup itself, the fibers being its translates. -/
theorem measurableSet_preimage_mk [MeasurableAdd G] {K : AddSubgroup G}
    (hK : MeasurableSet (K : Set G)) (q : G ⧸ K) :
    MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [preimage_mk_singleton]
  exact hK.preimage (measurable_const_add (-g))

/-! ## The collapse -/

/-- The collapse, with no normalization: a function constant on the cosets integrates to the common
fiber mass times the sum over the quotient.  The function is given as `F` on the quotient, so no
representative is selected. -/
theorem integral_comp_mk [MeasurableAdd G] (μ : Measure G) [IsFiniteMeasure μ]
    [μ.IsAddLeftInvariant] {K : AddSubgroup G} [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G))
    (F : G ⧸ K → ℂ) :
    ∫ x, F (QuotientAddGroup.mk x) ∂μ = (μ (K : Set G)).toReal • ∑ q : G ⧸ K, F q := by
  have hpt : (fun x ↦ F (QuotientAddGroup.mk x)) =
      fun x ↦ ∑ q : G ⧸ K, (QuotientAddGroup.mk ⁻¹' {q}).indicator (fun _ ↦ F q) x := by
    funext x
    rw [Finset.sum_eq_single (QuotientAddGroup.mk x : G ⧸ K)]
    · exact (Set.indicator_of_mem rfl _).symm
    · intro q _ hq
      refine Set.indicator_of_notMem ?_ _
      simpa [eq_comm] using hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hpt, integral_finset_sum]
  · have hterm : ∀ q : G ⧸ K,
        ∫ x, (QuotientAddGroup.mk ⁻¹' {q}).indicator (fun _ ↦ F q) x ∂μ =
          (μ (K : Set G)).toReal • F q := by
      intro q
      rw [integral_indicator_const _ (hfib q)]
      show (μ (QuotientAddGroup.mk ⁻¹' {q})).toReal • F q = _
      rw [measure_preimage_mk_singleton μ K q]
    simp only [hterm]
    rw [Finset.smul_sum]
  · intro q _
    exact (integrable_const (F q)).indicator (hfib q)

/-! ## The mass, and the normalized form -/

/-- The common mass times the number of classes is the total mass -- the only place a normalization
could enter. -/
theorem card_smul_measure_coe [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    {K : AddSubgroup G} [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G)) :
    (Fintype.card (G ⧸ K)) • μ (K : Set G) = μ Set.univ := by
  have hcover : (Set.univ : Set G) =
      ⋃ q : G ⧸ K, (QuotientAddGroup.mk ⁻¹' {q} : Set G) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : G ⧸ K ↦ (QuotientAddGroup.mk ⁻¹' {q} : Set G)) := by
    intro q r hqr
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    exact hqr (hx ▸ hx')
  rw [hcover, measure_iUnion hdisj hfib, tsum_fintype]
  simp only [measure_preimage_mk_singleton μ K, Finset.sum_const, Finset.card_univ]

/-- Hence, at a probability measure, the common mass is the reciprocal of the number of classes. -/
theorem measure_coe_toReal [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    [IsProbabilityMeasure μ] {K : AddSubgroup G} [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G)) :
    (μ (K : Set G)).toReal = ((Fintype.card (G ⧸ K) : ℝ))⁻¹ := by
  have hcard : (Fintype.card (G ⧸ K)) • μ (K : Set G) = 1 := by
    rw [card_smul_measure_coe μ hfib, measure_univ]
  have hne : μ (K : Set G) ≠ ⊤ := measure_ne_top μ _
  have hreal : (Fintype.card (G ⧸ K) : ℝ) * (μ (K : Set G)).toReal = 1 := by
    have := congrArg ENNReal.toReal hcard
    rwa [nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this
  have hpos : (0 : ℝ) < Fintype.card (G ⧸ K) := by
    exact_mod_cast Fintype.card_pos
  field_simp at hreal ⊢
  linarith [hreal]

/-- SO the integral is the normalized sum -- the exact quantity the conductor bounds control, so a
bound on the finite sum is a bound on the local integral. -/
theorem integral_comp_mk_eq_average [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    [IsProbabilityMeasure μ] {K : AddSubgroup G} [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G))
    (F : G ⧸ K → ℂ) :
    ∫ x, F (QuotientAddGroup.mk x) ∂μ =
      ((Fintype.card (G ⧸ K) : ℝ))⁻¹ • ∑ q : G ⧸ K, F q := by
  rw [integral_comp_mk μ hfib, measure_coe_toReal μ hfib]

/-- The form the bounds are stated in: the modulus of the local integral is the modulus of the
normalized finite sum. -/
theorem norm_integral_comp_mk [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    [IsProbabilityMeasure μ] {K : AddSubgroup G} [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G))
    (F : G ⧸ K → ℂ) :
    ‖∫ x, F (QuotientAddGroup.mk x) ∂μ‖ =
      ((Fintype.card (G ⧸ K) : ℝ))⁻¹ * ‖∑ q : G ⧸ K, F q‖ := by
  rw [integral_comp_mk_eq_average μ hfib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

end SMSFormula.CosetAverage
