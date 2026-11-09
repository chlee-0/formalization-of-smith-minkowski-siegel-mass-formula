import SMSFormula.PolarGaussianQuadraticIdentification
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The real shell is compact

The clopen approximation scheme handles the tail condition on the finite factor but not on the
archimedean one, because the real vector space is not compact and the clopen family there is
trivial. This file supplies the archimedean half by a different route: the object integrated over
is not the whole real space but a shell
`{x | Q x = a}` of the positive definite polar form, and such a shell is an ellipsoid -- compact.

Coercivity is the content.  Positive definiteness alone is a pointwise statement and gives no bound;
what makes the sublevel sets bounded is a uniform lower bound `m * ‖x‖^2 ≤ Q x` with `m > 0`.  That
comes from compactness of the unit sphere in finite dimension: the form attains a minimum there,
positive because the minimizer is nonzero, and homogeneity `Q (r • x) = r^2 Q x` propagates it to
every vector.  Sublevel sets then sit in a closed ball, and closed plus bounded is compact.

What compactness gives.  Two things, and the second is the one that matters.  First, on a compact
space separation of points alone gives tail-bounded approximants at the fixed constant `1`, so the
tail hypothesis is free there.  Second, and stronger, a finite regular measure concentrated on a
compact set -- giving the complement measure zero -- is determined by any point-separating
subalgebra with no compactness of the ambient space and no tail bound at all: every continuous
function is integrable against it, and the approximation on the carrying compact set already
controls the whole integral.  That is the archimedean situation exactly.

Scope.  It is the shell that is compact, not the real space: nothing here makes the
archimedean factor compact, and the sublevel version is equally conditional on positive
definiteness -- for an indefinite form the shell is a hyperboloid and unbounded.  The shell
may be empty, at a negative value, where compactness is vacuous, and at value zero it is the single
point `0`.  Continuity of the form is a hypothesis, as everywhere else in this layer.  And the
Gaussian generators are constant on a shell of the same form, so the separation on the shell must
come from shifted centers; that shift is not analyzed here.  Nothing is adelic.
-/

namespace SMSFormula.RealShell

open Metric Set MeasureTheory

/-! ## Coercivity of a positive definite form -/

section Coercivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sublevel set sits in a closed ball, with the radius read off the coercivity constant. -/
theorem quadratic_le_subset_closedBall (Q : QuadraticForm ℝ E) {m : ℝ} (hm : 0 < m)
    (hb : ∀ x, m * ‖x‖ ^ 2 ≤ Q x) (a : ℝ) :
    {x : E | Q x ≤ a} ⊆ closedBall (0 : E) (Real.sqrt (a / m)) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have h1 : m * ‖x‖ ^ 2 ≤ a := le_trans (hb x) hx
  have h2 : ‖x‖ ^ 2 ≤ a / m := by
    rw [le_div_iff₀ hm]
    linarith [h1]
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt (a / m) := Real.sqrt_le_sqrt h2

section FiniteDim

variable [FiniteDimensional ℝ E]

/-- Coercivity.  A continuous positive definite quadratic form on a finite-dimensional real normed
space dominates a positive multiple of the squared norm.  This is the uniform statement that
pointwise positivity does not give. -/
theorem exists_pos_norm_sq_le (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (hpos : Q.PosDef) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m * ‖x‖ ^ 2 ≤ Q x := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun x ↦ ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      (isCompact_sphere (0 : E) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hQ.continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      intro h
      rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hx₀
      exact zero_ne_one hx₀
    refine ⟨Q x₀, hpos x₀ hx₀0, fun x ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hnpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hn]
      have h1 : Q x₀ ≤ Q (‖x‖⁻¹ • x) := hmin hmem
      have h2 : Q (‖x‖⁻¹ • x) = ‖x‖⁻¹ * ‖x‖⁻¹ * Q x := by
        simpa [smul_eq_mul] using QuadraticMap.map_smul (Q := Q) (‖x‖⁻¹) x
      have hsq : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos hnpos 2
      have h3 := mul_le_mul_of_nonneg_right h1 hsq.le
      rw [h2] at h3
      have h4 : ‖x‖⁻¹ * ‖x‖⁻¹ * Q x * ‖x‖ ^ 2 = Q x := by
        field_simp
      linarith [h3, h4.le, h4.ge]

/-- Sublevel sets of a positive definite form are compact: closed by continuity, bounded by
coercivity, and finite dimension makes closed plus bounded compact. -/
theorem isCompact_quadratic_le (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (hpos : Q.PosDef)
    (a : ℝ) : IsCompact {x : E | Q x ≤ a} := by
  rcases lt_or_ge a 0 with ha | ha
  · have hempty : {x : E | Q x ≤ a} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ha (hpos.nonneg x)
    rw [hempty]
    exact isCompact_empty
  · obtain ⟨m, hm, hb⟩ := exists_pos_norm_sq_le Q hQ hpos
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hQ continuous_const) ?_
    exact (Metric.isBounded_closedBall).subset (quadratic_le_subset_closedBall Q hm hb a)

/-- The shell is compact.  A level set of a continuous positive definite form on a
finite-dimensional real normed space is an ellipsoid, hence compact. -/
theorem isCompact_quadratic_shell (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (hpos : Q.PosDef)
    (a : ℝ) : IsCompact {x : E | Q x = a} :=
  (isCompact_quadratic_le Q hQ hpos a).of_isClosed_subset (isClosed_eq hQ continuous_const)
    fun _ hx ↦ le_of_eq hx

/-- The shell as a space is compact, which is the form the determining-core layer consumes. -/
theorem compactSpace_quadratic_shell (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (hpos : Q.PosDef)
    (a : ℝ) : CompactSpace ↥{x : E | Q x = a} :=
  isCompact_iff_compactSpace.mp (isCompact_quadratic_shell Q hQ hpos a)

end FiniteDim

end Coercivity

/-! ## What compactness supplies: the tail bound, and then the criterion without it -/

section TailBound

variable {X : Type*} [TopologicalSpace X]

end TailBound

section AlmostEverywhere

variable {X : Type*} [MeasurableSpace X]

/-- A property holding on a carrying set holds almost everywhere for a measure whose complement mass
vanishes. -/
theorem ae_of_measure_compl_eq_zero {μ : Measure X} {K : Set X} (hK : μ Kᶜ = 0) {p : X → Prop}
    (hp : ∀ x ∈ K, p x) : ∀ᵐ x ∂μ, p x := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx hxK ↦ hx (hp x hxK)) hK

end AlmostEverywhere

section Concentrated

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Every continuous function is integrable against a finite measure concentrated on a compact set:
it is bounded there, and the rest of the space is null. -/
theorem integrable_of_concentrated {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hμK : μ Kᶜ = 0) (g : C(X, ℝ)) : Integrable (fun x ↦ (g : X → ℝ) x) μ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn g.continuous.continuousOn
  exact (integrable_const M).mono' g.continuous.aestronglyMeasurable
    (ae_of_measure_compl_eq_zero hμK fun x hx ↦ hM x hx)

/-- The accuracy bound: against a measure concentrated on the carrying compact set, an approximant
accurate on that set is accurate in integral. -/
theorem abs_integral_sub_le_of_concentrated {μ : Measure X} [IsFiniteMeasure μ] {K : Set X}
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) (f g : C(X, ℝ)) {ε : ℝ}
    (hg : ∀ x ∈ K, |(f : X → ℝ) x - (g : X → ℝ) x| ≤ ε) :
    |(∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (g : X → ℝ) x ∂μ| ≤ ε * μ.real univ := by
  have hf := integrable_of_concentrated hK hμK f
  have hgi := integrable_of_concentrated hK hμK g
  rw [← integral_sub hf hgi]
  calc |∫ x, ((f : X → ℝ) x - (g : X → ℝ) x) ∂μ|
      ≤ ∫ x, |(f : X → ℝ) x - (g : X → ℝ) x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, ε ∂μ :=
        integral_mono_ae (hf.sub hgi).abs (integrable_const ε)
          (ae_of_measure_compl_eq_zero hμK hg)
    _ = ε * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

/-- The criterion without a tail bound.  Two finite measures concentrated on a common compact set
and agreeing on a point-separating subalgebra give the same integral to every continuous function --
no compactness of the ambient space, no tail hypothesis, and no compact support on the target. -/
theorem integral_eq_of_concentrated {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set X} (hK : IsCompact K) (hμK : μ Kᶜ = 0) (hνK : ν Kᶜ = 0) (A : Subalgebra ℝ C(X, ℝ))
    (hA : A.SeparatesPoints) (h : ∀ g : A, ∫ x, (g : C(X, ℝ)) x ∂μ = ∫ x, (g : C(X, ℝ)) x ∂ν)
    (f : C(X, ℝ)) : ∫ x, (f : X → ℝ) x ∂μ = ∫ x, (f : X → ℝ) x ∂ν := by
  set M : ℝ := μ.real univ + ν.real univ with hMdef
  have hM : 0 ≤ M := by positivity
  have key : ∀ ε : ℝ, 0 < ε →
      |(∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (f : X → ℝ) x ∂ν| ≤ ε * M := by
    intro ε hε
    obtain ⟨g, hgA, hg⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints hA f hK hε
    have hgsub : ∀ x ∈ K, |(f : X → ℝ) x - (g : X → ℝ) x| ≤ ε := fun x hx ↦ by
      rw [abs_sub_comm]
      simpa [Real.norm_eq_abs] using (hg x hx).le
    have hμle := abs_integral_sub_le_of_concentrated hK hμK f g hgsub
    have hνle := abs_integral_sub_le_of_concentrated hK hνK f g hgsub
    have hgeq : ∫ x, (g : X → ℝ) x ∂μ = ∫ x, (g : X → ℝ) x ∂ν := h ⟨g, hgA⟩
    have hsplit : (∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (f : X → ℝ) x ∂ν =
        ((∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (g : X → ℝ) x ∂μ) -
          ((∫ x, (f : X → ℝ) x ∂ν) - ∫ x, (g : X → ℝ) x ∂ν) := by
      rw [hgeq]; ring
    have htri : |(∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (f : X → ℝ) x ∂ν| ≤
        |(∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (g : X → ℝ) x ∂μ| +
          |(∫ x, (f : X → ℝ) x ∂ν) - ∫ x, (g : X → ℝ) x ∂ν| := by
      rw [hsplit]; exact abs_sub _ _
    have : ε * μ.real univ + ε * ν.real univ = ε * M := by rw [hMdef]; ring
    linarith
  by_contra hne
  set d : ℝ := |(∫ x, (f : X → ℝ) x ∂μ) - ∫ x, (f : X → ℝ) x ∂ν| with hd
  have hdpos : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have := key (d / (2 * (M + 1))) (by positivity)
  have hlt : d / (2 * (M + 1)) * M < d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (M + 1))]
    nlinarith [hdpos, hM]
  linarith

/-- The same at the level of measures. -/
theorem eq_of_concentrated [T2Space X] [LocallyCompactSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [μ.Regular] [ν.Regular] {K : Set X} (hK : IsCompact K) (hμK : μ Kᶜ = 0)
    (hνK : ν Kᶜ = 0) (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (h : ∀ g : A, ∫ x, (g : C(X, ℝ)) x ∂μ = ∫ x, (g : C(X, ℝ)) x ∂ν) : μ = ν :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f ↦
    integral_eq_of_concentrated hK hμK hνK A hA h f.toContinuousMap

end Concentrated

end SMSFormula.RealShell

/-! ## The repository's own real form -/

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The polar shell of a lattice is compact.  The repository's own archimedean form is continuous
and positive definite, so every level set of it is an ellipsoid. -/
theorem isCompact_polarShell (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    IsCompact {x : Fin n → ℝ | L.polarQuadraticForm x = a} :=
  SMSFormula.RealShell.isCompact_quadratic_shell L.polarQuadraticForm
    L.continuous_polarQuadraticForm L.posDef_polarQuadraticForm a

end PositiveDefiniteIntegralLattice
