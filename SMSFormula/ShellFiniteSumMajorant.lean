import SMSFormula.ShellFixedWidthMajorant
import SMSFormula.ValueDensityTracePositivity

/-!
# The finite-sum domination, and why the maximizing centre is the trick

Everything about the bad set so far assumed the test dominated by a multiple of a single Gaussian.
The route's test is a finite sum `sum_j Gamma_(u_j) h_j`, and that is not of that shape -- so the
confinement had to be redone.  The obstacle is precise: at one centre the argument divides by
`Gamma_u(x)`, which cancels against the same factor on the dominating side; with a sum there is no
single factor to cancel and the division destroys the bound.

The maximizing centre removes the obstacle.  At each point choose the centre whose Gaussian is
largest there -- a finite family of reals attains its maximum, so no choice principle beyond picking
an index.  Then every term of the dominating sum is at most `M_j` times that value, so the whole sum
is at most `(sum_j M_j)` times it, and the single factor is back.  Dividing is legitimate again and
the slab bound comes out with the total mass `sum_j M_j` in place of the single `M`.

What changes downstream, and what does not.  The centre now depends on the point, so the bad set's
archimedean projection lies in a finite union of translated slabs rather than one -- still bounded,
a finite union of bounded sets being bounded.  Everything else is unchanged: the amplitude is still
chosen once, no limit is taken, and the second factor's compactness finishes exactly as before.

Negative scope.  The majorant must now dominate the pair sum at every centre, which is a real
strengthening and is why the route's majorant is a double sum over centres and shifts.  The maximizer
is a function of the point and not a uniform choice, so no single slab suffices -- checked.  And the
scope is unchanged otherwise: this is the archimedean factor, the domination is still a hypothesis,
and nothing is adelic.
-/

namespace SMSFormula.ShellFixedWidth

open MeasureTheory Set QuadraticMap SMSFormula.ShiftedGaussian

/-! ## The maximizing centre -/

section FiniteSum

variable {X E ι : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousSub E] [Finite ι] [Nonempty ι]

omit [Finite ι] [Nonempty ι] in
/-- The dominating sum collapses to a single factor at the maximizing centre. -/
theorem sum_le_totalMass_mul_max [Fintype ι] (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u : ι → E) {M : ι → ℝ} (hM : ∀ j, 0 ≤ M j) {x : X} {j₀ : ι}
    (hmax : ∀ j, quadraticShiftedGaussian Q hQ b i (u j) x ≤
      quadraticShiftedGaussian Q hQ b i (u j₀) x) :
    ∑ j, M j * quadraticShiftedGaussian Q hQ b i (u j) x ≤
      (∑ j, M j) * quadraticShiftedGaussian Q hQ b i (u j₀) x := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hmax j) (hM j)

omit [Finite ι] [Nonempty ι] in
/-- The finite-sum confinement, at the maximizing centre.  The total mass `sum_j M_j` replaces the
single `M`, and the division is legitimate because the maximizing factor is the one that cancels. -/
theorem exp_abs_polar_le_of_finiteSum [Fintype ι] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (b : ℝ) (i : C(X, E)) (u : ι → E) (v : E) {Φ Ψ : X → ℝ} {M : ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hM : ∀ j, 0 ≤ M j)
    (hdom : ∀ y, |Φ y| ≤ ∑ j, M j * quadraticShiftedGaussian Q hQ b i (u j) y)
    {x : X} {j₀ : ι}
    (hmax : ∀ j, quadraticShiftedGaussian Q hQ b i (u j) x ≤
      quadraticShiftedGaussian Q hQ b i (u j₀) x)
    (hmaj : ∀ y, quadraticShiftedGaussian Q hQ b i (u j₀ + v) y +
      quadraticShiftedGaussian Q hQ b i (u j₀ - v) y ≤ Ψ y)
    (hnonpos : Φ x + ε * Ψ x ≤ 0) :
    Real.exp (-b * Q v) * Real.exp |b * polar Q (i x - u j₀) v| ≤ (∑ j, M j) / ε := by
  set G : ℝ := quadraticShiftedGaussian Q hQ b i (u j₀) x with hG
  set P : ℝ := Real.exp (-b * Q v) * Real.exp |b * polar Q (i x - u j₀) v| with hP
  have hGpos : 0 < G := by
    rw [hG, quadraticShiftedGaussian_apply]
    exact Real.exp_pos _
  have h1 : G * P ≤ Ψ x := by
    rw [hP, ← mul_assoc]
    exact le_trans (exp_abs_polar_mul_le Q hQ b i (u j₀) v x) (hmaj x)
  have h2 : -((∑ j, M j) * G) ≤ Φ x := by
    have habs : |Φ x| ≤ (∑ j, M j) * G :=
      le_trans (hdom x) (sum_le_totalMass_mul_max Q hQ b i u hM hmax)
    exact neg_le_of_abs_le habs
  have h3 : ε * (G * P) ≤ (∑ j, M j) * G := by
    have hle : ε * (G * P) ≤ ε * Ψ x := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  have h4 : G * (ε * P) ≤ G * (∑ j, M j) := by
    calc G * (ε * P) = ε * (G * P) := by ring
      _ ≤ (∑ j, M j) * G := h3
      _ = G * (∑ j, M j) := by ring
  have h5 : ε * P ≤ ∑ j, M j := le_of_mul_le_mul_left h4 hGpos
  rw [le_div_iff₀ hε]
  linarith

/-- The maximizing centre exists, a finite family of reals attaining its maximum. -/
theorem exists_max_center (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ) (i : C(X, E))
    (u : ι → E) (x : X) :
    ∃ j₀ : ι, ∀ j, quadraticShiftedGaussian Q hQ b i (u j) x ≤
      quadraticShiftedGaussian Q hQ b i (u j₀) x :=
  Finite.exists_max fun j ↦ quadraticShiftedGaussian Q hQ b i (u j) x

end FiniteSum

/-! ## The bad set is still compact -/

section FiniteSumAssembly

variable {E Y ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Y] [CompactSpace Y] [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

omit [Nonempty κ] in
/-- The bad set is compact for a finite-sum domination.  The maximizing centre depends on the point,
so the archimedean projection lies in a finite union of translated slabs -- still bounded. -/
theorem isCompact_badSet_of_finiteSumMajorant (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (hpos : Q.PosDef) {b : ℝ} (hb : 0 < b) {v : κ → E}
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) (u : ι → E) {Φ Ψ : E × Y → ℝ} (hΦ : Continuous Φ)
    (hΨ : Continuous Ψ) {M : ι → ℝ} {ε : ℝ} (hε : 0 < ε) (hM : ∀ j, 0 ≤ M j)
    (hdom : ∀ p, |Φ p| ≤ ∑ j, M j * quadraticShiftedGaussian Q hQ b (ContinuousMap.fst) (u j) p)
    (hmaj : ∀ j, ∀ k, ∀ p,
      quadraticShiftedGaussian Q hQ b (ContinuousMap.fst) (u j + v k) p +
        quadraticShiftedGaussian Q hQ b (ContinuousMap.fst) (u j - v k) p ≤ Ψ p) :
    IsCompact {p : E × Y | Φ p + ε * Ψ p ≤ 0} := by
  obtain ⟨S, hS⟩ := Finite.exists_le (fun k ↦ Q (v k))
  set R : ℝ := Real.log ((∑ j, M j) / ε * Real.exp (b * S)) / b with hR
  obtain ⟨r, hr⟩ := (isBounded_polarSlab hpos hspan R).subset_closedBall (0 : E)
  have hsub : {p : E × Y | Φ p + ε * Ψ p ≤ 0} ⊆
      (⋃ j : ι, Metric.closedBall (u j) r) ×ˢ (Set.univ : Set Y) := by
    intro p hp
    obtain ⟨j₀, hmax⟩ := exists_max_center Q hQ b (ContinuousMap.fst) u p
    refine ⟨Set.mem_iUnion.mpr ⟨j₀, ?_⟩, Set.mem_univ _⟩
    have hslab : ∀ k, |polar Q (p.1 - u j₀) (v k)| ≤ R := by
      intro k
      have hle : Real.exp (-b * Q (v k)) * Real.exp |b * polar Q (p.1 - u j₀) (v k)| ≤
          (∑ j, M j) / ε :=
        exp_abs_polar_le_of_finiteSum Q hQ b (ContinuousMap.fst) u (v k) hε hM hdom
          hmax (hmaj j₀ k) hp
      have hposL : 0 < Real.exp (-b * Q (v k)) *
          Real.exp |b * polar Q (p.1 - u j₀) (v k)| := mul_pos (Real.exp_pos _) (Real.exp_pos _)
      have hMe0 : 0 < (∑ j, M j) / ε := lt_of_lt_of_le hposL hle
      have hEpos : 0 < Real.exp (b * Q (v k)) := Real.exp_pos _
      have hkey : Real.exp |b * polar Q (p.1 - u j₀) (v k)| ≤
          (∑ j, M j) / ε * Real.exp (b * Q (v k)) := by
        have h := mul_le_mul_of_nonneg_right hle hEpos.le
        have hcancel : Real.exp (-b * Q (v k)) * Real.exp |b * polar Q (p.1 - u j₀) (v k)| *
            Real.exp (b * Q (v k)) = Real.exp |b * polar Q (p.1 - u j₀) (v k)| := by
          rw [mul_right_comm, ← Real.exp_add]
          simp
        rw [hcancel] at h
        exact h
      have hmono : Real.log ((∑ j, M j) / ε * Real.exp (b * Q (v k))) ≤
          Real.log ((∑ j, M j) / ε * Real.exp (b * S)) := by
        refine Real.log_le_log (mul_pos hMe0 hEpos)
          (mul_le_mul_of_nonneg_left ?_ hMe0.le)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hS k) hb.le)
      have hlog : |b * polar Q (p.1 - u j₀) (v k)| ≤
          Real.log ((∑ j, M j) / ε * Real.exp (b * Q (v k))) :=
        (Real.le_log_iff_exp_le (mul_pos hMe0 hEpos)).mpr hkey
      have heq : |b * polar Q (p.1 - u j₀) (v k)| = b * |polar Q (p.1 - u j₀) (v k)| := by
        rw [abs_mul, abs_of_pos hb]
      rw [hR, le_div_iff₀ hb, mul_comm]
      calc b * |polar Q (p.1 - u j₀) (v k)| = |b * polar Q (p.1 - u j₀) (v k)| := heq.symm
        _ ≤ Real.log ((∑ j, M j) / ε * Real.exp (b * Q (v k))) := hlog
        _ ≤ Real.log ((∑ j, M j) / ε * Real.exp (b * S)) := hmono
    have hmem : p.1 - u j₀ ∈ {w : E | ∀ k, |polar Q w (v k)| ≤ R} := hslab
    have := hr hmem
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  refine IsCompact.of_isClosed_subset ?_ ?_ hsub
  · refine IsCompact.prod ?_ isCompact_univ
    refine (Bornology.isBounded_iUnion.mpr fun j ↦ Metric.isBounded_closedBall).isCompact_closure
      |>.of_isClosed_subset ?_ subset_closure
    exact isClosed_iUnion_of_finite fun j ↦ Metric.isClosed_closedBall
  · exact isClosed_le (hΦ.add (continuous_const.mul hΨ)) continuous_const

end FiniteSumAssembly

end SMSFormula.ShellFixedWidth
