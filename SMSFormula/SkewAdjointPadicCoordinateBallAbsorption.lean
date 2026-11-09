import SMSFormula.SkewAdjointPadicCoordinateBallCompactness

/-!
# Uniform norm absorption by p-adic coordinate balls

The transported coordinate lattice is simultaneously a zero-neighborhood and
a compact set.  A small ambient-norm error relative to an element of the
lattice therefore remains in the lattice.  Scaling both vectors by the same
nonzero power of `p` makes the resulting absorption constant uniform across
all coordinate-ball levels.

This argument uses only ordinary norm estimates together with the literal
scalar-image definition of the coordinate balls.  In particular, it does not
install an ultrametric instance for the selected ambient matrix/operator norm,
and it contains no Haar scaling or nonlinear pushforward statement.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- There is one positive ambient-norm absorption constant that works for
every uniform coordinate-ball level. -/
theorem exists_skewAdjointPadicUniformCoordinateBall_norm_absorption
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ q₀ : ℝ, 0 < q₀ ∧
      ∀ k
        (h e : (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        h ∈ skewAdjointPadicUniformCoordinateBall F p k →
        ‖e‖ ≤ q₀ * ‖h‖ →
        e ∈ skewAdjointPadicUniformCoordinateBall F p k := by
  obtain ⟨r, hr, hrL⟩ :=
    Metric.mem_nhds_iff.mp
      (skewAdjointPadicCoordinateLattice_mem_nhds_zero F p)
  obtain ⟨C, hCL⟩ :=
    (skewAdjointPadicCoordinateLattice F p).isCompact.isBounded.subset_closedBall
      (0 : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
  have hC : 0 ≤ C := by
    have := hCL (zero_mem_skewAdjointPadicCoordinateLattice F p)
    simpa using this
  let q₀ : ℝ := r / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hq₀ : 0 < q₀ := div_pos hr hC1
  refine ⟨q₀, hq₀, ?_⟩
  intro k h e hh he
  rcases hh with ⟨u, hu, rfl⟩
  let a : ℚ_[p] := (p : ℚ_[p]) ^ k
  have ha : a ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have huC : ‖u‖ ≤ C := by
    have := hCL hu
    simpa using this
  have hqC : q₀ * C < r := by
    calc
      q₀ * C < q₀ * (C + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hq₀
      _ = r := by
        dsimp [q₀]
        field_simp
  have he_scaled : ‖a⁻¹ • e‖ < r := by
    rw [norm_smul]
    calc
      ‖a⁻¹‖ * ‖e‖ ≤ ‖a⁻¹‖ * (q₀ * ‖a • u‖) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = q₀ * ‖u‖ := by
        rw [norm_smul, norm_inv]
        have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
        field_simp
      _ ≤ q₀ * C := mul_le_mul_of_nonneg_left huC hq₀.le
      _ < r := hqC
  refine ⟨a⁻¹ • e, ?_, ?_⟩
  · apply hrL
    simpa [Metric.mem_ball] using he_scaled
  · rw [skewAdjointPadicUniformCoordinateDilation_apply]
    change a • (a⁻¹ • e) = e
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

end Matrix
