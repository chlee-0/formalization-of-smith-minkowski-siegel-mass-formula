import SMSFormula.PadicQuadraticRestrictedLocalDensityCount

/-!
# Residue data carrying a relatively open compact subset of a shell

Let `O ⊆ ℚ_p^N` be a compact set of integral vectors that is relatively open in a set `X` (e.g. a
supplied compact open orbit `t_p · x_old` in the shell `X_a`): `O = X ∩ V` for an open `V`.  Then
there exist a level `e` and residues `R ⊆ (ℤ/p^eℤ)^N` whose restricted integral set carries `O`:

`T_R ∩ X = O`.

Indeed a thickening of the compact `O` by some `δ > 0` stays inside `V`; at a level `e` with
`p^{-e} < δ` every residue ball of a point of `O` lies in that thickening, and `R` is the set of
residues of `O`.  Consequently the glued slice mass of `T_R` on the shell is the glued slice mass
of `O` itself, so the replacement lemma evaluates the orbit test.  Only existence is asserted;
no level, residue set or cover is chosen.
-/

noncomputable section

open MeasureTheory Set Metric

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

/-- Existence of carrying residue data: a compact set of integral vectors relatively open in `X`
is the trace on `X` of the restricted integral set of some residue data. -/
theorem exists_restrictedIntegralVectors_inter_eq {X O V : Set (Fin N → ℚ_[p])}
    (hO : IsCompact O) (hV : IsOpen V) (hOX : O = X ∩ V)
    (hOint : O ⊆ closedBall (0 : Fin N → ℚ_[p]) 1) :
    ∃ (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))), restrictedIntegralVectors e R ∩ X = O := by
  have hOV : O ⊆ V := hOX ▸ inter_subset_right
  obtain ⟨δ, hδ, hsub⟩ := hO.exists_thickening_subset_open hV hOV
  obtain ⟨e, he⟩ := PadicInt.exists_pow_neg_lt p hδ
  refine ⟨e, vectorReduction e '' (vectorInclusion ⁻¹' O), ?_⟩
  apply Subset.antisymm
  · rintro v ⟨⟨y, ⟨x, hxO, hxy⟩, rfl⟩, hvX⟩
    have hmem : vectorInclusion y ∈ V := by
      apply hsub
      rw [Metric.mem_thickening_iff]
      refine ⟨vectorInclusion x, hxO, ?_⟩
      rw [dist_eq_norm, ← map_sub, norm_vectorInclusion]
      exact lt_of_le_of_lt ((vectorReduction_eq_iff e y x).1 hxy.symm) he
    rw [hOX]
    exact ⟨hvX, hmem⟩
  · intro v hv
    have hvX : v ∈ X := (hOX ▸ hv : v ∈ X ∩ V).1
    have hvr : v ∈ Set.range (vectorInclusion (p := p) (N := N)) := by
      rw [range_vectorInclusion]; exact hOint hv
    obtain ⟨y, rfl⟩ := hvr
    exact ⟨⟨y, ⟨y, hv, rfl⟩, rfl⟩, hvX⟩

/-- The glued slice mass of the carrying set is that of the carried set on the shell `{Q = a}`. -/
theorem preimage_val_restrictedIntegralVectors_eq_of_shell
    (Q : (Fin N → ℚ_[p]) → ℚ_[p]) (a : ℚ_[p]) {O : Set (Fin N → ℚ_[p])} {e : ℕ}
    {R : Set (Fin N → ZMod (p ^ e))} (hR : restrictedIntegralVectors e R ∩ {v | Q v = a} = O) :
    ((Subtype.val : {v : Fin N → ℚ_[p] // Q v = a} → _) ⁻¹' restrictedIntegralVectors e R) =
      Subtype.val ⁻¹' O := by
  ext x
  simp only [mem_preimage]
  constructor
  · intro h
    rw [← hR]
    exact ⟨h, x.2⟩
  · intro h
    rw [← hR] at h
    exact h.1

end PadicInt
