import SMSFormula.Genus
import SMSFormula.IntegralLatticeCoordinates
import SMSFormula.GenusDeterminantInvariants
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Round
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.Real.StarOrdered

/-!
# Finiteness results for the Smith–Minkowski–Siegel mass formula

This file establishes the finiteness milestones needed before defining mass:

1. **`isometryGroup_finite`**: The integral isometry group `O(L)` of a
   positive-definite integral lattice is finite.
2. **`properIsometryGroup_finite`**: The proper integral isometry group `SO(L)`
   is finite.
3. **`genus_finite`**: The genus of `L` (as a set of global isometry classes)
   is finite.

## Proof outlines

### Isometry group finiteness (§7103–7106 of Schulze-Pillot)

An integral matrix `U` satisfying `Uᵀ F U = F` with `F` positive definite
must have bounded entries.  Indeed, each column of `U` has bounded `F`-norm
(equal to a diagonal entry of `F`), and positive definiteness of `F` over `ℝ`
forces each entry to be bounded.  Integer matrices with bounded entries form
a finite set.

### Genus finiteness (§5280–5318 of Schulze-Pillot)

* **Theorem [finiteness_classnumber]**: There are only finitely many isometry
  classes of integral quadratic `ℤ`-lattices of fixed rank `n` and fixed
  determinant `det_B = det(F)`.  (Proof by induction on rank, using Hermite's
  bound on the minimum of the form.)
* **Corollary**: Lattices in the same genus have the same `det_B` (since the
  determinant ratio is a `p`-adic unit for all `p`, hence `±1`; and both are
  positive by definiteness).  Combined with the theorem, this gives finiteness
  of the genus.

## References

* Schulze-Pillot, *Lecture Notes on Quadratic Forms and their Arithmetic*,
  Theorem [finiteness_classnumber] and its corollary (around lines 5280–5318),
  and the compact-definite finiteness remark (lines 7103–7106).
-/

open Matrix

noncomputable section

set_option linter.unusedSimpArgs false

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

lemma ext_pairingMatrix {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.pairingMatrix = L'.pairingMatrix) : L = L' := by
  cases L
  cases L'
  simp at h
  subst h
  rfl

/-! ## Auxiliary finiteness lemmas -/

/-
The set of integer vectors `v` with `vᵀ F v ≤ M` is finite when `F` is
a positive-definite integer matrix.

**Proof sketch**: Cast to `ℝ`.  The positive-definite form `F_ℝ` has all
eigenvalues positive (`Matrix.PosDef.eigenvalues_pos`), so the quadratic form
`x ↦ xᵀ F_ℝ x` satisfies `xᵀ F_ℝ x ≥ λ_min ‖x‖²` with `λ_min > 0`.
If `vᵀ F v ≤ M` for `v ∈ ℤⁿ`, then `‖(v : ℝⁿ)‖² ≤ M / λ_min`,
bounding each `|v_i|`.  Integer vectors with bounded entries form a finite set
(via `Set.Finite.pi` and `Set.finite_Icc`).
-/
set_option maxHeartbeats 800000 in
lemma finite_int_vectors_bounded_quadForm
    (F : Matrix (Fin n) (Fin n) ℤ)
    (hF : (F.map (Int.cast : ℤ → ℝ)).PosDef)
    (M : ℤ) :
    Set.Finite { v : Fin n → ℤ | dotProduct v (F.mulVec v) ≤ M } := by
  -- Since $F$ is positive definite, there exists a constant $c > 0$ such that $v^T F v \geq c \|v\|^2$ for all $v \in \mathbb{R}^n$.
  obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ v : Fin n → ℝ, (v ⬝ᵥ (F.map (Int.cast : ℤ → ℝ)).mulVec v) ≥ c * (Finset.sum Finset.univ fun i => v i ^ 2) := by
    by_cases hn : n = 0;
    · subst hn; use 1; norm_num;
    · -- Since $F$ is positive definite, there exists a constant $c > 0$ such that $v^T F v \geq c \|v\|^2$ for all $v \in \mathbb{R}^n$. This follows from the fact that the quadratic form is continuous and positive definite.
      have h_cont_pos_def : ∃ c > 0, ∀ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 → (v ⬝ᵥ (F.map (Int.cast : ℤ → ℝ)).mulVec v) ≥ c := by
        have h_compact : IsCompact {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1} := by
          refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
          exact ⟨ isClosed_eq ( continuous_finset_sum _ fun _ _ => Continuous.pow ( continuous_apply _ ) _ ) continuous_const, isBounded_iff_forall_norm_le.mpr ⟨ 1, by rintro v ( hv : ∑ i, v i ^ 2 = 1 ) ; exact pi_norm_le_iff_of_nonneg ( by norm_num ) |>.2 fun i => by simpa [ hv ] using Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( v i ) ) ( Finset.mem_univ i ) ) ⟩ ⟩;
        have h_cont_pos_def : ∃ c ∈ (Set.image (fun v : Fin n → ℝ => (v ⬝ᵥ (F.map (Int.cast : ℤ → ℝ)).mulVec v)) {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}), ∀ y ∈ (Set.image (fun v : Fin n → ℝ => (v ⬝ᵥ (F.map (Int.cast : ℤ → ℝ)).mulVec v)) {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}), c ≤ y := by
          apply_rules [ IsCompact.exists_isLeast, h_compact ];
          · exact h_compact.image <| Continuous.dotProduct ( continuous_id' ) <| Continuous.matrix_mulVec ( continuous_const ) continuous_id';
          · exact ⟨ _, ⟨ fun i => if i = ⟨ 0, Nat.pos_of_ne_zero hn ⟩ then 1 else 0, by norm_num, rfl ⟩ ⟩;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h_cont_pos_def;
        use c;
        have := hF.2;
        simp_all +decide [ Finsupp.sum_fintype, dotProduct, Matrix.mulVec ];
        obtain ⟨ x, hx₁, hx₂ ⟩ := hc₁; specialize this ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from by intro h; simp_all +decide [ Finsupp.ext_iff ] ) ; simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ;
      obtain ⟨ c, hc₀, hc ⟩ := h_cont_pos_def; use c; refine' ⟨ hc₀, fun v => _ ⟩ ; by_cases hv : v = 0 <;> simp_all +decide [ Matrix.mulVec ] ;
      convert mul_le_mul_of_nonneg_right ( hc ( fun i => v i / Real.sqrt ( ∑ i, v i ^ 2 ) ) ?_ ) ( show 0 ≤ ∑ i, v i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) using 1;
      · simp +decide [ div_eq_inv_mul, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
        simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← sq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, hv ];
        rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt <| lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Ne.symm <| by contrapose! hv; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ), mul_one ];
      · norm_num [ div_pow, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
        rw [ ← Finset.sum_div, div_self <| ne_of_gt <| lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Ne.symm <| by contrapose! hv; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ];
  -- Since $c > 0$, we have $\|v\|^2 \leq \frac{M}{c}$ for all $v \in S$.
  have h_bound : ∀ v : Fin n → ℤ, (v ⬝ᵥ F *ᵥ v) ≤ M → ∀ i, (v i : ℝ) ^ 2 ≤ M / c := by
    intro v hv i;
    rw [ le_div_iff₀' hc_pos ];
    refine' le_trans _ ( Int.cast_le.mpr hv );
    convert le_trans _ ( hc ( fun i => v i ) ) using 1;
    · simp +decide [ Matrix.mulVec, dotProduct ];
    · exact mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => sq_nonneg ( v i : ℝ ) ) ( Finset.mem_univ i ) ) hc_pos.le;
  -- Since $c > 0$, we have $|v_i| \leq \sqrt{\frac{M}{c}}$ for all $i$.
  have h_abs_bound : ∀ v : Fin n → ℤ, (v ⬝ᵥ F *ᵥ v) ≤ M → ∀ i, |v i| ≤ Nat.ceil (Real.sqrt (M / c)) := by
    intro v hv i; specialize h_bound v hv i; exact_mod_cast ( show |( v i : ℝ )| ≤ ⌈Real.sqrt ( M / c ) ⌉₊ from le_trans ( Real.abs_le_sqrt <| by simpa using h_bound ) <| Nat.le_ceil _ ) ;
  exact Set.Finite.subset ( Set.finite_Icc _ _ ) fun v hv => ⟨ fun i => neg_le_of_abs_le ( h_abs_bound v hv i ), fun i => le_of_abs_le ( h_abs_bound v hv i ) ⟩

/-- Integer vectors whose real positive-definite matrix value is bounded
above form a finite set.

This is the real-matrix analogue of
`finite_int_vectors_bounded_quadForm`, used in the Hermite normal-form setup
to choose an integral minimum vector before the rank-induction step. -/
lemma _root_.Matrix.finite_int_vectors_bounded_dotProduct_mulVec
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) (M : ℝ) :
    Set.Finite { v : Fin n → ℤ |
      (let vℝ : Fin n → ℝ := fun i => (v i : ℝ)
       vℝ ⬝ᵥ S.mulVec vℝ) ≤ M } := by
  obtain ⟨c, hc_pos, hc⟩ :
      ∃ c > 0, ∀ v : Fin n → ℝ,
        (v ⬝ᵥ S.mulVec v) ≥ c * (Finset.sum Finset.univ fun i => v i ^ 2) := by
    by_cases hn : n = 0
    · subst hn
      use 1
      norm_num
    · have h_cont_pos_def :
          ∃ c > 0, ∀ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 →
            (v ⬝ᵥ S.mulVec v) ≥ c := by
        have h_compact : IsCompact {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1} := by
          refine' (Metric.isCompact_iff_isClosed_bounded.mpr _)
          exact ⟨isClosed_eq
              (continuous_finset_sum _ fun _ _ => Continuous.pow (continuous_apply _) _)
              continuous_const,
            isBounded_iff_forall_norm_le.mpr ⟨1, by
              rintro v (hv : ∑ i, v i ^ 2 = 1)
              exact pi_norm_le_iff_of_nonneg (by norm_num) |>.2 fun i => by
                simpa [hv] using
                  Real.abs_le_sqrt
                    (Finset.single_le_sum (fun i _ => sq_nonneg (v i))
                      (Finset.mem_univ i))⟩⟩
        have h_min :
            ∃ c ∈
                (Set.image (fun v : Fin n → ℝ => v ⬝ᵥ S.mulVec v)
                  {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}),
              ∀ y ∈
                (Set.image (fun v : Fin n → ℝ => v ⬝ᵥ S.mulVec v)
                  {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}),
                c ≤ y := by
          apply_rules [IsCompact.exists_isLeast, h_compact]
          · exact h_compact.image <|
              Continuous.dotProduct continuous_id' <|
                Continuous.matrix_mulVec continuous_const continuous_id'
          · exact ⟨_,
              ⟨fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then 1 else 0,
                by norm_num, rfl⟩⟩
        obtain ⟨c, hc_mem, hc_min⟩ := h_min
        refine ⟨c, ?_, ?_⟩
        · rcases hc_mem with ⟨x, hx_norm, rfl⟩
          have hx_ne : x ≠ 0 := by
            intro hx
            simp [hx] at hx_norm
          exact hS.dotProduct_mulVec_pos hx_ne
        · intro v hv
          exact hc_min _ ⟨v, hv, rfl⟩
      obtain ⟨c, hc₀, hc⟩ := h_cont_pos_def
      use c
      refine' ⟨hc₀, fun v => _⟩
      by_cases hv : v = 0
      · simp [hv, Matrix.mulVec, dotProduct, hc₀.le]
      · let N : ℝ := ∑ i, v i ^ 2
        have hN_nonneg : 0 ≤ N := by
          exact Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hN_pos : 0 < N := by
          exact lt_of_le_of_ne hN_nonneg <| Ne.symm <| by
            contrapose! hv
            ext i
            simp_all +decide [N, Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg]
        have hunit :
            (∑ i, (fun i => v i / Real.sqrt N) i ^ 2) = 1 := by
          norm_num [div_pow, Real.sq_sqrt hN_nonneg]
          rw [← Finset.sum_div, div_self (ne_of_gt hN_pos)]
        have hscale :
            (((fun i => v i / Real.sqrt N) ⬝ᵥ
                S.mulVec (fun i => v i / Real.sqrt N)) * N) =
              v ⬝ᵥ S.mulVec v := by
          have hsqrt_ne : Real.sqrt N ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.mpr hN_pos)
          have hsqrt_sq : Real.sqrt N * Real.sqrt N = N := by
            rw [← pow_two, Real.sq_sqrt hN_nonneg]
          have hinvN : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N = 1 := by
            calc
              (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N =
                  (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ *
                    (Real.sqrt N * Real.sqrt N) := by rw [hsqrt_sq]
              _ =
                  ((Real.sqrt N)⁻¹ * Real.sqrt N) *
                    ((Real.sqrt N)⁻¹ * Real.sqrt N) := by ring
              _ = 1 := by
                rw [inv_mul_cancel₀ hsqrt_ne]
                ring
          have hscale_q :
              ((fun i => v i / Real.sqrt N) ⬝ᵥ
                  S.mulVec (fun i => v i / Real.sqrt N)) =
                (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ *
                  (v ⬝ᵥ S.mulVec v) := by
            simp +decide [div_eq_inv_mul, Matrix.mulVec, dotProduct,
              Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
          calc
            ((fun i => v i / Real.sqrt N) ⬝ᵥ
                S.mulVec (fun i => v i / Real.sqrt N)) * N =
                ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N) *
                  (v ⬝ᵥ S.mulVec v) := by
              rw [hscale_q]
              ring
            _ = v ⬝ᵥ S.mulVec v := by
              rw [hinvN]
              ring
        calc
          c * N ≤
              ((fun i => v i / Real.sqrt N) ⬝ᵥ
                S.mulVec (fun i => v i / Real.sqrt N)) * N :=
            mul_le_mul_of_nonneg_right
              (hc (fun i => v i / Real.sqrt N) hunit) hN_nonneg
          _ = v ⬝ᵥ S.mulVec v := hscale
  have h_bound : ∀ v : Fin n → ℤ,
      (let vℝ : Fin n → ℝ := fun i => (v i : ℝ)
       vℝ ⬝ᵥ S.mulVec vℝ) ≤ M →
      ∀ i, (v i : ℝ) ^ 2 ≤ M / c := by
    intro v hv i
    rw [le_div_iff₀' hc_pos]
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ => sq_nonneg (v i : ℝ)) (Finset.mem_univ i))
        hc_pos.le)
      (le_trans (hc (fun i => (v i : ℝ))) hv)
  have h_abs_bound : ∀ v : Fin n → ℤ,
      (let vℝ : Fin n → ℝ := fun i => (v i : ℝ)
       vℝ ⬝ᵥ S.mulVec vℝ) ≤ M →
      ∀ i, |v i| ≤ Nat.ceil (Real.sqrt (M / c)) := by
    intro v hv i
    specialize h_bound v hv i
    exact_mod_cast
      (show |(v i : ℝ)| ≤ ⌈Real.sqrt (M / c)⌉₊ from
        le_trans (Real.abs_le_sqrt <| by simpa using h_bound) <| Nat.le_ceil _)
  exact Set.Finite.subset (Set.finite_Icc _ _) fun v hv =>
    ⟨fun i => neg_le_of_abs_le (h_abs_bound v hv i),
      fun i => le_of_abs_le (h_abs_bound v hv i)⟩

/-- A positive-rank real positive-definite matrix has an integral nonzero
vector attaining the minimum of `xᵀ S x` among nonzero integral vectors. -/
lemma _root_.Matrix.exists_dotProduct_mulVec_int_minimum_value
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hn : 0 < n) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) = μ ∧
      ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤
        (let yℝ : Fin n → ℝ := fun i => (y i : ℝ)
         yℝ ⬝ᵥ S.mulVec yℝ) := by
  classical
  let x₀ : Fin n → ℤ := fun i => if i = ⟨0, hn⟩ then 1 else 0
  have hx₀ : x₀ ≠ 0 := by
    intro h
    have := congr_fun h ⟨0, hn⟩
    simp [x₀] at this
  let q : (Fin n → ℤ) → ℝ := fun x =>
    let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
    xℝ ⬝ᵥ S.mulVec xℝ
  let M : ℝ := q x₀
  let T : Set (Fin n → ℤ) := {x | x ≠ 0 ∧ q x ≤ M}
  have hT_finite : T.Finite := by
    exact (Matrix.finite_int_vectors_bounded_dotProduct_mulVec S hS M).subset (by
      intro x hx
      exact hx.2)
  have hT_nonempty : T.Nonempty := ⟨x₀, hx₀, le_rfl⟩
  obtain ⟨x, hxT, hx_min⟩ := Set.exists_min_image T q hT_finite hT_nonempty
  have hxℝ_ne : (fun i : Fin n => (x i : ℝ)) ≠ 0 := by
    intro hx
    apply hxT.1
    ext i
    exact Int.cast_eq_zero.mp (congr_fun hx i)
  have hq_pos : 0 < q x := by
    simpa [q] using hS.dotProduct_mulVec_pos hxℝ_ne
  refine ⟨q x, hq_pos, x, hxT.1, rfl, ?_⟩
  intro y hy
  by_cases hy_bound : q y ≤ M
  · exact hx_min y ⟨hy, hy_bound⟩
  · exact le_trans hxT.2 (le_of_lt (lt_of_not_ge hy_bound))

/-- For a positive-definite integral form, there are finitely many integer
matrices whose pullback of the form equals any fixed target matrix. -/
lemma finite_matrices_preserving_form_to_fixed_target
    (L : PositiveDefiniteIntegralLattice n) (T : Matrix (Fin n) (Fin n) ℤ) :
    Set.Finite {U : Matrix (Fin n) (Fin n) ℤ |
      U.transpose * L.pairingMatrix * U = T} := by
  have hfiniteColumns : ∀ j : Fin n, Set.Finite
      {v : Fin n → ℤ |
        dotProduct v (L.pairingMatrix.mulVec v) = T j j} := by
    intro j
    exact (finite_int_vectors_bounded_quadForm L.pairingMatrix L.form_posDef (T j j)).subset
      fun _ hv ↦ hv.le
  have hfiniteMatrices : Set.Finite
      {U : Matrix (Fin n) (Fin n) ℤ |
        ∀ j : Fin n,
          dotProduct (fun i ↦ U i j)
            (L.pairingMatrix.mulVec (fun i ↦ U i j)) = T j j} := by
    have hpi : Set.Finite (Set.pi Set.univ fun j : Fin n ↦
        {v : Fin n → ℤ |
          dotProduct v (L.pairingMatrix.mulVec v) = T j j}) :=
      Set.Finite.pi fun j ↦ hfiniteColumns j
    refine' Set.Finite.subset (hpi.preimage _) _
    use fun U j i ↦ U i j
    · exact fun U _ V _ hUV ↦ by
        ext i j
        simpa using congrFun (congrFun hUV j) i
    · exact fun U hU j _ ↦ hU j
  refine hfiniteMatrices.subset ?_
  intro U hU j
  simpa [Matrix.mul_assoc] using congrFun (congrFun hU j) j

/-
The set of integer matrices preserving a positive-definite form is finite.

**Proof**: Apply the fixed-target theorem with the original form matrix as the
target.
-/
lemma finite_form_preserving_matrices (L : PositiveDefiniteIntegralLattice n) :
    Set.Finite { U : Matrix (Fin n) (Fin n) ℤ | Uᵀ * L.pairingMatrix * U = L.pairingMatrix } :=
  finite_matrices_preserving_form_to_fixed_target L L.pairingMatrix

/-! ## Isometry group finiteness -/

/-
The integral isometry group of a positive-definite lattice is finite.

This is the content of the compact-definite argument in Schulze-Pillot
(lines 7103–7106): the real orthogonal group `O(F_ℝ)` is compact and the
arithmetic stabilizer `O(F) = O(F_ℝ) ∩ GLₙ(ℤ)` is a discrete subgroup
of a compact group, hence finite.
-/
theorem isometryGroup_finite (L : PositiveDefiniteIntegralLattice n) : Finite L.IsometryGroup := by
  exact Set.Finite.subset ( finite_form_preserving_matrices L ) fun U hU => hU.2

/-
The proper integral isometry group is finite (immediate from
`isometryGroup_finite` since `ProperIsometryGroup` is a subtype of
`IsometryGroup`).
-/
theorem properIsometryGroup_finite (L : PositiveDefiniteIntegralLattice n) :
    Finite L.ProperIsometryGroup := by
  refine' Set.Finite.subset ( Set.finite_coe_iff.mpr ( finite_form_preserving_matrices L ) ) _;
  exact fun U hU => hU.1.2

/-- The ordinary integral isometry group can be used as a `Fintype`, as needed
for finite sums in the mass formula. -/
noncomputable instance isometryGroup_fintype (L : PositiveDefiniteIntegralLattice n) :
    Fintype L.IsometryGroup := by
  letI : Finite L.IsometryGroup := isometryGroup_finite L
  exact Fintype.ofFinite L.IsometryGroup

/-- The proper integral isometry group can be used as a `Fintype`, as needed
for the proper mass formula. -/
noncomputable instance properIsometryGroup_fintype (L : PositiveDefiniteIntegralLattice n) :
    Fintype L.ProperIsometryGroup := by
  letI : Finite L.ProperIsometryGroup := properIsometryGroup_finite L
  exact Fintype.ofFinite L.ProperIsometryGroup

/-- The ordinary integral isometry group is nonempty: it contains the identity
isometry. -/
lemma isometryGroup_card_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < Fintype.card L.IsometryGroup := by
  exact Fintype.card_pos_iff.mpr ⟨⟨1, by simp [IsIsometry]⟩⟩

/-- The proper integral isometry group is nonempty: it contains the identity
isometry. -/
lemma properIsometryGroup_card_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < Fintype.card L.ProperIsometryGroup := by
  exact Fintype.card_pos_iff.mpr ⟨⟨1, by simp [IsProperIsometry, IsIsometry]⟩⟩

/-- A finite set of lattice representatives meeting every global isometry class
in a set of classes gives finiteness of that class set. -/
lemma global_isometry_classes_finite_of_finite_representatives
    {S : Set (Set (PositiveDefiniteIntegralLattice n))}
    {representatives : Set (PositiveDefiniteIntegralLattice n)}
    (hrepresentatives_finite : representatives.Finite)
    (hrepresentatives :
      ∀ C ∈ S, ∃ L ∈ representatives, C = L.globalIsometryClass) :
    S.Finite := by
  refine Set.Finite.subset (hrepresentatives_finite.image globalIsometryClass) ?_
  intro C hC
  obtain ⟨L, hL_mem, hC⟩ := hrepresentatives C hC
  exact ⟨L, hL_mem, hC.symm⟩

/-- A finite submodule has only finitely many submodules contained in it. -/
lemma finite_submodules_le_of_finite
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {B : Submodule R M} (hB : (B : Set M).Finite) :
    Set.Finite { C : Submodule R M | C ≤ B } := by
  refine Set.Finite.of_injOn (f := fun C : Submodule R M => (C : Set M))
    ?_ ?_ hB.finite_subsets
  · intro C hC
    exact hC
  · intro C _ D _ hCD
    ext x
    exact Set.ext_iff.mp hCD x

/-- If `A ≤ B` and the image of `B` in the quotient `M ⧸ A` is finite, then
there are only finitely many intermediate submodules `C` with `A ≤ C ≤ B`.

This is the abstract finite-index ingredient in Schulze--Pillot's overlattice
step: once a lattice is known to lie between a fixed lattice and a finite-index
overlattice, the possible intermediate lattices form a finite set. -/
lemma finite_intermediate_submodules_of_finite_quotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A B : Submodule R M} (_hAB : A ≤ B)
    (hquot : ((B.map A.mkQ : Submodule R (M ⧸ A)) : Set (M ⧸ A)).Finite) :
    Set.Finite { C : Submodule R M | A ≤ C ∧ C ≤ B } := by
  let toQuotient (C : Submodule R M) : Submodule R (M ⧸ A) := C.map A.mkQ
  have hfinite_image :
      Set.Finite { Q : Submodule R (M ⧸ A) | Q ≤ B.map A.mkQ } :=
    finite_submodules_le_of_finite hquot
  refine Set.Finite.of_injOn (f := toQuotient) ?_ ?_ hfinite_image
  · intro C hC
    exact Submodule.map_mono hC.2
  · intro C hC D hD hmap
    have hC_comap : (toQuotient C).comap A.mkQ = C := by
      rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hC.1]
    have hD_comap : (toQuotient D).comap A.mkQ = D := by
      rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hD.1]
    have hcomap := congrArg (fun Q : Submodule R (M ⧸ A) => Q.comap A.mkQ) hmap
    change (toQuotient C).comap A.mkQ = (toQuotient D).comap A.mkQ at hcomap
    rwa [hC_comap, hD_comap] at hcomap

/-- If `A ≤ B ≤ Ω` and the image of the fixed overmodule `Ω` in `M ⧸ A`
is finite, then there are only finitely many submodules `C` with `A ≤ C ≤ B`.

This is the form needed for Schulze--Pillot's fixed sandwich
`M ⊥ N ⊆ Λ ⊆ M# ⊥ N#`: once the upper quotient is finite, any smaller
family of intermediate lattices below the upper overmodule is finite. -/
lemma finite_intermediate_submodules_of_finite_overmodule_quotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A B Ω : Submodule R M} (hAB : A ≤ B) (hBΩ : B ≤ Ω)
    (hquot : ((Ω.map A.mkQ : Submodule R (M ⧸ A)) : Set (M ⧸ A)).Finite) :
    Set.Finite { C : Submodule R M | A ≤ C ∧ C ≤ B } := by
  have hBquot : ((B.map A.mkQ : Submodule R (M ⧸ A)) : Set (M ⧸ A)).Finite :=
    hquot.subset (by
      intro x hx
      exact Submodule.map_mono hBΩ hx)
  exact finite_intermediate_submodules_of_finite_quotient hAB hBquot

/-- If both components have finite quotient image, then their join has finite
quotient image modulo the join of the lower components.

This is the split-overmodule bookkeeping needed for the full
Schulze--Pillot sandwich: the line component gives one finite quotient, while
the orthogonal-complement dual contributes a second finite quotient. -/
lemma finite_quotient_image_sup_of_finite_quotient_images
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A B C D : Submodule R M}
    (hB : ((B.map A.mkQ : Submodule R (M ⧸ A)) : Set (M ⧸ A)).Finite)
    (hD : ((D.map C.mkQ : Submodule R (M ⧸ C)) : Set (M ⧸ C)).Finite) :
    (((B ⊔ D).map (A ⊔ C).mkQ :
        Submodule R (M ⧸ (A ⊔ C))) : Set (M ⧸ (A ⊔ C))).Finite := by
  let q : M →ₗ[R] M ⧸ (A ⊔ C) := (A ⊔ C).mkQ
  let φA : M ⧸ A →ₗ[R] M ⧸ (A ⊔ C) :=
    A.mapQ (A ⊔ C) LinearMap.id (by
      intro x hx
      exact (le_sup_left : A ≤ A ⊔ C) hx)
  let φC : M ⧸ C →ₗ[R] M ⧸ (A ⊔ C) :=
    C.mapQ (A ⊔ C) LinearMap.id (by
      intro x hx
      exact (le_sup_right : C ≤ A ⊔ C) hx)
  have hBq : ((B.map q : Submodule R (M ⧸ (A ⊔ C))) :
      Set (M ⧸ (A ⊔ C))).Finite := by
    refine (hB.image φA).subset ?_
    rintro y ⟨b, hb, rfl⟩
    exact ⟨A.mkQ b, ⟨b, hb, rfl⟩, rfl⟩
  have hDq : ((D.map q : Submodule R (M ⧸ (A ⊔ C))) :
      Set (M ⧸ (A ⊔ C))).Finite := by
    refine (hD.image φC).subset ?_
    rintro y ⟨d, hd, rfl⟩
    exact ⟨C.mkQ d, ⟨d, hd, rfl⟩, rfl⟩
  let sums : Set (M ⧸ (A ⊔ C)) :=
    (fun p : (M ⧸ (A ⊔ C)) × (M ⧸ (A ⊔ C)) => p.1 + p.2) ''
      (((B.map q : Submodule R (M ⧸ (A ⊔ C))) :
        Set (M ⧸ (A ⊔ C))) ×ˢ
      ((D.map q : Submodule R (M ⧸ (A ⊔ C))) :
        Set (M ⧸ (A ⊔ C))))
  have hsums : sums.Finite := (hBq.prod hDq).image
    (fun p : (M ⧸ (A ⊔ C)) × (M ⧸ (A ⊔ C)) => p.1 + p.2)
  refine hsums.subset ?_
  intro y hy
  rcases hy with ⟨m, hm, rfl⟩
  change m ∈ B ⊔ D at hm
  rw [Submodule.mem_sup] at hm
  rcases hm with ⟨b, hb, d, hd, hbd⟩
  refine ⟨(q b, q d), ?_, ?_⟩
  · exact ⟨⟨b, hb, rfl⟩, ⟨d, hd, rfl⟩⟩
  · rw [← hbd]
    simp [q]

/-! ### Coordinate-submodule reconstruction data -/

/-- A full-rank coordinate submodule of `ℤ^n` admits a basis indexed by
`Fin n`.

This is the first algebraic input for turning a coordinate-overmodule
candidate in Schulze--Pillot's fixed-index sandwich into an actual based
quadratic lattice: once the candidate has full rank, Mathlib's Smith normal
form over the PID `ℤ` supplies a square basis. -/
lemma exists_basis_of_full_rank_integral_coordinate_submodule
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) :
    Nonempty (Module.Basis (Fin n) ℤ B) := by
  have hB_rank : Module.finrank ℤ B = Module.finrank ℤ (Fin n → ℤ) := by
    simpa using hB
  obtain ⟨_bM, _a, bB, _hdiag⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq
      (N := B) (Pi.basisFun ℤ (Fin n)) hB_rank
  exact ⟨bB⟩

/-- A chosen square basis of a full-rank coordinate submodule. -/
noncomputable def fullRankCoordinateSubmoduleBasis
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) :
    Module.Basis (Fin n) ℤ B :=
  Classical.choice (exists_basis_of_full_rank_integral_coordinate_submodule B hB)

/-- The matrix whose columns are the chosen basis vectors of a full-rank
coordinate submodule, expressed in the ambient standard coordinates. -/
noncomputable def fullRankCoordinateSubmoduleBasisMatrix
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((fullRankCoordinateSubmoduleBasis B hB j : B) : Fin n → ℤ) i

/-- Every column of the chosen basis matrix lies in the coordinate submodule it
was chosen from. -/
lemma fullRankCoordinateSubmoduleBasisMatrix_col_mem
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) (j : Fin n) :
    (fun i => fullRankCoordinateSubmoduleBasisMatrix B hB i j) ∈ B := by
  change (((fullRankCoordinateSubmoduleBasis B hB j : B) : Fin n → ℤ)) ∈ B
  exact (fullRankCoordinateSubmoduleBasis B hB j).property

/-- Multiplication by the chosen basis matrix is the same as expanding the
coordinate vector in the chosen basis of the full-rank coordinate submodule,
then forgetting from the submodule to the ambient coordinate lattice. -/
lemma fullRankCoordinateSubmoduleBasisMatrix_mulVec_eq
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) (z : Fin n → ℤ) :
    (fullRankCoordinateSubmoduleBasisMatrix B hB).mulVec z =
      ((fullRankCoordinateSubmoduleBasis B hB).equivFun.symm z : B) := by
  ext i
  simp [fullRankCoordinateSubmoduleBasisMatrix, Matrix.mulVec,
    Module.Basis.equivFun_symm_apply, dotProduct, mul_comm]

/-- The chosen basis matrix for a full-rank coordinate submodule has image
exactly that coordinate submodule.

This is the submodule-identification half of the final coordinate
reconstruction step: once a reconstructed overlattice is expressed through a
coordinate basis matrix, this lemma identifies the matrix image with the
candidate coordinate submodule in the fixed sandwich. -/
lemma fullRankCoordinateSubmoduleBasisMatrix_range_eq
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) :
    LinearMap.range (Matrix.toLin' (fullRankCoordinateSubmoduleBasisMatrix B hB)) =
      B := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    have hz_mem :
        (fullRankCoordinateSubmoduleBasisMatrix B hB).mulVec z ∈ B := by
      rw [fullRankCoordinateSubmoduleBasisMatrix_mulVec_eq]
      exact ((fullRankCoordinateSubmoduleBasis B hB).equivFun.symm z).property
    simpa [Matrix.toLin'_apply, hz.symm] using hz_mem
  · intro hy
    let b := fullRankCoordinateSubmoduleBasis B hB
    refine ⟨b.equivFun ⟨y, hy⟩, ?_⟩
    simp [Matrix.toLin'_apply, fullRankCoordinateSubmoduleBasisMatrix_mulVec_eq,
      b]

/-- The chosen basis matrix of a full-rank coordinate submodule is injective
on integral coordinate vectors. -/
lemma fullRankCoordinateSubmoduleBasisMatrix_mulVec_ne_zero
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) {z : Fin n → ℤ} (hz : z ≠ 0) :
    (fullRankCoordinateSubmoduleBasisMatrix B hB).mulVec z ≠ 0 := by
  intro hzero
  let b := fullRankCoordinateSubmoduleBasis B hB
  have hb_zero : b.equivFun.symm z = 0 := by
    apply Subtype.ext
    simpa [b, fullRankCoordinateSubmoduleBasisMatrix_mulVec_eq B hB z] using hzero
  apply hz
  have hz_zero := congrArg b.equivFun hb_zero
  rw [b.equivFun.apply_symm_apply, map_zero] at hz_zero
  exact hz_zero

/-- The chosen basis matrix of a full-rank coordinate submodule has nonzero
determinant. -/
lemma fullRankCoordinateSubmoduleBasisMatrix_det_ne_zero
    (B : Submodule ℤ (Fin n → ℤ))
    (hB : Module.finrank ℤ B = n) :
    (fullRankCoordinateSubmoduleBasisMatrix B hB).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz_ne, hz_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact fullRankCoordinateSubmoduleBasisMatrix_mulVec_ne_zero B hB hz_ne hz_zero

/-- Pull back the quadratic matrix of `L` along a rectangular complement
matrix.

This is the matrix carried by the primitive orthogonal complement once a
source or a normal-form construction supplies integer columns spanning
`x⊥`. -/
noncomputable def complementMatrixPulledFormMatrix
    (L : PositiveDefiniteIntegralLattice n) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ :=
  Cᵀ * L.pairingMatrix * C

/-- The rectangular pulled-back complement matrix is symmetric. -/
lemma complementMatrixPulledFormMatrix_symm
    (L : PositiveDefiniteIntegralLattice n) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    (complementMatrixPulledFormMatrix L C).IsSymm := by
  change (Cᵀ * L.pairingMatrix * C).IsSymm
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  have htranspose : (Cᵀ * L.pairingMatrix * C)ᵀ = Cᵀ * L.pairingMatrix * C := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      L.form_symm.eq]
    simp [Matrix.mul_assoc]
  exact congr_fun (congr_fun htranspose i) j

/-- If the real column map of a rectangular complement matrix is injective,
then the pulled-back complement matrix is positive definite. -/
lemma complementMatrixPulledFormMatrix_posDef
    (L : PositiveDefiniteIntegralLattice n) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hC_inj : Function.Injective ((C.map (Int.cast : ℤ → ℝ)).mulVec)) :
    ((complementMatrixPulledFormMatrix L C).map
      (Int.cast : ℤ → ℝ)).PosDef := by
  let Cℝ : Matrix (Fin n) (Fin (n - 1)) ℝ := C.map (Int.cast : ℤ → ℝ)
  have hpos := L.form_posDef.conjTranspose_mul_mul_same (B := Cℝ) hC_inj
  change ((Cᵀ * L.pairingMatrix * C).map (Int.cast : ℤ → ℝ)).PosDef
  convert hpos using 1
  ext i j
  simp [Cℝ, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The positive integral lattice obtained by pulling `L` back to an
injective rectangular complement matrix.

For the primitive-complement determinant step, this formalizes the
lattice-construction part once the complement columns have been supplied.
What remains is the existence of a full
orthogonal complement matrix and the determinant relation. -/
noncomputable def complementLatticeOfMatrix
    (L : PositiveDefiniteIntegralLattice n) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hC_inj : Function.Injective ((C.map (Int.cast : ℤ → ℝ)).mulVec)) :
    PositiveDefiniteIntegralLattice (n - 1) where
  pairingMatrix := complementMatrixPulledFormMatrix L C
  form_symm := complementMatrixPulledFormMatrix_symm L C
  form_posDef := complementMatrixPulledFormMatrix_posDef L C hC_inj

/-- The complement lattice constructed from a rectangular matrix has the
expected pulled-back form matrix. -/
lemma complementLatticeOfMatrix_pairingMatrix
    (L : PositiveDefiniteIntegralLattice n) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hC_inj : Function.Injective ((C.map (Int.cast : ℤ → ℝ)).mulVec)) :
    (complementLatticeOfMatrix L C hC_inj).pairingMatrix =
      Cᵀ * L.pairingMatrix * C := rfl

/-- The set of integral vectors with bounded value under the lattice
quadratic form is finite. -/
lemma finite_vectors_bounded_quadForm (L : PositiveDefiniteIntegralLattice n) (M : ℤ) :
    Set.Finite { x : Fin n → ℤ | L.quadForm x ≤ M } := by
  simpa [quadForm_eq_dotProduct]
    using finite_int_vectors_bounded_quadForm L.pairingMatrix L.form_posDef M

/-- In positive rank there exists a nonzero integral vector. -/
lemma exists_nonzero_vector_of_pos_rank (hn : 0 < n) :
    ∃ x : Fin n → ℤ, x ≠ 0 := by
  refine ⟨fun i => if i = ⟨0, hn⟩ then 1 else 0, ?_⟩
  intro h
  have := congr_fun h ⟨0, hn⟩
  simp at this

/-- In positive rank the positive-definite integral quadratic form has a
minimal nonzero vector.  This is the formal starting point for the
Schulze--Pillot/Hermite minimum bound used in class-number finiteness. -/
lemma exists_quadForm_minimizer (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      ∀ y : Fin n → ℤ, y ≠ 0 → L.quadForm x ≤ L.quadForm y := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_nonzero_vector_of_pos_rank (n := n) hn
  let M : ℤ := L.quadForm x₀
  let S : Set (Fin n → ℤ) := { x | x ≠ 0 ∧ L.quadForm x ≤ M }
  have hS_finite : S.Finite := by
    exact (finite_vectors_bounded_quadForm L M).subset (by
      intro x hx
      exact hx.2)
  have hS_nonempty : S.Nonempty := ⟨x₀, hx₀, le_rfl⟩
  obtain ⟨x, hxS, hx_min⟩ := Set.exists_min_image S L.quadForm hS_finite hS_nonempty
  refine ⟨x, hxS.1, ?_⟩
  intro y hy
  by_cases hy_bound : L.quadForm y ≤ M
  · exact hx_min y ⟨hy, hy_bound⟩
  · exact le_trans hxS.2 (le_of_lt (lt_of_not_ge hy_bound))

/-- In positive rank the positive-definite integral quadratic form has a
positive minimum value on nonzero integral vectors. -/
lemma exists_quadForm_minimum_value (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) :
    ∃ μ : ℤ, 0 < μ ∧ ∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
      ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y := by
  obtain ⟨x, hx, hx_min⟩ := exists_quadForm_minimizer L hn
  exact ⟨L.quadForm x, L.quadForm_pos hx, x, hx, rfl, hx_min⟩

/-- The explicit Hermite real bound used by Schulze--Pillot for a positive
rank `n` positive definite form of Schulze--Pillot determinant `d = det(F)`.

This is `(4 / 3)^((n - 1) / 2) * d^(1 / n)`, with real powers.  It is a
separate definition so that the theorem below records the mathematical
constant, while later finiteness arguments can round it up to an integer. -/
def hermiteShortVectorRealBound (n : ℕ) (d : ℤ) : ℝ :=
  Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
    Real.rpow (d : ℝ) ((n : ℝ)⁻¹)

/-- The explicit Hermite real bound is positive for positive determinant. -/
lemma hermiteShortVectorRealBound_pos (n : ℕ) (d : ℤ) (hd : 0 < d) :
    0 < hermiteShortVectorRealBound n d := by
  dsimp [hermiteShortVectorRealBound]
  positivity

/-- Integer rounding to the interval `[-1 / 2, 1 / 2]`, in the form used by
Siegel's inductive proof of Hermite's estimate when choosing the first
coordinate after fixing the remaining coordinates. -/
lemma exists_int_add_mem_Icc_neg_half_half (r : ℝ) :
    ∃ z : ℤ, -(1 / 2 : ℝ) ≤ (z : ℝ) + r ∧ (z : ℝ) + r ≤ (1 / 2 : ℝ) := by
  refine ⟨round (-r), ?_⟩
  have hround : |(-r) - (round (-r) : ℝ)| ≤ (1 / 2 : ℝ) :=
    abs_sub_round (-r)
  have hrewrite : |(round (-r) : ℝ) + r| = |(-r) - (round (-r) : ℝ)| := by
    rw [abs_sub_comm]
    ring_nf
  exact abs_le.mp (by simpa [hrewrite] using hround)

/-- The rank-one Schur complement of a `Unit ⊕ m` block decomposition,
written entrywise in Siegel's notation.

This identifies Mathlib's `D - C * A⁻¹ * B` convention with the lower block
`S₁ - q s₁⁻¹ qᵀ` used in the inductive proof of Hermite's estimate. -/
lemma _root_.Matrix.schurComplement_sum_inr_apply {m : Type*}
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (i j : m) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
    (D - C * A⁻¹ * B) i j =
      S (Sum.inr i) (Sum.inr j) -
        S (Sum.inr i) (Sum.inl ()) * (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
          S (Sum.inl ()) (Sum.inr j) := by
  dsimp only
  simp [Matrix.mul_apply, Finset.univ_unique]

/-- Completed-square expansion for the `Unit ⊕ m` block decomposition used in
Siegel's inductive proof of Hermite's estimate.

With `W = S₁ - q s₁⁻¹ qᵀ`, this is the coordinate identity
`S[x] = s₁ (x₁ + s₁⁻¹ qᵀ y)^2 + W[y]`. -/
lemma _root_.Matrix.dotProduct_mulVec_sum_schurComplement_inr {m : Type*}
    [Fintype m] (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ)
    (hS_symm : S.IsSymm) (hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0)
    (x₁ : ℝ) (y : m → ℝ) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
    let W : Matrix m m ℝ := D - C * A⁻¹ * B
    let x : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => x₁) y
    x ⬝ᵥ S.mulVec x =
      S (Sum.inl ()) (Sum.inl ()) *
          (x₁ + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            (∑ j, S (Sum.inl ()) (Sum.inr j) * y j)) ^ 2 +
        y ⬝ᵥ W.mulVec y := by
  dsimp only
  have hsymm : ∀ i : m, S (Sum.inr i) (Sum.inl ()) = S (Sum.inl ()) (Sum.inr i) := by
    intro i
    simpa using (hS_symm.apply (Sum.inr i) (Sum.inl ())).symm
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.mul_apply,
    Finset.univ_unique, hsymm, hs, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    sub_eq_add_neg, pow_two]
  field_simp [hs]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_assoc, mul_left_comm, mul_comm]
  have htail :
      ((∑ i, ∑ j,
          y i * y j * S (Sum.inl ()) (Sum.inr i) *
            S (Sum.inl ()) (Sum.inr j) *
              (S (Sum.inl ()) (Sum.inl ()))⁻¹) -
        (∑ i, ∑ j,
          (S (Sum.inl ()) (Sum.inl ()))⁻¹ * y i * y j *
            S (Sum.inl ()) (Sum.inr i) *
              S (Sum.inl ()) (Sum.inr j))) = 0 := by
    rw [sub_eq_zero]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  nlinarith [htail]

/-- After the nearest-integer choice in Siegel's induction proof, the
completed-square identity gives the elementary bound
`S[x] ≤ s₁ / 4 + W[y]`.

This isolates the real inequality step used in the formal Hermite induction:
the only inputs are the completed-square identity, positivity of the
distinguished diagonal entry, and the rounded coordinate lying in
`[-1 / 2, 1 / 2]`. -/
lemma _root_.Matrix.dotProduct_mulVec_sum_schurComplement_inr_le_of_half_bound {m : Type*}
    [Fintype m] (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ)
    (hS_symm : S.IsSymm) (hs_pos : 0 < S (Sum.inl ()) (Sum.inl ()))
    (x₁ : ℝ) (y : m → ℝ)
    (hround :
      -(1 / 2 : ℝ) ≤
          x₁ + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            (∑ j, S (Sum.inl ()) (Sum.inr j) * y j) ∧
        x₁ + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            (∑ j, S (Sum.inl ()) (Sum.inr j) * y j) ≤ (1 / 2 : ℝ)) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
    let W : Matrix m m ℝ := D - C * A⁻¹ * B
    let x : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => x₁) y
    x ⬝ᵥ S.mulVec x ≤
      S (Sum.inl ()) (Sum.inl ()) / 4 + y ⬝ᵥ W.mulVec y := by
  dsimp only
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
  let W : Matrix m m ℝ := D - C * A⁻¹ * B
  let x : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => x₁) y
  let t : ℝ :=
    x₁ + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
      (∑ j, S (Sum.inl ()) (Sum.inr j) * y j)
  have ht_sq : t ^ 2 ≤ (1 / 4 : ℝ) := by
    have ht_low : -(1 / 2 : ℝ) ≤ t := by
      simpa [t] using hround.1
    have ht_high : t ≤ (1 / 2 : ℝ) := by
      simpa [t] using hround.2
    nlinarith [sq_nonneg (t - (1 / 2 : ℝ)), sq_nonneg (t + (1 / 2 : ℝ))]
  have hmul :
      S (Sum.inl ()) (Sum.inl ()) * t ^ 2 ≤
        S (Sum.inl ()) (Sum.inl ()) * (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left ht_sq hs_pos.le
  have hs_ne : S (Sum.inl ()) (Sum.inl ()) ≠ 0 := ne_of_gt hs_pos
  have hidentity :=
    Matrix.dotProduct_mulVec_sum_schurComplement_inr S hS_symm hs_ne x₁ y
  calc
    x ⬝ᵥ S.mulVec x =
        S (Sum.inl ()) (Sum.inl ()) * t ^ 2 + y ⬝ᵥ W.mulVec y := by
      simpa [A, B, C, D, W, x, t] using hidentity
    _ ≤ S (Sum.inl ()) (Sum.inl ()) * (1 / 4 : ℝ) + y ⬝ᵥ W.mulVec y :=
      by linarith
    _ = S (Sum.inl ()) (Sum.inl ()) / 4 + y ⬝ᵥ W.mulVec y := by
      ring

/-- Siegel's one-step Hermite comparison after choosing a lower-block short
vector.

Assume the first diagonal entry is the matrix minimum `μ`, and assume `y` is
a nonzero integral vector in the Schur-complement lower block with value at
most `R`.  Rounding the distinguished coordinate and applying the completed
square estimate gives
`μ ≤ μ / 4 + R`.

This is the formal bridge between the lower-rank Hermite witness for `W` and
the displayed inequality on p. 33 of Siegel's lectures. -/
lemma _root_.Matrix.hermite_one_step_bound_of_lower_short_vector {m : Type*}
    [Fintype m] (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ)
    (hS_symm : S.IsSymm) (hs_pos : 0 < S (Sum.inl ()) (Sum.inl ()))
    (μ R : ℝ) (hdiag : S (Sum.inl ()) (Sum.inl ()) = μ)
    (hmin :
      ∀ x : Unit ⊕ m → ℤ, x ≠ 0 →
        μ ≤
          (let xℝ : Unit ⊕ m → ℝ := fun i => (x i : ℝ)
           xℝ ⬝ᵥ S.mulVec xℝ))
    (y : m → ℤ) (hy_ne : y ≠ 0)
    (hy_bound :
      (let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
       let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
       let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
       let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
       let W : Matrix m m ℝ := D - C * A⁻¹ * B
       let yℝ : m → ℝ := fun i => (y i : ℝ)
       yℝ ⬝ᵥ W.mulVec yℝ) ≤ R) :
    μ ≤ μ / 4 + R := by
  classical
  let yℝ : m → ℝ := fun i => (y i : ℝ)
  obtain ⟨z, hz⟩ :=
    PositiveDefiniteIntegralLattice.exists_int_add_mem_Icc_neg_half_half
      ((S (Sum.inl ()) (Sum.inl ()))⁻¹ *
        (∑ j, S (Sum.inl ()) (Sum.inr j) * yℝ j))
  let xℤ : Unit ⊕ m → ℤ := Sum.elim (fun _ : Unit => z) y
  have hx_ne : xℤ ≠ 0 := by
    intro hx
    apply hy_ne
    ext i
    exact congr_fun hx (Sum.inr i)
  have hμ_le :
      μ ≤
        (let xℝ : Unit ⊕ m → ℝ := fun i => (xℤ i : ℝ)
         xℝ ⬝ᵥ S.mulVec xℝ) :=
    hmin xℤ hx_ne
  have hround :
      -(1 / 2 : ℝ) ≤
          (z : ℝ) + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            (∑ j, S (Sum.inl ()) (Sum.inr j) * yℝ j) ∧
        (z : ℝ) + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            (∑ j, S (Sum.inl ()) (Sum.inr j) * yℝ j) ≤ (1 / 2 : ℝ) := by
    simpa [add_comm, add_left_comm, add_assoc] using hz
  have hhalf :=
    Matrix.dotProduct_mulVec_sum_schurComplement_inr_le_of_half_bound
      S hS_symm hs_pos (z : ℝ) yℝ hround
  have hxℝ_eq :
      (fun i : Unit ⊕ m => (xℤ i : ℝ)) =
        Sum.elim (fun _ : Unit => (z : ℝ)) yℝ := by
    ext i
    cases i <;> rfl
  calc
    μ ≤
        (let xℝ : Unit ⊕ m → ℝ := fun i => (xℤ i : ℝ)
         xℝ ⬝ᵥ S.mulVec xℝ) := hμ_le
    _ ≤
        S (Sum.inl ()) (Sum.inl ()) / 4 +
          (let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
           let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
           let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
           let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
           let W : Matrix m m ℝ := D - C * A⁻¹ * B
           let yℝ : m → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ W.mulVec yℝ) := by
      dsimp only
      rw [hxℝ_eq]
      simpa [yℝ] using hhalf
    _ = μ / 4 +
          (let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
           let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
           let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
           let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
           let W : Matrix m m ℝ := D - C * A⁻¹ * B
           let yℝ : m → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ W.mulVec yℝ) := by
      rw [hdiag]
    _ ≤ μ / 4 + R := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hy_bound (μ / 4)

/-- The Schur-complement lower block in Siegel's Hermite induction is positive
definite.

If `S` is positive definite in the `Unit ⊕ m` block decomposition, then the
rank-one Schur complement `W = D - C * A⁻¹ * B` is positive definite.  This is
the formal version of the source step `W > 0`, needed before applying the
lower-rank Hermite hypothesis to the lower block. -/
theorem _root_.Matrix.PosDef.schurComplement_sum_inr {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
    (D - C * A⁻¹ * B).PosDef := by
  dsimp only
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
  let W : Matrix m m ℝ := D - C * A⁻¹ * B
  have hS_symm : S.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    simpa using hS.isHermitian.apply i j
  have hs_pos : 0 < S (Sum.inl ()) (Sum.inl ()) := by
    let e : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : m => 0)
    have he : e ≠ 0 := by
      intro he
      have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
      norm_num [e] at h
    have hpos := hS.dotProduct_mulVec_pos (x := e) he
    simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos
  have hs_ne : S (Sum.inl ()) (Sum.inl ()) ≠ 0 := ne_of_gt hs_pos
  have hW_herm : W.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    have hD : S (Sum.inr j) (Sum.inr i) = S (Sum.inr i) (Sum.inr j) :=
      hS_symm.apply (Sum.inr i) (Sum.inr j)
    have hCi : S (Sum.inr i) (Sum.inl ()) = S (Sum.inl ()) (Sum.inr i) :=
      hS_symm.apply (Sum.inl ()) (Sum.inr i)
    have hCj : S (Sum.inr j) (Sum.inl ()) = S (Sum.inl ()) (Sum.inr j) :=
      hS_symm.apply (Sum.inl ()) (Sum.inr j)
    simp [W, A, B, C, D, Matrix.mul_apply, Finset.univ_unique, hD, hCi, hCj,
      mul_comm, mul_left_comm, mul_assoc]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hW_herm ?_
  intro y hy
  let q : ℝ :=
    (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
      (∑ j, S (Sum.inl ()) (Sum.inr j) * y j)
  let x : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => -q) y
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hy
    ext i
    exact congr_fun hx (Sum.inr i)
  have hpos : 0 < x ⬝ᵥ S.mulVec x := by
    simpa [x] using hS.dotProduct_mulVec_pos (x := x) hx_ne
  have hidentity :=
    Matrix.dotProduct_mulVec_sum_schurComplement_inr S hS_symm hs_ne (-q) y
  have hx_eq : x ⬝ᵥ S.mulVec x = y ⬝ᵥ W.mulVec y := by
    calc
      x ⬝ᵥ S.mulVec x =
          S (Sum.inl ()) (Sum.inl ()) *
            (-q + (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
              (∑ j, S (Sum.inl ()) (Sum.inr j) * y j)) ^ 2 +
            y ⬝ᵥ W.mulVec y := by
        simpa [A, B, C, D, W, x, q] using hidentity
      _ = y ⬝ᵥ W.mulVec y := by
        simp [q]
  rw [hx_eq] at hpos
  simpa [W, A, B, C, D] using hpos

/-- Schur-complement determinant formula for the `Unit ⊕ m` block split used
in Siegel's induction proof of Hermite's estimate.

If the distinguished diagonal entry `s₁` is nonzero, then
`det S = s₁ * det W`, where `W` is Mathlib's Schur complement of the
distinguished rank-one block. -/
lemma _root_.Matrix.det_sum_schurComplement_inr {m : Type*} [Fintype m] [DecidableEq m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ)
    (hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
    S.det = S (Sum.inl ()) (Sum.inl ()) * (D - C * A⁻¹ * B).det := by
  dsimp only
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
  have hdetA : IsUnit A.det := by
    simpa [A, Matrix.det_fin_one] using (isUnit_iff_ne_zero.mpr hs)
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hdetA
  have hS_blocks : S = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  calc
    S.det = (Matrix.fromBlocks A B C D).det := by rw [hS_blocks]
    _ = A.det * (D - C * ⅟A * B).det := by
      exact Matrix.det_fromBlocks₁₁ A B C D
    _ = A.det * (D - C * A⁻¹ * B).det := by
      rw [Matrix.invOf_eq_nonsing_inv]
    _ = S (Sum.inl ()) (Sum.inl ()) * (D - C * A⁻¹ * B).det := by
      simp [A]

/-- The rank-one Hermite short-vector inequality is elementary.

For rank one, the vector with coordinate `1` has quadratic value equal to the
single matrix entry, hence to `pairingDeterminant`.  The explicit Hermite constant is
also exactly `d` in rank one. -/
theorem fixed_rank_one_positive_pairingDeterminant_hermite_real_bound
    (d : ℤ) (_hd : 0 < d) :
    ∀ L : PositiveDefiniteIntegralLattice 1, L.pairingDeterminant = d →
      ∃ x : Fin 1 → ℤ, x ≠ 0 ∧
        (L.quadForm x : ℝ) ≤ hermiteShortVectorRealBound 1 d := by
  intro L hdet
  let x : Fin 1 → ℤ := fun _ => 1
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have h : x 0 = (0 : ℤ) := congr_fun hx 0
    norm_num [x] at h
  · have hquad : L.quadForm x = d := by
      calc
        L.quadForm x = dotProduct x (L.pairingMatrix.mulVec x) :=
          L.quadForm_eq_dotProduct x
        _ = L.pairingMatrix 0 0 := by
          simp [x, dotProduct, Matrix.mulVec]
        _ = L.pairingDeterminant := by
          simp [pairingDeterminant, Matrix.det_fin_one]
        _ = d := hdet
    have hbound : hermiteShortVectorRealBound 1 d = (d : ℝ) := by
      norm_num [hermiteShortVectorRealBound, Real.rpow_zero, Real.rpow_one]
    rw [hquad, hbound]

/-- The rank-one Hermite matrix inequality is elementary. -/
theorem hermite_positive_definite_matrix_short_vector_bound_rank_one
    (S : Matrix (Fin 1) (Fin 1) ℝ)
    (_hS_symm : S.IsSymm) (_hS_pos : S.PosDef) :
    ∃ x : Fin 1 → ℤ, x ≠ 0 ∧
      (let xℝ : Fin 1 → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) ≤
        Real.rpow (4 / 3 : ℝ) (((1 : ℝ) - 1) / 2) *
          Real.rpow S.det ((1 : ℝ)⁻¹) := by
  let x : Fin 1 → ℤ := fun _ => 1
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have h : x 0 = (0 : ℤ) := congr_fun hx 0
    norm_num [x] at h
  · have hquad :
        (let xℝ : Fin 1 → ℝ := fun i => (x i : ℝ)
         xℝ ⬝ᵥ S.mulVec xℝ) = S 0 0 := by
      simp [x, dotProduct, Matrix.mulVec]
    have hbound :
        Real.rpow (4 / 3 : ℝ) (((1 : ℝ) - 1) / 2) *
            Real.rpow S.det ((1 : ℝ)⁻¹) = S 0 0 := by
      norm_num [Matrix.det_fin_one, Real.rpow_one]
    rw [hquad, hbound]

/-- Feed an explicitly supplied lower-rank Hermite witness theorem for the
Schur complement into Siegel's one-step comparison.

After block-decomposing a positive definite matrix as `Unit ⊕ Fin k`, the
Schur complement `W = D - C * A⁻¹ * B` is positive definite.  Applying the
given rank-`k` Hermite theorem to `W` and then using
`Matrix.hermite_one_step_bound_of_lower_short_vector` gives the displayed
one-step inequality
`μ ≤ μ / 4 + c_k * det(W)^(1/k)`.

This is the induction-hypothesis form of the Schur-complement step. -/
lemma _root_.Matrix.hermite_one_step_bound_of_schurComplement_of_lower_rank_bound
    {k : ℕ} (_hk : 0 < k)
    (hlower :
      ∀ W : Matrix (Fin k) (Fin k) ℝ, W.IsSymm → W.PosDef →
        ∃ y : Fin k → ℤ, y ≠ 0 ∧
          (let yℝ : Fin k → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ W.mulVec yℝ) ≤
            Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
              Real.rpow W.det ((k : ℝ)⁻¹))
    (S : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef)
    (μ : ℝ) (hdiag : S (Sum.inl ()) (Sum.inl ()) = μ)
    (hmin :
      ∀ x : Unit ⊕ Fin k → ℤ, x ≠ 0 →
        μ ≤
          (let xℝ : Unit ⊕ Fin k → ℝ := fun i => (x i : ℝ)
           xℝ ⬝ᵥ S.mulVec xℝ)) :
    let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
    let B : Matrix Unit (Fin k) ℝ := S.submatrix Sum.inl Sum.inr
    let C : Matrix (Fin k) Unit ℝ := S.submatrix Sum.inr Sum.inl
    let D : Matrix (Fin k) (Fin k) ℝ := S.submatrix Sum.inr Sum.inr
    let W : Matrix (Fin k) (Fin k) ℝ := D - C * A⁻¹ * B
    μ ≤ μ / 4 +
      Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
        Real.rpow W.det ((k : ℝ)⁻¹) := by
  classical
  dsimp only
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit (Fin k) ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix (Fin k) Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix (Fin k) (Fin k) ℝ := S.submatrix Sum.inr Sum.inr
  let W : Matrix (Fin k) (Fin k) ℝ := D - C * A⁻¹ * B
  have hs_pos : 0 < S (Sum.inl ()) (Sum.inl ()) := by
    let e : Unit ⊕ Fin k → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : Fin k => 0)
    have he : e ≠ 0 := by
      intro he
      have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
      norm_num [e] at h
    have hpos := hS_pos.dotProduct_mulVec_pos (x := e) he
    simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos
  have hW_pos : W.PosDef := by
    simpa [A, B, C, D, W] using
      Matrix.PosDef.schurComplement_sum_inr S hS_pos
  have hW_symm : W.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    simpa using hW_pos.isHermitian.apply i j
  let R : ℝ :=
    Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
      Real.rpow W.det ((k : ℝ)⁻¹)
  obtain ⟨y, hy_ne, hy_bound⟩ := hlower W hW_symm hW_pos
  exact Matrix.hermite_one_step_bound_of_lower_short_vector
    S hS_symm hs_pos μ R hdiag hmin y hy_ne
      (by simpa [A, B, C, D, W, R] using hy_bound)

/-- The elementary real recurrence algebra in Siegel's Hermite induction.

From the one-step inequality
`μ ≤ μ / 4 + (4 / 3)^((k - 1) / 2) * δ^(1 / k)`, Lean derives
`μ ≤ (4 / 3)^((k + 1) / 2) * δ^(1 / k)`.  This is the formal
`3 / 4` rearrangement and Hermite-constant exponent shift; the next
formal Hermite-induction step is the determinant substitution from
`det(S) = μ * δ` to the rank-`k + 1` bound. -/
lemma _root_.Matrix.hermite_recurrence_bound_of_one_step {k : ℕ} {μ δ : ℝ}
    (hstep :
      μ ≤ μ / 4 +
        Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
          Real.rpow δ ((k : ℝ)⁻¹)) :
    μ ≤
      Real.rpow (4 / 3 : ℝ) (((k : ℝ) + 1) / 2) *
        Real.rpow δ ((k : ℝ)⁻¹) := by
  let T : ℝ :=
    Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
      Real.rpow δ ((k : ℝ)⁻¹)
  have hT : (3 / 4 : ℝ) * μ ≤ T := by
    nlinarith [hstep]
  have hμ_le : μ ≤ (4 / 3 : ℝ) * T := by
    nlinarith [hT]
  have hbase_pos : 0 < (4 / 3 : ℝ) := by norm_num
  have hpow :
      Real.rpow (4 / 3 : ℝ) (1 + (((k : ℝ) - 1) / 2)) =
        (4 / 3 : ℝ) * Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) := by
    change (4 / 3 : ℝ) ^ (1 + (((k : ℝ) - 1) / 2)) =
      (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ (((k : ℝ) - 1) / 2)
    rw [Real.rpow_add hbase_pos]
    simp [Real.rpow_one]
  calc
    μ ≤ (4 / 3 : ℝ) * T := hμ_le
    _ = Real.rpow (4 / 3 : ℝ) (1 + (((k : ℝ) - 1) / 2)) *
          Real.rpow δ ((k : ℝ)⁻¹) := by
      simp only [T]
      rw [hpow]
      ring
    _ = Real.rpow (4 / 3 : ℝ) (((k : ℝ) + 1) / 2) *
          Real.rpow δ ((k : ℝ)⁻¹) := by
      congr 1
      ring_nf

/-- The determinant/rpow substitution at the end of Siegel's Hermite
induction step.

After the recurrence gives
`μ ≤ (4 / 3)^((k + 1) / 2) * δ^(1 / k)` and the block determinant identity
gives `Δ = μ * δ`, this proves the rank-`k + 1` Hermite bound
`μ ≤ (4 / 3)^(k / 2) * Δ^(1 / (k + 1))`. -/
lemma _root_.Matrix.hermite_rank_succ_bound_of_recurrence_and_det
    {k : ℕ} {μ δ Δ : ℝ} (hk : 0 < k) (hμ : 0 < μ) (hδ : 0 < δ)
    (hΔ : Δ = μ * δ)
    (hrec :
      μ ≤ Real.rpow (4 / 3 : ℝ) (((k : ℝ) + 1) / 2) *
        Real.rpow δ ((k : ℝ)⁻¹)) :
    μ ≤ Real.rpow (4 / 3 : ℝ) ((k : ℝ) / 2) *
      Real.rpow Δ (((k : ℝ) + 1)⁻¹) := by
  let c : ℝ := 4 / 3
  let α : ℝ := (k : ℝ) / ((k : ℝ) + 1)
  let β : ℝ := ((k : ℝ) + 1)⁻¹
  have hc_pos : 0 < c := by norm_num [c]
  have hα_nonneg : 0 ≤ α := by positivity
  have hμ_nonneg : 0 ≤ μ := hμ.le
  have hδ_nonneg : 0 ≤ δ := hδ.le
  have hA_nonneg : 0 ≤ c ^ (((k : ℝ) + 1) / 2) :=
    (Real.rpow_pos_of_pos hc_pos _).le
  have hδpow_nonneg : 0 ≤ δ ^ ((k : ℝ)⁻¹) :=
    Real.rpow_nonneg hδ_nonneg _
  have hpow := Real.rpow_le_rpow hμ_nonneg hrec hα_nonneg
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hμ_nonneg β)
  have hleft : μ ^ α * μ ^ β = μ := by
    rw [← Real.rpow_add hμ α β]
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
    rw [hαβ, Real.rpow_one]
  have hright :
      (c ^ (((k : ℝ) + 1) / 2) * δ ^ ((k : ℝ)⁻¹)) ^ α * μ ^ β =
        c ^ ((k : ℝ) / 2) * Δ ^ β := by
    rw [Real.mul_rpow hA_nonneg hδpow_nonneg]
    rw [← Real.rpow_mul hc_pos.le]
    rw [← Real.rpow_mul hδ_nonneg]
    have hAexp : (((k : ℝ) + 1) / 2) * α = (k : ℝ) / 2 := by
      dsimp [α]
      field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
    have hDexp : (k : ℝ)⁻¹ * α = β := by
      dsimp [α, β]
      field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hk),
        show (k : ℝ) + 1 ≠ 0 by positivity]
    rw [hAexp, hDexp]
    rw [hΔ]
    rw [Real.mul_rpow hμ_nonneg hδ_nonneg]
    ring
  calc
    μ = μ ^ α * μ ^ β := hleft.symm
    _ ≤ (Real.rpow (4 / 3 : ℝ) (((k : ℝ) + 1) / 2) *
            Real.rpow δ ((k : ℝ)⁻¹)) ^ α * μ ^ β := hmul
    _ = Real.rpow c ((k : ℝ) / 2) * Real.rpow Δ β := by
      simpa [c] using hright
    _ = Real.rpow (4 / 3 : ℝ) ((k : ℝ) / 2) *
          Real.rpow Δ (((k : ℝ) + 1)⁻¹) := by
      rfl

/-- The assembled matrix induction step in Siegel's Hermite proof with an
explicit lower-rank Hermite hypothesis.

For a positive definite matrix in `Unit ⊕ Fin k` block form, if the
distinguished diagonal entry is the matrix minimum `μ`, then the already
formal Schur-complement witness from the supplied rank-`k` theorem, recurrence rearrangement,
Schur-complement determinant formula, and final rpow substitution give the
rank-`k + 1` Hermite bound for `μ`.

This is the induction-hypothesis form of the block step. -/
lemma _root_.Matrix.hermite_rank_succ_bound_of_schurComplement_of_lower_rank_bound
    {k : ℕ} (hk : 0 < k)
    (hlower :
      ∀ W : Matrix (Fin k) (Fin k) ℝ, W.IsSymm → W.PosDef →
        ∃ y : Fin k → ℤ, y ≠ 0 ∧
          (let yℝ : Fin k → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ W.mulVec yℝ) ≤
            Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
              Real.rpow W.det ((k : ℝ)⁻¹))
    (S : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef)
    (μ : ℝ) (hdiag : S (Sum.inl ()) (Sum.inl ()) = μ)
    (hmin :
      ∀ x : Unit ⊕ Fin k → ℤ, x ≠ 0 →
        μ ≤
          (let xℝ : Unit ⊕ Fin k → ℝ := fun i => (x i : ℝ)
           xℝ ⬝ᵥ S.mulVec xℝ)) :
    μ ≤ Real.rpow (4 / 3 : ℝ) ((k : ℝ) / 2) *
      Real.rpow S.det (((k : ℝ) + 1)⁻¹) := by
  classical
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit (Fin k) ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix (Fin k) Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix (Fin k) (Fin k) ℝ := S.submatrix Sum.inr Sum.inr
  let W : Matrix (Fin k) (Fin k) ℝ := D - C * A⁻¹ * B
  have hs_pos : 0 < S (Sum.inl ()) (Sum.inl ()) := by
    let e : Unit ⊕ Fin k → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : Fin k => 0)
    have he : e ≠ 0 := by
      intro he
      have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
      norm_num [e] at h
    have hpos := hS_pos.dotProduct_mulVec_pos (x := e) he
    simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos
  have hμ_pos : 0 < μ := by
    simpa [hdiag] using hs_pos
  have hW_pos : W.PosDef := by
    simpa [A, B, C, D, W] using
      Matrix.PosDef.schurComplement_sum_inr S hS_pos
  have hW_det_pos : 0 < W.det := hW_pos.det_pos
  have hstep :
      μ ≤ μ / 4 +
        Real.rpow (4 / 3 : ℝ) (((k : ℝ) - 1) / 2) *
          Real.rpow W.det ((k : ℝ)⁻¹) := by
    simpa [A, B, C, D, W] using
      Matrix.hermite_one_step_bound_of_schurComplement_of_lower_rank_bound
        hk hlower S hS_symm hS_pos μ hdiag hmin
  have hrec :
      μ ≤ Real.rpow (4 / 3 : ℝ) (((k : ℝ) + 1) / 2) *
        Real.rpow W.det ((k : ℝ)⁻¹) :=
    Matrix.hermite_recurrence_bound_of_one_step hstep
  have hdet : S.det = μ * W.det := by
    have hs_ne : S (Sum.inl ()) (Sum.inl ()) ≠ 0 := ne_of_gt hs_pos
    simpa [A, B, C, D, W, hdiag] using
      Matrix.det_sum_schurComplement_inr S hs_ne
  exact Matrix.hermite_rank_succ_bound_of_recurrence_and_det
    hk hμ_pos hW_det_pos hdet hrec

/-- Symmetry is preserved by an integral basis-change congruence after casting
the basis matrix to `ℝ`.

This is one of the matrix-normal-form transport facts needed to apply the
`Unit ⊕ Fin k` Hermite block lemma after moving an arbitrary minimum vector to
a distinguished coordinate. -/
lemma _root_.Matrix.IsSymm.basis_change_intCast
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSymm)
    (P : Matrix (Fin n) (Fin n) ℤ) :
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))).IsSymm := by
  rw [Matrix.IsSymm]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, hS.eq]

/-- Positive definiteness is preserved by an integral unimodular
basis-change congruence after casting the basis matrix to `ℝ`. -/
lemma _root_.Matrix.PosDef.basis_change_intCast_of_isUnit
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (P : Matrix (Fin n) (Fin n) ℤ) (hP : IsUnit P) :
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))).PosDef := by
  have hP_real : IsUnit (P.map (Int.cast : ℤ → ℝ)) := by
    exact hP.map (RingHom.mapMatrix (Int.castRingHom ℝ))
  have hpos :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff
      (x := S) hP_real).2 hS
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.mul_assoc]
    using hpos

/-- A unimodular integral basis-change congruence preserves the real
determinant after casting the basis matrix to `ℝ`. -/
lemma _root_.Matrix.det_basis_change_intCast_of_isUnit
    (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℤ) (hP : IsUnit P) :
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))).det = S.det := by
  let Pℝ : Matrix (Fin n) (Fin n) ℝ := P.map (Int.cast : ℤ → ℝ)
  have hdetP_unit : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP
  have hdetP_sq : Pℝ.det * Pℝ.det = (1 : ℝ) := by
    rcases Int.isUnit_iff.mp hdetP_unit with hdet | hdet
    · simp [Pℝ, ← Int.cast_det, hdet]
    · simp [Pℝ, ← Int.cast_det, hdet]
  calc
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))).det =
        Pℝ.det * S.det * Pℝ.det := by
      simp [Pℝ, Matrix.det_mul, Matrix.det_transpose, Matrix.mul_assoc]
      ring
    _ = S.det := by
      calc
        Pℝ.det * S.det * Pℝ.det = (Pℝ.det * Pℝ.det) * S.det := by ring
        _ = S.det := by simp [hdetP_sq]

/-- Quadratic values are transported by an integral basis-change congruence
after casting the basis matrix to `ℝ`. -/
lemma _root_.Matrix.dotProduct_mulVec_basis_change_intCast
    (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
     zℝ ⬝ᵥ
       (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ))).mulVec zℝ)) =
      (let Pzℝ : Fin n → ℝ := fun i => (P.mulVec z i : ℝ)
       Pzℝ ⬝ᵥ S.mulVec Pzℝ) := by
  let Pℝ : Matrix (Fin n) (Fin n) ℝ := P.map (Int.cast : ℤ → ℝ)
  let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
  let Pzℝ : Fin n → ℝ := fun i => (P.mulVec z i : ℝ)
  have hPz : Pℝ.mulVec zℝ = Pzℝ := by
    ext i
    simp [Pℝ, zℝ, Pzℝ, Matrix.mulVec, dotProduct]
  calc
    zℝ ⬝ᵥ ((Pℝᵀ * S * Pℝ).mulVec zℝ)
        = (zℝ ᵥ* (Pℝᵀ * S * Pℝ)) ⬝ᵥ zℝ := by
          rw [dotProduct_mulVec]
    _ = (((zℝ ᵥ* Pℝᵀ) ᵥ* S) ᵥ* Pℝ) ⬝ᵥ zℝ := by
          simp [Matrix.mul_assoc]
    _ = ((Pℝ *ᵥ zℝ) ᵥ* S) ⬝ᵥ (Pℝ *ᵥ zℝ) := by
          rw [← dotProduct_mulVec]
          rw [vecMul_transpose]
    _ = Pzℝ ⬝ᵥ S.mulVec Pzℝ := by
          rw [hPz]
          exact (dotProduct_mulVec Pzℝ S Pzℝ).symm

/-- A matrix minimum inequality transports through an integral unimodular
basis-change congruence. -/
lemma _root_.Matrix.minimum_le_basis_change_intCast_of_isUnit
    (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℤ) (hP : IsUnit P) (μ : ℝ)
    (hmin :
      ∀ x : Fin n → ℤ, x ≠ 0 →
        μ ≤
          (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
           xℝ ⬝ᵥ S.mulVec xℝ)) :
    ∀ z : Fin n → ℤ, z ≠ 0 →
      μ ≤
        (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
         zℝ ⬝ᵥ
           (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
              (P.map (Int.cast : ℤ → ℝ))).mulVec zℝ)) := by
  intro z hz
  have hPz_ne : P.mulVec z ≠ 0 := by
    have hinj : Function.Injective P.mulVec :=
      Matrix.mulVec_injective_of_isUnit hP
    intro hPz
    apply hz
    exact hinj (by simpa using hPz)
  calc
    μ ≤
        (let Pzℝ : Fin n → ℝ := fun i => (P.mulVec z i : ℝ)
         Pzℝ ⬝ᵥ S.mulVec Pzℝ) :=
      hmin (P.mulVec z) hPz_ne
    _ =
        (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
         zℝ ⬝ᵥ
           (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
              (P.map (Int.cast : ℤ → ℝ))).mulVec zℝ)) :=
      (Matrix.dotProduct_mulVec_basis_change_intCast S P z).symm

/-- The distinguished diagonal entry after a basis change is the original
quadratic value of the corresponding basis vector. -/
lemma _root_.Matrix.basis_change_intCast_apply_self_eq_quadratic_of_mulVec
    (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (x : Fin n → ℤ)
    (hx : P.mulVec ((Pi.basisFun ℤ (Fin n)) j) = x) :
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))) j j =
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) := by
  let e : Fin n → ℤ := (Pi.basisFun ℤ (Fin n)) j
  have htransport := Matrix.dotProduct_mulVec_basis_change_intCast S P e
  have he_left :
      (let eℝ : Fin n → ℝ := fun i => (e i : ℝ)
       eℝ ⬝ᵥ
         (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
            (P.map (Int.cast : ℤ → ℝ))).mulVec eℝ)) =
        ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ))) j j := by
    let A : Matrix (Fin n) (Fin n) ℝ :=
      (P.map (Int.cast : ℤ → ℝ))ᵀ * S * (P.map (Int.cast : ℤ → ℝ))
    change (∑ a, (e a : ℝ) * (∑ b, A a b * (e b : ℝ))) = A j j
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single j]
      · simp [e]
      · intro b _ hb
        simp [e, Pi.single_eq_of_ne hb]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro a _ ha
      simp [e, Pi.single_eq_of_ne ha]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  have he_right :
      (let Peℝ : Fin n → ℝ := fun i => (P.mulVec e i : ℝ)
       Peℝ ⬝ᵥ S.mulVec Peℝ) =
        (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
         xℝ ⬝ᵥ S.mulVec xℝ) := by
    subst x
    rfl
  calc
    ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
        (P.map (Int.cast : ℤ → ℝ))) j j =
        (let eℝ : Fin n → ℝ := fun i => (e i : ℝ)
         eℝ ⬝ᵥ
           (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
              (P.map (Int.cast : ℤ → ℝ))).mulVec eℝ)) := he_left.symm
    _ =
        (let Peℝ : Fin n → ℝ := fun i => (P.mulVec e i : ℝ)
         Peℝ ⬝ᵥ S.mulVec Peℝ) := htransport
    _ =
        (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
         xℝ ⬝ᵥ S.mulVec xℝ) := he_right

/-- Symmetry is preserved when a square matrix is reindexed by an equivalence. -/
lemma _root_.Matrix.IsSymm.submatrix_equiv
    {α β : Type*} (S : Matrix α α ℝ) (e : β ≃ α) (hS : S.IsSymm) :
    (S.submatrix e e).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  simpa [Matrix.submatrix] using congr_fun (congr_fun hS.eq (e i)) (e j)

/-- Quadratic values are unchanged by reindexing both rows and columns by an
equivalence. -/
lemma _root_.Matrix.dotProduct_mulVec_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (x : β → ℝ) :
    x ⬝ᵥ (S.submatrix e e).mulVec x =
      (fun a : α => x (e.symm a)) ⬝ᵥ
        S.mulVec (fun a : α => x (e.symm a)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix]
  conv_rhs =>
    rw [← Equiv.sum_comp e
      (fun a : α => x (e.symm a) * ∑ b : α, S a b * x (e.symm b))]
  simp only [Equiv.symm_apply_apply]
  congr
  ext i
  rw [← Equiv.sum_comp e (fun b : α => S (e i) b * x (e.symm b))]
  simp

/-- Positive definiteness is preserved when a square real matrix is reindexed by
an equivalence. -/
lemma _root_.Matrix.PosDef.submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (hS : S.PosDef) :
    (S.submatrix e e).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hS.isHermitian.submatrix e) ?_
  intro x hx
  let y : α → ℝ := fun a => x (e.symm a)
  have hy_ne : y ≠ 0 := by
    intro hy
    apply hx
    ext b
    have hb := congr_fun hy (e b)
    simpa [y] using hb
  have hpos := hS.dotProduct_mulVec_pos (x := y) hy_ne
  change 0 < x ⬝ᵥ (S.submatrix e e).mulVec x
  rw [Matrix.dotProduct_mulVec_submatrix_equiv S e x]
  change 0 < y ⬝ᵥ S.mulVec y
  simpa [y] using hpos

/-- Integral quadratic values are unchanged by reindexing both rows and columns
by an equivalence. -/
lemma _root_.Matrix.dotProduct_mulVec_submatrix_equiv_int
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (x : β → ℤ) :
    (let xℝ : β → ℝ := fun i => (x i : ℝ)
     xℝ ⬝ᵥ (S.submatrix e e).mulVec xℝ) =
      (let yℝ : α → ℝ := fun i => (x (e.symm i) : ℝ)
       yℝ ⬝ᵥ S.mulVec yℝ) := by
  exact Matrix.dotProduct_mulVec_submatrix_equiv S e (fun i : β => (x i : ℝ))

/-- In rank one, the quadratic matrix is determined by its determinant. -/
lemma rank_one_pairingMatrix_eq_of_pairingDeterminant_eq {L L' : PositiveDefiniteIntegralLattice 1}
    (hdet : L.pairingDeterminant = L'.pairingDeterminant) :
    L.pairingMatrix = L'.pairingMatrix := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [pairingDeterminant, Matrix.det_fin_one] using hdet

/-- In rank one, a positive-definite integral lattice is determined by
`pairingDeterminant`. -/
lemma rank_one_eq_of_pairingDeterminant_eq {L L' : PositiveDefiniteIntegralLattice 1}
    (hdet : L.pairingDeterminant = L'.pairingDeterminant) : L = L' := by
  obtain ⟨F, hsym, hpos⟩ := L
  obtain ⟨F', hsym', hpos'⟩ := L'
  have hF : F = F' := rank_one_pairingMatrix_eq_of_pairingDeterminant_eq hdet
  cases hF
  congr

/-- The fixed-determinant isometry-class set is finite in rank one.  Indeed,
the single entry of a `1 × 1` quadratic matrix is its determinant, so a fixed
`pairingDeterminant` determines the based lattice itself. -/
theorem fixed_rank_one_pairingDeterminant_isometry_classes_finite (d : ℤ) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice 1) |
      ∃ L : PositiveDefiniteIntegralLattice 1, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  classical
  by_cases hnonempty : ∃ L : PositiveDefiniteIntegralLattice 1, L.pairingDeterminant = d
  · obtain ⟨L0, hL0⟩ := hnonempty
    refine Set.Finite.subset (Set.finite_singleton L0.globalIsometryClass) ?_
    intro C hC
    obtain ⟨L, hdet, rfl⟩ := hC
    have hL : L = L0 := rank_one_eq_of_pairingDeterminant_eq (hdet.trans hL0.symm)
    simp [hL]
  · have h_empty :
        { C : Set (PositiveDefiniteIntegralLattice 1) |
          ∃ L : PositiveDefiniteIntegralLattice 1, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } = ∅ := by
      ext C
      constructor
      · rintro ⟨L, hdet, hC⟩
        exact (hnonempty ⟨L, hdet⟩).elim
      · intro hC
        simp at hC
    simp [h_empty]

/-- A positive integer divisor of a fixed positive integer is bounded, hence
there are only finitely many positive integer divisors.  This is the elementary
finite-determinant step used in Schulze--Pillot's fixed-minimum induction: the
orthogonal complement has determinant dividing `μ * d`. -/
lemma finite_positive_int_divisors (N : ℤ) (hN : 0 < N) :
    Set.Finite { e : ℤ | 0 < e ∧ e ∣ N } := by
  have h_dvd_le : ∀ e : ℤ, 0 < e → e ∣ N → e ≤ N := by
    intro e he hdvd
    obtain ⟨k, rfl⟩ := hdvd
    have hk : 0 < k := by nlinarith [mul_pos_iff.mp hN]
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 : ℤ) ≤ k by omega) (le_of_lt he)]
  refine (Set.finite_Icc (1 : ℤ) N).subset ?_
  intro e he
  change 0 < e ∧ e ∣ N at he
  exact ⟨by omega, h_dvd_le e he.1 he.2⟩

/-- If fixed-`pairingDeterminant` class finiteness is known in a lower positive rank,
then the classes whose determinant ranges over a finite set of positive values
are finite. -/
theorem lower_rank_positive_pairingDeterminant_isometry_classes_finite_of_finite_det_set
    {m : ℕ}
    (hind : ∀ r : ℕ, 0 < r → r < n → ∀ e : ℤ, 0 < e →
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice r) |
        ∃ L : PositiveDefiniteIntegralLattice r, L.pairingDeterminant = e ∧ C = L.globalIsometryClass })
    (hm_pos : 0 < m) (hm_lt : m < n)
    {D : Set ℤ} (hD : D.Finite) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice m) |
      ∃ e ∈ D, 0 < e ∧
        ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = e ∧ C = L.globalIsometryClass } := by
  classical
  let classesOfDet (e : ℤ) : Set (Set (PositiveDefiniteIntegralLattice m)) :=
    { C : Set (PositiveDefiniteIntegralLattice m) |
      ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = e ∧ C = L.globalIsometryClass }
  have hclasses :
      (⋃ e ∈ D, { C : Set (PositiveDefiniteIntegralLattice m) |
        0 < e ∧ C ∈ classesOfDet e }).Finite := by
    refine hD.biUnion ?_
    intro e heD
    by_cases he : 0 < e
    · refine (hind m hm_pos hm_lt e he).subset ?_
      intro C hC
      exact by simpa [classesOfDet] using hC.2
    · have h_empty :
          { C : Set (PositiveDefiniteIntegralLattice m) |
            0 < e ∧ C ∈ classesOfDet e } = ∅ := by
        ext C
        constructor
        · intro hC
          exact (he hC.1).elim
        · intro hC
          simp at hC
      simp [h_empty]
  refine hclasses.subset ?_
  intro C hC
  obtain ⟨e, heD, he_pos, L, hdet, hclass⟩ := hC
  refine Set.mem_iUnion.2 ⟨e, ?_⟩
  refine Set.mem_iUnion.2 ⟨heD, ?_⟩
  exact ⟨he_pos, L, hdet, hclass⟩

/-- Under the lower-rank induction hypothesis, there are only finitely many
possible lower-rank isometry classes whose positive Schulze--Pillot determinant
divides the fixed positive integer `N`. -/
theorem lower_rank_positive_pairingDeterminant_isometry_classes_finite_of_det_divides
    {m : ℕ}
    (hind : ∀ r : ℕ, 0 < r → r < n → ∀ e : ℤ, 0 < e →
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice r) |
        ∃ L : PositiveDefiniteIntegralLattice r, L.pairingDeterminant = e ∧ C = L.globalIsometryClass })
    (hm_pos : 0 < m) (hm_lt : m < n)
    (N : ℤ) (hN : 0 < N) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice m) |
      ∃ e : ℤ, 0 < e ∧ e ∣ N ∧
        ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = e ∧ C = L.globalIsometryClass } := by
  let D : Set ℤ := { e : ℤ | 0 < e ∧ e ∣ N }
  have hD : D.Finite := finite_positive_int_divisors N hN
  refine (lower_rank_positive_pairingDeterminant_isometry_classes_finite_of_finite_det_set
    (n := n) hind hm_pos hm_lt hD).subset ?_
  intro C hC
  obtain ⟨e, he_pos, he_dvd, L, hdet, hclass⟩ := hC
  exact ⟨e, ⟨he_pos, he_dvd⟩, he_pos, L, hdet, hclass⟩


/-- Quadratic values are transported by an explicit matrix congruence.

This is the basic matrix algebra needed after replacing the standard
coordinates by a source-chosen basis in the fixed-index normal-form step. -/
lemma quadForm_eq_of_pairingMatrix_eq_basis_change
    (L L' : PositiveDefiniteIntegralLattice n) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : L'.pairingMatrix = Pᵀ * L.pairingMatrix * P)
    (z : Fin n → ℤ) :
    L'.quadForm z = L.quadForm (P.mulVec z) := by
  rw [L'.quadForm_eq_dotProduct, L.quadForm_eq_dotProduct, hmatrix]
  calc
    dotProduct z (((Pᵀ * L.pairingMatrix * P).mulVec z))
        = (z ᵥ* (Pᵀ * L.pairingMatrix * P)) ⬝ᵥ z := by
          rw [dotProduct_mulVec]
    _ = (((z ᵥ* Pᵀ) ᵥ* L.pairingMatrix) ᵥ* P) ⬝ᵥ z := by
          simp [Matrix.mul_assoc]
    _ = ((P *ᵥ z) ᵥ* L.pairingMatrix) ⬝ᵥ (P *ᵥ z) := by
          rw [← dotProduct_mulVec]
          rw [vecMul_transpose]
    _ = dotProduct (P.mulVec z) (L.pairingMatrix.mulVec (P.mulVec z)) := by
          exact (dotProduct_mulVec (P *ᵥ z) L.pairingMatrix (P *ᵥ z)).symm

/-- Schulze--Pillot bilinear values are transported by an explicit matrix
congruence.

Together with the quadratic version, this is the first comparison lemma for
the transformed primitive-line coordinates and the original fixed coordinate
sandwich. -/
lemma bilinearFormValue_eq_of_pairingMatrix_eq_basis_change
    (L L' : PositiveDefiniteIntegralLattice n) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : L'.pairingMatrix = Pᵀ * L.pairingMatrix * P)
    (x y : Fin n → ℤ) :
    L'.bilinearFormValue x y =
      L.bilinearFormValue (P.mulVec x) (P.mulVec y) := by
  rw [bilinearFormValue, bilinearFormValue, hmatrix]
  calc
    dotProduct x (((Pᵀ * L.pairingMatrix * P).mulVec y))
        = (x ᵥ* (Pᵀ * L.pairingMatrix * P)) ⬝ᵥ y := by
          rw [dotProduct_mulVec]
    _ = (((x ᵥ* Pᵀ) ᵥ* L.pairingMatrix) ᵥ* P) ⬝ᵥ y := by
          simp [Matrix.mul_assoc]
    _ = ((P *ᵥ x) ᵥ* L.pairingMatrix) ⬝ᵥ (P *ᵥ y) := by
          rw [← dotProduct_mulVec]
          rw [vecMul_transpose]
    _ = dotProduct (P.mulVec x) (L.pairingMatrix.mulVec (P.mulVec y)) := by
          exact (dotProduct_mulVec (P *ᵥ x) L.pairingMatrix (P *ᵥ y)).symm

/-- The Schulze--Pillot bilinear form `y ↦ B(x,y)` as a linear map in its
second argument. -/
def bilinearFormLinear (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  (dotProductBilin ℤ ℤ x).comp (Matrix.toLin' L.pairingMatrix)

@[simp]
lemma bilinearFormLinear_apply (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → ℤ) :
    L.bilinearFormLinear x y = L.bilinearFormValue x y := by
  simp [bilinearFormLinear, bilinearFormValue]

/-- The full `B`-orthogonal complement of a vector, as a submodule of the
ambient based lattice. -/
def bilinearOrthogonalSubmodule (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (L.bilinearFormLinear x)

/-- The integral lower sandwich generated by a minimum-vector line and its
full `B`-orthogonal complement.  This is Schulze--Pillot's lower lattice
`ℤx ⊥ x⊥` before embedding in the rational ambient space. -/
def lowerSandwichSubmodule (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ ({x} : Set (Fin n → ℤ)) ⊔ L.bilinearOrthogonalSubmodule x

@[simp]
lemma mem_bilinearOrthogonalSubmodule (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → ℤ) :
    y ∈ L.bilinearOrthogonalSubmodule x ↔ L.bilinearFormValue x y = 0 := by
  simp [bilinearOrthogonalSubmodule]

/-- Schulze--Pillot's bilinear form is linear in the second argument. -/
lemma bilinearFormValue_smul_right (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → ℤ) (r : ℤ) :
    L.bilinearFormValue x (r • y) = r * L.bilinearFormValue x y := by
  simp [bilinearFormValue, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

/-- The natural `ℤ`-linear embedding of the ambient based lattice into its
rational scalar extension. -/
def intVectorToRatLinear (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun x := fun i => (x i : ℚ)
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    simp

@[simp]
lemma intVectorToRatLinear_apply (x : Fin n → ℤ) (i : Fin n) :
    intVectorToRatLinear n x i = (x i : ℚ) := rfl

/-- The rational linear map induced by an integer matrix.  This is used to
transport the rational upper sandwich after changing integral coordinates. -/
def intMatrixRatLinear {m n : ℕ} (P : Matrix (Fin n) (Fin m) ℤ) :
    (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun v := (P.map (Int.cast : ℤ → ℚ)).mulVec v
  map_add' v w := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' r v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm]

@[simp]
lemma intMatrixRatLinear_apply {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) ℤ) (v : Fin m → ℚ) (i : Fin n) :
    intMatrixRatLinear P v i =
      ((P.map (Int.cast : ℤ → ℚ)).mulVec v) i := rfl

@[simp]
lemma intMatrixRatLinear_intVectorToRatLinear {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) ℤ) (x : Fin m → ℤ) :
    intMatrixRatLinear P (intVectorToRatLinear m x) =
      intVectorToRatLinear n (P.mulVec x) := by
  ext i
  simp [intMatrixRatLinear, Matrix.mulVec, dotProduct]

/-- The image of an integral submodule in the rational ambient module
`ℚ^n`. -/
def embeddedSubmodule (A : Submodule ℤ (Fin n → ℤ)) :
    Submodule ℤ (Fin n → ℚ) :=
  A.map (intVectorToRatLinear n)

/-- The embedded copy of the original integral coordinate lattice inside
`ℚ^n`.  This is the rational-submodule avatar of the candidate rank-`n`
lattice before imposing a fixed upper sandwich. -/
def embeddedIntegralLatticeSubmodule (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  embeddedSubmodule (⊤ : Submodule ℤ (Fin n → ℤ))

/-- The rational coordinate overmodule `d⁻¹ ℤ^n` inside `ℚ^n`, regarded as a
`ℤ`-submodule.

This is the elementary finite denominator object used to make the discriminant
group `M# / M` concrete: once a dual lattice is shown to lie in
`det(M)⁻¹ ℤ^n`, its image modulo `ℤ^n` is finite. -/
def invScalarIntegralLatticeSubmodule (d : ℤ) (n : ℕ) :
    Submodule ℤ (Fin n → ℚ) where
  carrier := { v : Fin n → ℚ |
    ∃ z : Fin n → ℤ, v = (d : ℚ)⁻¹ • intVectorToRatLinear n z }
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    rintro v w ⟨zv, rfl⟩ ⟨zw, rfl⟩
    refine ⟨zv + zw, ?_⟩
    ext i
    simp [intVectorToRatLinear]
    ring
  smul_mem' := by
    rintro r v ⟨z, rfl⟩
    refine ⟨r • z, ?_⟩
    ext i
    simp [intVectorToRatLinear, smul_eq_mul]
    ring

@[simp]
lemma mem_invScalarIntegralLatticeSubmodule (d : ℤ) (n : ℕ)
    (v : Fin n → ℚ) :
    v ∈ invScalarIntegralLatticeSubmodule d n ↔
      ∃ z : Fin n → ℤ, v = (d : ℚ)⁻¹ • intVectorToRatLinear n z := by
  rfl

/-- Clear a fixed rational denominator in a rational coordinate submodule.

For `Ω ≤ d⁻¹ℤ^n`, this integral submodule records the numerators of elements
of `Ω`.  It is the intended bridge from the finite rational overlattice list
to the existing full-rank integral-submodule basis machinery. -/
def denominatorClearedSubmodule (d : ℤ)
    (Ω : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℤ) where
  carrier := { z : Fin n → ℤ |
    (d : ℚ)⁻¹ • intVectorToRatLinear n z ∈ Ω }
  zero_mem' := by
    simp
  add_mem' := by
    intro z w hz hw
    change (d : ℚ)⁻¹ • intVectorToRatLinear n (z + w) ∈ Ω
    rw [map_add]
    change (d : ℚ)⁻¹ •
        (intVectorToRatLinear n z + intVectorToRatLinear n w) ∈ Ω
    rw [smul_add]
    exact add_mem hz hw
  smul_mem' := by
    intro r z hz
    change (d : ℚ)⁻¹ • intVectorToRatLinear n (r • z) ∈ Ω
    rw [map_zsmul]
    change (d : ℚ)⁻¹ • (r • intVectorToRatLinear n z) ∈ Ω
    rw [← smul_comm]
    exact Submodule.smul_mem Ω r hz

@[simp]
lemma mem_denominatorClearedSubmodule (d : ℤ)
    (Ω : Submodule ℤ (Fin n → ℚ)) (z : Fin n → ℤ) :
    z ∈ denominatorClearedSubmodule (n := n) d Ω ↔
      (d : ℚ)⁻¹ • intVectorToRatLinear n z ∈ Ω := by
  rfl

lemma smul_top_le_denominatorClearedSubmodule_of_embedded_le
    (d : ℤ) (hd : d ≠ 0) {Ω : Submodule ℤ (Fin n → ℚ)}
    (hΩ : embeddedIntegralLatticeSubmodule n ≤ Ω) :
    LinearMap.range
        ((d : ℤ) •
          (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))) ≤
      denominatorClearedSubmodule (n := n) d Ω := by
  rintro z ⟨y, rfl⟩
  rw [mem_denominatorClearedSubmodule]
  have hdℚ : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd
  have hrecover :
      (d : ℚ)⁻¹ • intVectorToRatLinear n (d • y) =
        intVectorToRatLinear n y := by
    ext i
    simp [intVectorToRatLinear, smul_eq_mul, hdℚ]
  change (d : ℚ)⁻¹ • intVectorToRatLinear n (d • y) ∈ Ω
  rw [hrecover]
  exact hΩ ⟨y, trivial, rfl⟩

lemma mem_iff_exists_denominatorClearedSubmodule
    (d : ℤ) {Ω : Submodule ℤ (Fin n → ℚ)}
    (hΩden : Ω ≤ invScalarIntegralLatticeSubmodule d n)
    (v : Fin n → ℚ) :
    v ∈ Ω ↔
      ∃ z : Fin n → ℤ,
        z ∈ denominatorClearedSubmodule (n := n) d Ω ∧
          v = (d : ℚ)⁻¹ • intVectorToRatLinear n z := by
  constructor
  · intro hv
    rcases hΩden hv with ⟨z, hz⟩
    refine ⟨z, ?_, hz⟩
    rw [mem_denominatorClearedSubmodule]
    rw [← hz]
    exact hv
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- The finite quotient calculation for the denominator overmodule
`d⁻¹ ℤ^n / ℤ^n`.

Representatives are coordinatewise residues modulo `d`. -/
lemma finite_quotient_image_invScalarIntegralLatticeSubmodule
    (d : ℤ) (hd : d ≠ 0) :
    (((invScalarIntegralLatticeSubmodule d n).map
        (embeddedIntegralLatticeSubmodule n).mkQ :
          Submodule ℤ ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)) :
      Set ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)).Finite := by
  classical
  let A : Submodule ℤ (Fin n → ℚ) := embeddedIntegralLatticeSubmodule n
  let Ω : Submodule ℤ (Fin n → ℚ) := invScalarIntegralLatticeSubmodule d n
  let residueVectors : Set (Fin n → ℤ) :=
    Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℤ) (|d| - 1)
  let residues : Set ((Fin n → ℚ) ⧸ A) :=
    (fun z : Fin n → ℤ =>
      A.mkQ ((d : ℚ)⁻¹ • intVectorToRatLinear n z)) '' residueVectors
  have hresidueVectors_finite : residueVectors.Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc (0 : ℤ) (|d| - 1)
  have hresidues_finite : residues.Finite :=
    hresidueVectors_finite.image
      (fun z : Fin n → ℤ =>
        A.mkQ ((d : ℚ)⁻¹ • intVectorToRatLinear n z))
  change ((Ω.map A.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ A)) :
      Set ((Fin n → ℚ) ⧸ A)).Finite
  refine hresidues_finite.subset ?_
  intro q hq
  rcases hq with ⟨v, hvΩ, rfl⟩
  rcases hvΩ with ⟨z, rfl⟩
  let r : Fin n → ℤ := fun i => z i % d
  refine ⟨r, ?_, ?_⟩
  · intro i _hi
    constructor
    · exact Int.emod_nonneg (z i) hd
    · have hlt : z i % d < |d| := Int.emod_lt_abs (z i) hd
      dsimp [r]
      omega
  · change A.mkQ ((d : ℚ)⁻¹ • intVectorToRatLinear n r) =
      A.mkQ ((d : ℚ)⁻¹ • intVectorToRatLinear n z)
    symm
    change Submodule.Quotient.mk ((d : ℚ)⁻¹ • intVectorToRatLinear n z) =
      Submodule.Quotient.mk ((d : ℚ)⁻¹ • intVectorToRatLinear n r)
    rw [Submodule.Quotient.eq]
    refine ⟨fun i => z i / d, trivial, ?_⟩
    ext i
    have hsub : z i - z i % d = d * (z i / d) := by
      have hdecomp := Int.mul_ediv_add_emod (z i) d
      omega
    have hdℚ : (d : ℚ) ≠ 0 := by
      exact_mod_cast hd
    symm
    change (d : ℚ)⁻¹ * (z i : ℚ) - (d : ℚ)⁻¹ * (r i : ℚ) =
      ((z i / d : ℤ) : ℚ)
    have hsub' : z i - r i = d * (z i / d) := by
      simpa [r] using hsub
    calc
      (d : ℚ)⁻¹ * (z i : ℚ) - (d : ℚ)⁻¹ * (r i : ℚ)
          = (d : ℚ)⁻¹ * ((z i - r i : ℤ) : ℚ) := by
            norm_num
            ring
      _ = (d : ℚ)⁻¹ * ((d * (z i / d) : ℤ) : ℚ) := by
            rw [hsub']
      _ = ((z i / d : ℤ) : ℚ) := by
            simp [hdℚ]

/-- Embedding integral submodules in the rational ambient module preserves
joins.  This is the bookkeeping needed to regard the embedded lower sandwich
as the join of the embedded minimum-vector line and the embedded orthogonal
complement. -/
lemma embeddedSubmodule_sup (A B : Submodule ℤ (Fin n → ℤ)) :
    embeddedSubmodule (A ⊔ B) = embeddedSubmodule A ⊔ embeddedSubmodule B := by
  exact Submodule.map_sup A B (intVectorToRatLinear n)

/-- The embedded lower sandwich splits into the embedded line and embedded
orthogonal-complement summands. -/
lemma embedded_lowerSandwichSubmodule_eq (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    embeddedSubmodule (L.lowerSandwichSubmodule x) =
      embeddedSubmodule (Submodule.span ℤ ({x} : Set (Fin n → ℤ))) ⊔
        embeddedSubmodule (L.bilinearOrthogonalSubmodule x) := by
  rw [lowerSandwichSubmodule, embeddedSubmodule_sup]

/-- The natural coordinate embedding `ℤ^n → ℚ^n` is injective. -/
lemma intVectorToRatLinear_injective (n : ℕ) :
    Function.Injective (intVectorToRatLinear n) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro x hx
  ext i
  have hcoord : ((x i : ℤ) : ℚ) = 0 := by
    simpa [intVectorToRatLinear] using congr_fun hx i
  exact_mod_cast hcoord

/-- The rational span of an integral coordinate submodule inside `ℚ^n`.

This is the coordinate version of the rational space `W` generated by a
lattice `M` in Schulze--Pillot's primitive-closure reduction. -/
def rationalSpanOfIntegralSubmodule
    (A : Submodule ℤ (Fin n → ℤ)) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ ((intVectorToRatLinear n) '' (A : Set (Fin n → ℤ)))

/-- The primitive closure `W ∩ Λ` of an integral coordinate submodule `A`.

Here `W` is the rational span of `A` in `ℚ^n`, and `Λ` is the ambient
coordinate lattice `ℤ^n`.  This is the concrete object needed to replace a
bounded-imprimitivity representation by its primitive closure. -/
def primitiveClosure (A : Submodule ℤ (Fin n → ℤ)) :
    Submodule ℤ (Fin n → ℤ) :=
  (rationalSpanOfIntegralSubmodule A).restrictScalars ℤ |>.comap
    (intVectorToRatLinear n)

lemma mem_primitiveClosure_iff
    (A : Submodule ℤ (Fin n → ℤ)) (x : Fin n → ℤ) :
    x ∈ primitiveClosure A ↔
      intVectorToRatLinear n x ∈ rationalSpanOfIntegralSubmodule A := by
  rfl

/-- Rational span commutes with applying an integral coordinate matrix.

This is the coordinate transport fact needed when a primitive representation
argument controls rational spaces only up to integral coordinate change. -/
lemma rationalSpanOfIntegralSubmodule_map_intMatrix
    {m n : ℕ} (P : Matrix (Fin n) (Fin m) ℤ)
    (A : Submodule ℤ (Fin m → ℤ)) :
    (rationalSpanOfIntegralSubmodule A).map (intMatrixRatLinear P) =
      rationalSpanOfIntegralSubmodule
        (A.map (Matrix.toLin' P)) := by
  rw [rationalSpanOfIntegralSubmodule, rationalSpanOfIntegralSubmodule,
    Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨P.mulVec x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · exact (intMatrixRatLinear_intVectorToRatLinear P x).symm
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨intVectorToRatLinear m x, ⟨x, hx, rfl⟩,
      by simp [Matrix.toLin'_apply]⟩

/-- A full-rank coordinate submodule spans the whole rational ambient space.

In the exact full-rank bounded-imprimitivity setting, this identifies the
source rational space `W` with the ambient space after passing from the
integral coordinate image to its rational span. -/
lemma rationalSpanOfIntegralSubmodule_eq_top_of_fullRank
    (A : Submodule ℤ (Fin n → ℤ)) (hA_rank : Module.finrank ℤ A = n) :
    rationalSpanOfIntegralSubmodule A = ⊤ := by
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix A hA_rank
  let Pℚ : Matrix (Fin n) (Fin n) ℚ := Pℤ.map (Int.cast : ℤ → ℚ)
  have hdetℚ : Pℚ.det ≠ 0 := by
    have hdetℤ : Pℤ.det ≠ 0 :=
      fullRankCoordinateSubmoduleBasisMatrix_det_ne_zero A hA_rank
    have hmapdet :
        ((Pℤ.det : ℤ) : ℚ) = Pℚ.det := by
      simpa [Pℚ] using (RingHom.map_det (Int.castRingHom ℚ) Pℤ)
    rw [← hmapdet]
    exact_mod_cast hdetℤ
  have hPℚ_unit : IsUnit Pℚ :=
    Matrix.isUnit_iff_isUnit_det Pℚ |>.mpr (isUnit_iff_ne_zero.mpr hdetℚ)
  have hrange_top : LinearMap.range (Matrix.toLin' Pℚ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact Matrix.mulVec_surjective_iff_isUnit.mpr hPℚ_unit
  have hcols_le :
      Submodule.span ℚ (Set.range Pℚ.col) ≤ rationalSpanOfIntegralSubmodule A := by
    refine Submodule.span_le.mpr ?_
    rintro v ⟨j, rfl⟩
    have hcolA :
        (fun i => Pℤ i j) ∈ A :=
      fullRankCoordinateSubmoduleBasisMatrix_col_mem A hA_rank j
    refine Submodule.subset_span ?_
    refine ⟨fun i => Pℤ i j, hcolA, ?_⟩
    ext i
    simp [Pℚ, Pℤ, intVectorToRatLinear]
  apply le_antisymm le_top
  rw [← hrange_top, Matrix.range_toLin']
  exact hcols_le

/-- The primitive closure of a full-rank coordinate submodule is the whole
ambient coordinate lattice.

This is the full-rank specialization of the source step `M' = W ∩ Λ`: once the
coordinate image has rank `n`, its rational span is all of `ℚ^n`, so its
primitive closure inside `ℤ^n` is `ℤ^n`. -/
lemma primitiveClosure_eq_top_of_fullRank
    (A : Submodule ℤ (Fin n → ℤ)) (hA_rank : Module.finrank ℤ A = n) :
    primitiveClosure A = ⊤ := by
  ext x
  rw [mem_primitiveClosure_iff,
    rationalSpanOfIntegralSubmodule_eq_top_of_fullRank A hA_rank]
  simp

/-- If the overmodule is the full ambient lattice, the relative submodule
index is exactly the ambient quotient cardinality.

This is the exact-index version of the primitive-closure bookkeeping:
Schulze--Pillot's imprimitivity index `(M' : M)` agrees with the Lean quotient
cardinality once the primitive closure `M'` is the whole ambient coordinate
lattice. -/
lemma comap_subtype_index_eq_card_quotient_of_eq_top
    {Ω : Type*} [AddCommGroup Ω]
    {A B : Submodule ℤ Ω} (hBtop : B = ⊤) :
    (A.comap B.subtype).toAddSubgroup.index = Nat.card (Ω ⧸ A) := by
  let f : B →+ Ω := {
    toFun := fun x => x
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [hBtop]
    trivial
  have hidx := AddSubgroup.index_comap_of_surjective A.toAddSubgroup hsurj
  rw [AddSubgroup.index_eq_card]
  convert hidx using 1

/-- In the full-rank coordinate branch, Schulze--Pillot's relative
imprimitivity index inside the primitive closure is exactly Lean's ambient
coordinate quotient cardinality.

Since `primitiveClosure A = ⊤` for full-rank coordinate images, the source
index `(W ∩ Λ : A)` is not merely bounded by `Nat.card ((Fin n → ℤ) ⧸ A)`:
it is equal to it. -/
lemma primitiveClosure_comap_index_eq_card_quotient_of_fullRank
    (A : Submodule ℤ (Fin n → ℤ)) (hA_rank : Module.finrank ℤ A = n) :
    (A.comap (primitiveClosure A).subtype).toAddSubgroup.index =
      Nat.card ((Fin n → ℤ) ⧸ A) :=
  comap_subtype_index_eq_card_quotient_of_eq_top
    (primitiveClosure_eq_top_of_fullRank A hA_rank)

/-- The Schulze--Pillot bilinear value after extending scalars from `ℤ` to
`ℚ`.  This is the ambient form used to describe dual overlattices. -/
def bilinearFormValueRat (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℚ) : ℚ :=
  dotProduct x ((L.pairingMatrix.map (Int.cast : ℤ → ℚ)).mulVec y)

/-- The scalar-extended Schulze--Pillot bilinear form is symmetric. -/
lemma bilinearFormValueRat_comm (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℚ) :
    L.bilinearFormValueRat x y = L.bilinearFormValueRat y x := by
  calc
    L.bilinearFormValueRat x y =
        ∑ i, ∑ j, x i * (L.pairingMatrix i j : ℚ) * y j := by
          simp [bilinearFormValueRat, dotProduct, Matrix.mulVec,
            Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ i, x i * (L.pairingMatrix i j : ℚ) * y j := by
          rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, y j * (L.pairingMatrix j i : ℚ) * x i := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [← L.form_symm.apply i j]
          ring
    _ = L.bilinearFormValueRat y x := by
          simp [bilinearFormValueRat, dotProduct, Matrix.mulVec,
            Finset.mul_sum, mul_assoc]

@[simp]
lemma bilinearFormValueRat_zero_left (L : PositiveDefiniteIntegralLattice n) (y : Fin n → ℚ) :
    L.bilinearFormValueRat 0 y = 0 := by
  simp [bilinearFormValueRat, dotProduct]

lemma bilinearFormValueRat_add_left (L : PositiveDefiniteIntegralLattice n)
    (x₁ x₂ y : Fin n → ℚ) :
    L.bilinearFormValueRat (x₁ + x₂) y =
      L.bilinearFormValueRat x₁ y + L.bilinearFormValueRat x₂ y := by
  simp [bilinearFormValueRat, dotProduct, Finset.sum_add_distrib,
    add_mul]

lemma bilinearFormValueRat_zsmul_left (L : PositiveDefiniteIntegralLattice n)
    (r : ℤ) (x y : Fin n → ℚ) :
    L.bilinearFormValueRat (r • x) y = r * L.bilinearFormValueRat x y := by
  simp [bilinearFormValueRat, dotProduct, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm]

lemma bilinearFormValueRat_add_right (L : PositiveDefiniteIntegralLattice n)
    (x y₁ y₂ : Fin n → ℚ) :
    L.bilinearFormValueRat x (y₁ + y₂) =
      L.bilinearFormValueRat x y₁ + L.bilinearFormValueRat x y₂ := by
  simp [bilinearFormValueRat, dotProduct, Matrix.mulVec,
    Finset.sum_add_distrib, mul_add, Finset.mul_sum]

lemma bilinearFormValueRat_zsmul_right (L : PositiveDefiniteIntegralLattice n)
    (r : ℤ) (x y : Fin n → ℚ) :
    L.bilinearFormValueRat x (r • y) = r * L.bilinearFormValueRat x y := by
  simp [bilinearFormValueRat, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

@[simp]
lemma bilinearFormValueRat_intVectorToRatLinear (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → ℤ) :
    L.bilinearFormValueRat (intVectorToRatLinear n x)
      (intVectorToRatLinear n y) = (L.bilinearFormValue x y : ℚ) := by
  simp [bilinearFormValueRat, bilinearFormValue, dotProduct, Matrix.mulVec]

/-- A rational matrix is integral on an integral coordinate submodule if all
pairings of submodule vectors are integer-valued.

This is the admissibility predicate for the remaining finite-overlattice
reconstruction step: after the fixed lower block determines a rational ambient
form, only those candidate overmodules on which this rational form is integral
can define integral lattice representatives. -/
def rationalMatrixIntegralOnSubmodule
    (F : Matrix (Fin n) (Fin n) ℚ)
    (B : Submodule ℤ (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, x ∈ B →
    ∀ y : Fin n → ℤ, y ∈ B →
      ∃ z : ℤ,
        dotProduct (intVectorToRatLinear n x)
          (F.mulVec (intVectorToRatLinear n y)) = z

/-- A rational coordinate submodule is integral for an integral lattice form
if all pairings of rational vectors in the submodule are integer-valued. -/
def rationalSubmoduleIntegralOnLattice
    (L : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ)) : Prop :=
  ∀ v : Fin n → ℚ, v ∈ Ω →
    ∀ w : Fin n → ℚ, w ∈ Ω →
      ∃ z : ℤ, L.bilinearFormValueRat v w = z

/-- Turn a rational matrix with entrywise integrality witnesses into an
integer matrix. -/
noncomputable def integerMatrixOfRatMatrix
    {m n : Type*} (G : Matrix m n ℚ)
    (hG : ∀ i j, ∃ z : ℤ, G i j = z) : Matrix m n ℤ :=
  fun i j => Classical.choose (hG i j)

@[simp]
lemma integerMatrixOfRatMatrix_cast
    {m n : Type*} (G : Matrix m n ℚ)
    (hG : ∀ i j, ∃ z : ℤ, G i j = z) :
    (integerMatrixOfRatMatrix G hG).map (Int.cast : ℤ → ℚ) = G := by
  ext i j
  exact (Classical.choose_spec (hG i j)).symm

/-- The rational `B`-orthogonal hyperplane to `x` inside `ℚ^n`.

This is the scalar-extended orthogonal complement.  It is larger than the
embedded integral orthogonal complement, so it is useful for decomposition
bookkeeping but is not by itself the finite upper sandwich. -/
def rationalBilinearOrthogonalSubmodule (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℚ) where
  carrier := { v : Fin n → ℚ |
    L.bilinearFormValueRat (intVectorToRatLinear n x) v = 0 }
  zero_mem' := by
    simp [bilinearFormValueRat, dotProduct]
  add_mem' := by
    intro v w hv hw
    change L.bilinearFormValueRat (intVectorToRatLinear n x) v = 0 at hv
    change L.bilinearFormValueRat (intVectorToRatLinear n x) w = 0 at hw
    change L.bilinearFormValueRat (intVectorToRatLinear n x) (v + w) = 0
    rw [bilinearFormValueRat_add_right, hv, hw]
    norm_num
  smul_mem' := by
    intro r v hv
    change L.bilinearFormValueRat (intVectorToRatLinear n x) v = 0 at hv
    change L.bilinearFormValueRat (intVectorToRatLinear n x) (r • v) = 0
    rw [bilinearFormValueRat_zsmul_right, hv]
    norm_num

@[simp]
lemma mem_rationalBilinearOrthogonalSubmodule (L : PositiveDefiniteIntegralLattice n)
    (x : Fin n → ℤ) (v : Fin n → ℚ) :
    v ∈ L.rationalBilinearOrthogonalSubmodule x ↔
      L.bilinearFormValueRat (intVectorToRatLinear n x) v = 0 :=
  Iff.rfl

/-- The dual overmodule of an integral submodule after embedding the ambient
coordinate lattice in `ℚ^n`.

This is the concrete rational-lattice side of the Schulze--Pillot upper
sandwich.  For a lower lattice `A`, it consists of rational vectors pairing
integrally with every vector of `A` under `B(x,y)=xᵀFy`. -/
def dualSubmodule (L : PositiveDefiniteIntegralLattice n) (A : Submodule ℤ (Fin n → ℤ)) :
    Submodule ℤ (Fin n → ℚ) where
  carrier := { v : Fin n → ℚ |
    ∀ y : Fin n → ℤ, y ∈ A →
      ∃ z : ℤ, L.bilinearFormValueRat v (intVectorToRatLinear n y) = z }
  zero_mem' := by
    intro y _hy
    exact ⟨0, by simp⟩
  add_mem' := by
    intro v w hv hw y hy
    obtain ⟨zv, hzv⟩ := hv y hy
    obtain ⟨zw, hzw⟩ := hw y hy
    refine ⟨zv + zw, ?_⟩
    rw [bilinearFormValueRat_add_left, hzv, hzw]
    norm_num
  smul_mem' := by
    intro r v hv y hy
    obtain ⟨z, hz⟩ := hv y hy
    refine ⟨r * z, ?_⟩
    rw [bilinearFormValueRat_zsmul_left, hz]
    norm_num

@[simp]
lemma mem_dualSubmodule (L : PositiveDefiniteIntegralLattice n)
    (A : Submodule ℤ (Fin n → ℤ)) (v : Fin n → ℚ) :
    v ∈ L.dualSubmodule A ↔
      ∀ y : Fin n → ℤ, y ∈ A →
        ∃ z : ℤ, L.bilinearFormValueRat v (intVectorToRatLinear n y) = z :=
  Iff.rfl

/-- Every integral vector lies in the rational dual of any integral submodule,
because the stored Schulze--Pillot form has integral matrix entries.  This is
the basic `Λ ⊆ Ω` inclusion needed before the fixed-index upper sandwich is
specialized to a finite rational dual overmodule. -/
lemma intVectorToRatLinear_mem_dualSubmodule (L : PositiveDefiniteIntegralLattice n)
    (A : Submodule ℤ (Fin n → ℤ)) (x : Fin n → ℤ) :
    intVectorToRatLinear n x ∈ L.dualSubmodule A := by
  intro y _hy
  exact ⟨L.bilinearFormValue x y, by simp⟩

/-- The full-coordinate dual lattice is contained in the elementary
determinant-denominator overmodule `det(L)⁻¹ ℤ^n`.

This is the adjugate half of the discriminant-group finiteness argument:
if `F v` has integral coordinates, then `det(F) v = adj(F) F v` is integral. -/
lemma dualSubmodule_top_le_invScalarIntegralLatticeSubmodule
    (L : PositiveDefiniteIntegralLattice n) :
    L.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ)) ≤
      invScalarIntegralLatticeSubmodule L.pairingDeterminant n := by
  classical
  intro v hv
  let Fℤ : Matrix (Fin n) (Fin n) ℤ := L.pairingMatrix
  let Fℚ : Matrix (Fin n) (Fin n) ℚ := Fℤ.map (Int.cast : ℤ → ℚ)
  let w : Fin n → ℤ := fun j =>
    Classical.choose (hv ((Pi.basisFun ℤ (Fin n)) j) trivial)
  have hw : ∀ j : Fin n,
      L.bilinearFormValueRat v
          (intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j)) =
        (w j : ℚ) := by
    intro j
    exact Classical.choose_spec
      (hv ((Pi.basisFun ℤ (Fin n)) j) trivial)
  have hFv : Fℚ.mulVec v = intVectorToRatLinear n w := by
    ext j
    calc
      Fℚ.mulVec v j =
          dotProduct (intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j))
            (Fℚ.mulVec v) := by
            symm
            rw [dotProduct]
            calc
              ∑ k, intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j) k *
                    Fℚ.mulVec v k =
                  intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j) j *
                    Fℚ.mulVec v j := by
                    refine Finset.sum_eq_single (s := Finset.univ) (a := j)
                      (f := fun k : Fin n =>
                        intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j) k *
                          Fℚ.mulVec v k) ?_ ?_
                    · intro k _hk hkj
                      simp [intVectorToRatLinear, Pi.basisFun_apply,
                        Pi.single_eq_of_ne hkj]
                    · intro hj
                      simp at hj
              _ = Fℚ.mulVec v j := by
                    simp [intVectorToRatLinear, Pi.basisFun_apply]
      _ = L.bilinearFormValueRat
            (intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j)) v := by
            rfl
      _ = L.bilinearFormValueRat v
            (intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j)) := by
            rw [bilinearFormValueRat_comm]
      _ = (w j : ℚ) := hw j
      _ = intVectorToRatLinear n w j := rfl
  have hadj_mul :
      (Fℤ.adjugate.map (Int.cast : ℤ → ℚ)) * Fℚ =
        (L.pairingDeterminant : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    calc
      (Fℤ.adjugate.map (Int.cast : ℤ → ℚ)) * Fℚ =
          (Fℤ.adjugate * Fℤ).map (Int.cast : ℤ → ℚ) := by
            rw [Matrix.map_mul_intCast]
      _ = (Fℤ.det • (1 : Matrix (Fin n) (Fin n) ℤ)).map
            (Int.cast : ℤ → ℚ) := by
            rw [Matrix.adjugate_mul]
      _ = (L.pairingDeterminant : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
            ext i j
            change (((Fℤ.det • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℤ) : ℚ) =
              (((L.pairingDeterminant : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ)) i j)
            by_cases hij : i = j
            · subst j
              simp [Fℤ, pairingDeterminant]
            · simp [Fℤ, pairingDeterminant, hij]
  refine ⟨Fℤ.adjugate.mulVec w, ?_⟩
  have hdet_v :
      (L.pairingDeterminant : ℚ) • v =
        intVectorToRatLinear n (Fℤ.adjugate.mulVec w) := by
    calc
      (L.pairingDeterminant : ℚ) • v =
          ((Fℤ.adjugate.map (Int.cast : ℤ → ℚ)) * Fℚ).mulVec v := by
            rw [hadj_mul]
            ext i
            change (L.pairingDeterminant : ℚ) * v i =
              ∑ j, ((L.pairingDeterminant : ℚ) * (1 : Matrix (Fin n) (Fin n) ℚ) i j) * v j
            symm
            calc
              ∑ j, ((L.pairingDeterminant : ℚ) * (1 : Matrix (Fin n) (Fin n) ℚ) i j) * v j =
                  ((L.pairingDeterminant : ℚ) * (1 : Matrix (Fin n) (Fin n) ℚ) i i) *
                    v i := by
                    refine Finset.sum_eq_single (s := Finset.univ) (a := i)
                      (f := fun j : Fin n =>
                        ((L.pairingDeterminant : ℚ) *
                          (1 : Matrix (Fin n) (Fin n) ℚ) i j) * v j) ?_ ?_
                    · intro j _hj hji
                      have hij : i ≠ j := by
                        intro h
                        exact hji h.symm
                      simp [hij]
                    · intro hi
                      simp at hi
              _ = (L.pairingDeterminant : ℚ) * v i := by
                    simp
      _ = (Fℤ.adjugate.map (Int.cast : ℤ → ℚ)).mulVec
            (Fℚ.mulVec v) := by
            rw [Matrix.mulVec_mulVec]
      _ = (Fℤ.adjugate.map (Int.cast : ℤ → ℚ)).mulVec
            (intVectorToRatLinear n w) := by
            rw [hFv]
      _ = intVectorToRatLinear n (Fℤ.adjugate.mulVec w) := by
            exact intMatrixRatLinear_intVectorToRatLinear Fℤ.adjugate w
  have hdet_ne : (L.pairingDeterminant : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
  calc
    v = (L.pairingDeterminant : ℚ)⁻¹ • ((L.pairingDeterminant : ℚ) • v) := by
          ext i
          simp [hdet_ne]
    _ = (L.pairingDeterminant : ℚ)⁻¹ •
          intVectorToRatLinear n (Fℤ.adjugate.mulVec w) := by
          rw [hdet_v]

/-- The discriminant quotient image `L# / ℤ^n` is finite in coordinates. -/
lemma finite_quotient_image_dualSubmodule_top
    (L : PositiveDefiniteIntegralLattice n) :
    (((L.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ))).map
        (embeddedIntegralLatticeSubmodule n).mkQ :
          Submodule ℤ ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)) :
      Set ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)).Finite := by
  classical
  have hden :
      (((invScalarIntegralLatticeSubmodule L.pairingDeterminant n).map
          (embeddedIntegralLatticeSubmodule n).mkQ :
            Submodule ℤ ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)) :
        Set ((Fin n → ℚ) ⧸ embeddedIntegralLatticeSubmodule n)).Finite :=
    finite_quotient_image_invScalarIntegralLatticeSubmodule
      L.pairingDeterminant (ne_of_gt L.pairingDeterminant_pos)
  refine hden.subset ?_
  intro q hq
  rcases hq with ⟨v, hv, rfl⟩
  exact ⟨v, dualSubmodule_top_le_invScalarIntegralLatticeSubmodule L hv, rfl⟩

/-- The embedded lower sandwich is contained in the embedded original
integral coordinate lattice.  This records the lower inclusion
`M ⊥ N ⊆ Λ` in the rational-submodule language used for fixed-index
overlattice counting. -/
lemma embedded_lowerSandwichSubmodule_le_embeddedIntegralLatticeSubmodule
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    embeddedSubmodule (L.lowerSandwichSubmodule x) ≤
      embeddedIntegralLatticeSubmodule n := by
  exact Submodule.map_mono le_top

/-- The embedded original integral coordinate lattice is contained in the
rational dual of any integral submodule, because the stored
Schulze--Pillot matrix has integral entries. -/
lemma embeddedIntegralLatticeSubmodule_le_dualSubmodule
    (L : PositiveDefiniteIntegralLattice n) (A : Submodule ℤ (Fin n → ℤ)) :
    embeddedIntegralLatticeSubmodule n ≤ L.dualSubmodule A := by
  rintro v ⟨x, _hx, rfl⟩
  exact intVectorToRatLinear_mem_dualSubmodule L A x

/-- If a matrix parametrizes exactly the vectors orthogonal to `x`, then its
linear range is the `B`-orthogonal submodule of `x`. -/
lemma bilinearOrthogonalSubmodule_eq_range_of_forall
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) :
    L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (hspan y).1 ((mem_bilinearOrthogonalSubmodule L x y).1 hy)
    exact ⟨z, by simpa using hz.symm⟩
  · rintro ⟨z, hz⟩
    rw [mem_bilinearOrthogonalSubmodule]
    exact (hspan y).2 ⟨z, by simpa using hz.symm⟩

/-- If the linear range of `C` is the `B`-orthogonal submodule of `x`, then
`C` parametrizes exactly the vectors orthogonal to `x`.

This is the converse of `bilinearOrthogonalSubmodule_eq_range_of_forall`.  It
is used when only the coordinate-submodule equality is known but a primitive
complement presentation has to be reconstructed. -/
lemma forall_bilinearFormValue_eq_zero_iff_exists_of_bilinearOrthogonalSubmodule_eq_range
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (horth : L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C)) :
    ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z := by
  intro y
  constructor
  · intro hy
    have hyorth : y ∈ L.bilinearOrthogonalSubmodule x :=
      (mem_bilinearOrthogonalSubmodule L x y).2 hy
    rw [horth] at hyorth
    rcases hyorth with ⟨z, hz⟩
    exact ⟨z, by simpa [Matrix.toLin'_apply] using hz.symm⟩
  · rintro ⟨z, rfl⟩
    have hz_range : C.mulVec z ∈ LinearMap.range (Matrix.toLin' C) := by
      exact ⟨z, by simp [Matrix.toLin'_apply]⟩
    have hz_orth : C.mulVec z ∈ L.bilinearOrthogonalSubmodule x := by
      rwa [horth]
    exact (mem_bilinearOrthogonalSubmodule L x (C.mulVec z)).1 hz_orth

/-- The diagonal value of Schulze--Pillot's bilinear form is the quadratic
form value. -/
lemma bilinearFormValue_self (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    L.bilinearFormValue x x = L.quadForm x := by
  simp [bilinearFormValue, quadForm_eq_dotProduct]

/-- Orthogonal-residual integrality is exactly the missing input needed to
upgrade the universal rational hyperplane decomposition to the finite split
overmodule.

If every residual `y - B(x,y) Q(x)⁻¹x` lies in the embedded integral
orthogonal complement, then every embedded integral vector lies in
`ℤ · Q(x)⁻¹x + embedded(x⊥)`.  This packages the fixed-index upper-control
target as an integral-orthogonal-component statement. -/
lemma embeddedIntegralLatticeSubmodule_le_splitOvermodule_of_residual_mem_embeddedOrthogonal
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    (∀ y : Fin n → ℤ,
      intVectorToRatLinear n y +
          (-(L.bilinearFormValue x y) : ℤ) •
            ((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x) ∈
        embeddedSubmodule (L.bilinearOrthogonalSubmodule x)) →
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔
          embeddedSubmodule (L.bilinearOrthogonalSubmodule x) := by
  intro hresidual
  rintro v ⟨y, _hy, rfl⟩
  let g : Fin n → ℚ := (L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x
  let c : ℤ := L.bilinearFormValue x y
  refine Submodule.mem_sup.2
    ⟨c • g, ?_, intVectorToRatLinear n y + (-c) • g, ?_, ?_⟩
  · exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
  · simpa [g, c] using hresidual y
  · ext i
    simp [g, c, add_assoc]

/-- The denominator-controlled rational line has finite image modulo the
embedded integral line.

Concretely, if `g = Q(x)⁻¹x`, then the embedded integral line contains
`Q(x)g = x`, so the quotient of `ℤg` by the embedded `ℤx` is represented by
the finitely many residues modulo `Q(x)`.  This is the line-component finite
quotient calculation needed in the fixed-index Schulze--Pillot sandwich. -/
lemma finite_quotient_image_span_inv_quadForm_smul_intVectorToRatLinear
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) (hx : L.quadForm x ≠ 0) :
    let A : Submodule ℤ (Fin n → ℚ) :=
      embeddedSubmodule (Submodule.span ℤ ({x} : Set (Fin n → ℤ)))
    let B : Submodule ℤ (Fin n → ℚ) :=
      Submodule.span ℤ
        ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
          Set (Fin n → ℚ))
    ((B.map A.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ A)) :
      Set ((Fin n → ℚ) ⧸ A)).Finite := by
  classical
  intro A B
  let g : Fin n → ℚ := (L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x
  have hB : B = Submodule.span ℤ ({g} : Set (Fin n → ℚ)) := rfl
  have hqg_mem : (L.quadForm x : ℤ) • g ∈ A := by
    have hrecover :
        (L.quadForm x : ℤ) • g = intVectorToRatLinear n x := by
      ext i
      simp [g, smul_eq_mul, hx]
    rw [hrecover]
    exact ⟨x, Submodule.subset_span (by simp), rfl⟩
  let residues : Set ((Fin n → ℚ) ⧸ A) :=
    (fun k : ℤ => A.mkQ (k • g)) ''
      Set.Icc (0 : ℤ) (|L.quadForm x| - 1)
  have hresidues_finite : residues.Finite :=
    (Set.finite_Icc (0 : ℤ) (|L.quadForm x| - 1)).image
      (fun k : ℤ => A.mkQ (k • g))
  refine hresidues_finite.subset ?_
  intro v hv
  rcases hv with ⟨w, hwB, rfl⟩
  rw [hB] at hwB
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hwB
  refine ⟨r % L.quadForm x, ?_, ?_⟩
  · constructor
    · exact Int.emod_nonneg r hx
    · have hlt : r % L.quadForm x < |L.quadForm x| :=
        Int.emod_lt_abs r hx
      omega
  · change Submodule.Quotient.mk ((r % L.quadForm x) • g) =
      Submodule.Quotient.mk (r • g)
    symm
    rw [Submodule.Quotient.eq]
    have hdiff :
        r • g - (r % L.quadForm x) • g =
          (r / L.quadForm x) • ((L.quadForm x : ℤ) • g) := by
      calc
        r • g - (r % L.quadForm x) • g =
            (r - r % L.quadForm x) • g := by rw [sub_smul]
        _ = (L.quadForm x * (r / L.quadForm x)) • g := by
            have hsub :
                r - r % L.quadForm x =
                  L.quadForm x * (r / L.quadForm x) := by
              have hdecomp := Int.mul_ediv_add_emod r (L.quadForm x)
              omega
            rw [hsub]
        _ = (r / L.quadForm x) • ((L.quadForm x : ℤ) • g) := by
            rw [smul_smul, mul_comm]
    rw [hdiff]
    exact Submodule.smul_mem A (r / L.quadForm x) hqg_mem

/-- The rational embedding of a complement matrix after clearing a fixed
denominator.

For a complement matrix `C`, this is the map
`z ↦ m⁻¹ C z` from the abstract complement coordinates into `ℚ^n`.  It is the
linear map underlying the finite orthogonal-side overmodule used in the
fixed-index Schulze--Pillot sandwich. -/
def scaledComplementMap
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (m : ℤ) :
    (Fin (n - 1) → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun z := (m : ℚ)⁻¹ • intVectorToRatLinear n (C.mulVec z)
  map_add' z w := by
    ext i
    simp [Matrix.mulVec, Finset.sum_add_distrib, mul_add]
  map_smul' r z := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm]

/-- The denominator-controlled rational overmodule generated by a complement
matrix `C`.

This is the concrete finite-index candidate for the orthogonal side of
Schulze--Pillot's `N#`: vectors are generated by `m⁻¹ C z` with integral
complement coordinates `z`. -/
def scaledComplementOvermodule
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (m : ℤ) :
    Submodule ℤ (Fin n → ℚ) :=
  LinearMap.range (scaledComplementMap C m)

@[simp]
lemma intMatrixRatLinear_inv_smul_intVectorToRatLinear
    (P : Matrix (Fin n) (Fin n) ℤ) (μ : ℤ) (x : Fin n → ℤ) :
    intMatrixRatLinear P
        ((μ : ℚ)⁻¹ • intVectorToRatLinear n x) =
      (μ : ℚ)⁻¹ • intVectorToRatLinear n (P.mulVec x) := by
  rw [map_smul, intMatrixRatLinear_intVectorToRatLinear]

@[simp]
lemma intMatrixRatLinear_scaledComplementMap
    (P : Matrix (Fin n) (Fin n) ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (m : ℤ)
    (z : Fin (n - 1) → ℤ) :
    intMatrixRatLinear P (scaledComplementMap C m z) =
      scaledComplementMap (P * C) m z := by
  ext i
  simp [intMatrixRatLinear, scaledComplementMap, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

/-- A denominator-controlled complement overmodule has finite image modulo the
embedded integral complement range.

Concretely, the quotient is represented by the finitely many coordinate
residues modulo `m` in the complement coordinates.  This is the orthogonal
analogue of the cyclic line quotient generated by `Q(x)⁻¹x`. -/
lemma finite_quotient_image_scaledComplementOvermodule
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) {m : ℤ} (hm : m ≠ 0) :
    let A : Submodule ℤ (Fin n → ℚ) :=
      embeddedSubmodule (LinearMap.range (Matrix.toLin' C))
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      scaledComplementOvermodule C m
    ((Ω.map A.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ A)) :
      Set ((Fin n → ℚ) ⧸ A)).Finite := by
  intro A Ω
  let residues : Set ((Fin n → ℚ) ⧸ A) :=
    (fun r : Fin (n - 1) → ℤ => A.mkQ (scaledComplementMap C m r)) ''
      Set.pi Set.univ (fun _ : Fin (n - 1) => Set.Icc (0 : ℤ) (|m| - 1))
  have hresidues_finite : residues.Finite :=
    (Set.Finite.pi fun _ : Fin (n - 1) =>
      Set.finite_Icc (0 : ℤ) (|m| - 1)).image
        (fun r : Fin (n - 1) → ℤ => A.mkQ (scaledComplementMap C m r))
  refine hresidues_finite.subset ?_
  intro v hv
  rcases hv with ⟨w, hw, rfl⟩
  change w ∈ scaledComplementOvermodule C m at hw
  obtain ⟨z, rfl⟩ := hw
  let r : Fin (n - 1) → ℤ := fun i => z i % m
  let q : Fin (n - 1) → ℤ := fun i => z i / m
  refine ⟨r, ?_, ?_⟩
  · intro i _hi
    dsimp [r]
    constructor
    · exact Int.emod_nonneg (z i) hm
    · have hlt : z i % m < |m| := Int.emod_lt_abs (z i) hm
      omega
  · change A.mkQ (scaledComplementMap C m r) =
      A.mkQ (scaledComplementMap C m z)
    symm
    change Submodule.Quotient.mk (scaledComplementMap C m z) =
      Submodule.Quotient.mk (scaledComplementMap C m r)
    rw [Submodule.Quotient.eq]
    have hzr : z - r = m • q := by
      ext i
      dsimp [r, q]
      have hdecomp := Int.mul_ediv_add_emod (z i) m
      omega
    have hdiff :
        scaledComplementMap C m z - scaledComplementMap C m r =
          intVectorToRatLinear n (C.mulVec q) := by
      calc
        scaledComplementMap C m z - scaledComplementMap C m r =
            scaledComplementMap C m (z - r) := by
              rw [map_sub]
        _ = scaledComplementMap C m (m • q) := by rw [hzr]
        _ = intVectorToRatLinear n (C.mulVec q) := by
              ext i
              simp [scaledComplementMap, Matrix.mulVec, dotProduct, smul_eq_mul,
                hm, mul_assoc]
              field_simp [(show (m : ℚ) ≠ 0 by exact_mod_cast hm)]
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (by intro j _hj; ring)
    rw [hdiff]
    exact ⟨C.mulVec q, ⟨q, by simp [Matrix.toLin'_apply]⟩, rfl⟩

/-- A finite quotient on any orthogonal-side overmodule combines with the
finite line quotient to give a finite quotient for the split overmodule.

This generalizes the statement for the embedded integral orthogonal complement
itself to any fixed orthogonal-side overmodule with finite image modulo that
complement.  It is the quotient shape of Schulze--Pillot's `M# ⊥ N#` upper
sandwich. -/
lemma finite_quotient_image_span_inv_quadForm_smul_intVectorToRatLinear_sup_of_finite_orthogonal_overmodule
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) (hx : L.quadForm x ≠ 0)
    (Ωorth : Submodule ℤ (Fin n → ℚ))
    (horth :
      ((Ωorth.map (embeddedSubmodule (L.bilinearOrthogonalSubmodule x)).mkQ :
          Submodule ℤ
            ((Fin n → ℚ) ⧸
              embeddedSubmodule (L.bilinearOrthogonalSubmodule x))) :
        Set ((Fin n → ℚ) ⧸
          embeddedSubmodule (L.bilinearOrthogonalSubmodule x))).Finite) :
    let A : Submodule ℤ (Fin n → ℚ) :=
      embeddedSubmodule (L.lowerSandwichSubmodule x)
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      Submodule.span ℤ
          ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
            Set (Fin n → ℚ)) ⊔ Ωorth
    ((Ω.map A.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ A)) :
      Set ((Fin n → ℚ) ⧸ A)).Finite := by
  intro A Ω
  let Aline : Submodule ℤ (Fin n → ℚ) :=
    embeddedSubmodule (Submodule.span ℤ ({x} : Set (Fin n → ℤ)))
  let Bline : Submodule ℤ (Fin n → ℚ) :=
    Submodule.span ℤ
      ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
        Set (Fin n → ℚ))
  let Aorth : Submodule ℤ (Fin n → ℚ) :=
    embeddedSubmodule (L.bilinearOrthogonalSubmodule x)
  have hline :
      ((Bline.map Aline.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ Aline)) :
        Set ((Fin n → ℚ) ⧸ Aline)).Finite := by
    simpa [Aline, Bline]
      using finite_quotient_image_span_inv_quadForm_smul_intVectorToRatLinear
        L x hx
  have hsup :
      (((Bline ⊔ Ωorth).map (Aline ⊔ Aorth).mkQ :
          Submodule ℤ ((Fin n → ℚ) ⧸ (Aline ⊔ Aorth))) :
        Set ((Fin n → ℚ) ⧸ (Aline ⊔ Aorth))).Finite :=
    finite_quotient_image_sup_of_finite_quotient_images
      (A := Aline) (B := Bline) (C := Aorth) (D := Ωorth) hline
      (by simpa [Aorth] using horth)
  exact (congrArg (fun D : Submodule ℤ (Fin n → ℚ) =>
    ((Ω.map D.mkQ : Submodule ℤ ((Fin n → ℚ) ⧸ D)) :
      Set ((Fin n → ℚ) ⧸ D)).Finite)
    (embedded_lowerSandwichSubmodule_eq L x)).mpr hsup

/-- A finite orthogonal-side overmodule is enough for the embedded coordinate
lattice finite count, provided the embedded lattice lies under the resulting
line-plus-orthogonal split overmodule.

For the eventual Schulze--Pillot fixed-index source, `Ωorth` should be the
fixed dual complement side (the formal version of `N#`), with finite quotient
over the embedded integral complement. -/
lemma finite_intermediate_submodules_embeddedIntegralLattice_of_le_line_sup_finite_orthogonal_overmodule
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) (hx : L.quadForm x ≠ 0)
    (Ωorth : Submodule ℤ (Fin n → ℚ))
    (horth :
      ((Ωorth.map (embeddedSubmodule (L.bilinearOrthogonalSubmodule x)).mkQ :
          Submodule ℤ
            ((Fin n → ℚ) ⧸
              embeddedSubmodule (L.bilinearOrthogonalSubmodule x))) :
        Set ((Fin n → ℚ) ⧸
          embeddedSubmodule (L.bilinearOrthogonalSubmodule x))).Finite)
    (hupper :
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔ Ωorth) :
    Set.Finite { C : Submodule ℤ (Fin n → ℚ) |
      embeddedSubmodule (L.lowerSandwichSubmodule x) ≤ C ∧
        C ≤ embeddedIntegralLatticeSubmodule n } := by
  exact finite_intermediate_submodules_of_finite_overmodule_quotient
    (A := embeddedSubmodule (L.lowerSandwichSubmodule x))
    (B := embeddedIntegralLatticeSubmodule n)
    (Ω := Submodule.span ℤ
        ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
          Set (Fin n → ℚ)) ⊔ Ωorth)
    (embedded_lowerSandwichSubmodule_le_embeddedIntegralLatticeSubmodule L x)
    hupper
    (by
      simpa
        using
          finite_quotient_image_span_inv_quadForm_smul_intVectorToRatLinear_sup_of_finite_orthogonal_overmodule
            L x hx Ωorth horth)

/-- A denominator-controlled complement overmodule supplies the finite
orthogonal-side quotient needed by the line-plus-orthogonal finite-count
bridge.

This is the form intended for the fixed-index source once Schulze--Pillot's
`N#` side has been bounded by a fixed denominator in the complement matrix
coordinates. -/
lemma finite_intermediate_submodules_embeddedIntegralLattice_of_le_line_sup_scaledComplementOvermodule
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) {m : ℤ}
    (hx : L.quadForm x ≠ 0) (hm : m ≠ 0)
    (horth : L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C))
    (hupper :
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔ scaledComplementOvermodule C m) :
    Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
      embeddedSubmodule (L.lowerSandwichSubmodule x) ≤ D ∧
        D ≤ embeddedIntegralLatticeSubmodule n } := by
  exact finite_intermediate_submodules_embeddedIntegralLattice_of_le_line_sup_finite_orthogonal_overmodule
    L x hx (scaledComplementOvermodule C m)
    (by
      rw [horth]
      exact finite_quotient_image_scaledComplementOvermodule C hm)
    hupper

/-- Residual control by a denominator-controlled complement overmodule gives
the fixed-index upper inclusion.

This is the scaled-complement analogue of
`embeddedIntegralLatticeSubmodule_le_splitOvermodule_of_residual_mem_embeddedOrthogonal`:
if every standard residual `y - B(x,y) Q(x)⁻¹x` lies in
`scaledComplementOvermodule C m`, then the embedded coordinate lattice lies in
the line-plus-scaled-complement overmodule. -/
lemma embeddedIntegralLatticeSubmodule_le_line_sup_scaledComplementOvermodule_of_residual_mem_scaledComplement
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (m : ℤ) :
    (∀ y : Fin n → ℤ,
      intVectorToRatLinear n y +
          (-(L.bilinearFormValue x y) : ℤ) •
            ((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x) ∈
        scaledComplementOvermodule C m) →
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔ scaledComplementOvermodule C m := by
  intro hresidual
  rintro v ⟨y, _hy, rfl⟩
  let g : Fin n → ℚ := (L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x
  let c : ℤ := L.bilinearFormValue x y
  refine Submodule.mem_sup.2
    ⟨c • g, ?_, intVectorToRatLinear n y + (-c) • g, ?_, ?_⟩
  · exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
  · simpa [g, c] using hresidual y
  · ext i
    simp [g, c, add_assoc]

/-- An integral vector is primitive when its coordinates generate the unit
ideal in `ℤ`. -/
def IsPrimitiveVector (x : Fin n → ℤ) : Prop :=
  Ideal.span (Set.range x) = ⊤

/-- A primitive coordinate vector has a Bezout dual row.

This is the algebraic first step in normalizing the varying primitive minimum
vector in the fixed-index reconstruction: the coordinates of `x` admit an
integral linear combination equal to `1`. -/
lemma exists_int_linear_combination_eq_one_of_isPrimitiveVector
    (x : Fin n → ℤ) (hx : IsPrimitiveVector x) :
    ∃ c : Fin n → ℤ, (∑ i, c i * x i) = 1 := by
  classical
  have htop : (1 : ℤ) ∈ Submodule.span ℤ (Set.range x) := by
    change (1 : ℤ) ∈ Ideal.span (Set.range x)
    rw [hx]
    simp
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at htop
  rcases htop with ⟨c, hc⟩
  refine ⟨fun i => c i, ?_⟩
  simpa [Finsupp.sum_fintype, smul_eq_mul, mul_comm] using hc

/-- A primitive coordinate vector admits an integral linear functional taking
value `1` on it. -/
lemma exists_linearForm_apply_eq_one_of_isPrimitiveVector
    (x : Fin n → ℤ) (hx : IsPrimitiveVector x) :
    ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ, f x = 1 := by
  classical
  rcases exists_int_linear_combination_eq_one_of_isPrimitiveVector x hx with
    ⟨c, hc⟩
  refine ⟨
    { toFun := fun y => ∑ i, c i * y i
      map_add' := by
        intro y z
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r y
        calc
          ∑ i, c i * (r * y i) = ∑ i, r * (c i * y i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = r * ∑ i, c i * y i := by
            rw [Finset.mul_sum] },
    hc⟩

/-- A linear functional taking value `1` on `x` makes the line `ℤx`
disjoint from its kernel. -/
lemma disjoint_span_singleton_ker_linearForm_of_apply_eq_one
    (x : Fin n → ℤ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ) (hf : f x = 1) :
    Disjoint (Submodule.span ℤ ({x} : Set (Fin n → ℤ))) (LinearMap.ker f) := by
  rw [Submodule.disjoint_def]
  intro y hyspan hyker
  rw [Submodule.mem_span_singleton] at hyspan
  rcases hyspan with ⟨r, rfl⟩
  rw [LinearMap.mem_ker] at hyker
  change f (r • x) = 0 at hyker
  have hfr : f (r • x) = r := by
    calc
      f (r • x) = r • f x := f.map_smul r x
      _ = r := by simp [hf]
  have hr : r = 0 := by
    rw [← hfr]
    exact hyker
  simp [hr]

/-- A linear functional taking value `1` on `x` splits the ambient coordinate
lattice as the line `ℤx` plus the kernel of the functional. -/
lemma span_singleton_sup_ker_linearForm_eq_top_of_apply_eq_one
    (x : Fin n → ℤ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ) (hf : f x = 1) :
    Submodule.span ℤ ({x} : Set (Fin n → ℤ)) ⊔ LinearMap.ker f = ⊤ := by
  rw [eq_top_iff]
  intro y _hy
  refine Submodule.mem_sup.2
    ⟨(f y) • x, ?_, y - (f y) • x, ?_, ?_⟩
  · rw [Submodule.mem_span_singleton]
    exact ⟨f y, rfl⟩
  · rw [LinearMap.mem_ker]
    change f (y - (f y) • x) = 0
    rw [map_sub]
    have hline : f ((f y) • x) = f y := by
      calc
        f ((f y) • x) = (f y) • f x := f.map_smul (f y) x
        _ = f y := by simp [hf]
    rw [hline]
    simp
  · simp

/-- A Bezout dual row lets one choose finite coordinates on its kernel and
extend the primitive line to an ambient coordinate basis.

This is the finite-coordinate input for the fixed-index normal-form step:
after the split `ℤx ⊕ ker(f) = ℤ^n`, Mathlib's PID basis theorem gives a
`Fin m`-indexed basis of `ker(f)`, and the product basis sends the distinguished
left index to the original primitive vector `x`. -/
lemma exists_basis_sum_ker_linearForm_of_apply_eq_one
    (x : Fin n → ℤ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ) (hf : f x = 1) :
    ∃ m : ℕ, ∃ b : Module.Basis (Unit ⊕ Fin m) ℤ (Fin n → ℤ),
      b (Sum.inl ()) = x ∧
        ∀ j : Fin m, b (Sum.inr j) ∈ LinearMap.ker f := by
  classical
  let p : Submodule ℤ (Fin n → ℤ) :=
    Submodule.span ℤ ({x} : Set (Fin n → ℤ))
  let q : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  have hx_ne : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at hf
    norm_num at hf
  have hpq : IsCompl p q := by
    refine ⟨?_, ?_⟩
    · exact disjoint_span_singleton_ker_linearForm_of_apply_eq_one x f hf
    · rw [codisjoint_iff]
      exact span_singleton_sup_ker_linearForm_eq_top_of_apply_eq_one x f hf
  let bp : Module.Basis Unit ℤ p :=
    (Module.Basis.singleton Unit ℤ).map
      (LinearEquiv.coord ℤ (Fin n → ℤ) x hx_ne).symm
  have hx_mem : x ∈ p := Submodule.mem_span_singleton_self x
  have hbp : bp () = (⟨x, hx_mem⟩ : p) := by
    simp [bp, p, LinearEquiv.toSpanNonzeroSingleton_one ℤ (Fin n → ℤ) x hx_ne]
  rcases Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) q with ⟨m, bq⟩
  let b : Module.Basis (Unit ⊕ Fin m) ℤ (Fin n → ℤ) :=
    (bp.prod bq).map (Submodule.prodEquivOfIsCompl p q hpq)
  refine ⟨m, b, ?_, ?_⟩
  · change Submodule.prodEquivOfIsCompl p q hpq ((bp.prod bq) (Sum.inl ())) = x
    simp [hbp]
  · intro j
    change Submodule.prodEquivOfIsCompl p q hpq ((bp.prod bq) (Sum.inr j)) ∈ q
    simp

/-- Reindex a primitive-line/kernel basis by `Fin n` and extract its square
unimodular coordinate matrix.

This is the algebraic reindexing step in the fixed-index normal-form argument:
given a basis indexed by `Unit ⊕ Fin m`, whose left vector is the primitive
vector and whose right vectors lie in the Bezout kernel, Lean identifies
`m + 1 = n`, reindexes the basis by `Fin n`, and builds the corresponding
unimodular integer matrix in the standard coordinate basis. -/
lemma exists_fin_basis_unimodular_matrix_of_basis_sum_ker_linearForm
    {m : ℕ} (x : Fin n → ℤ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (b : Module.Basis (Unit ⊕ Fin m) ℤ (Fin n → ℤ))
    (hb_line : b (Sum.inl ()) = x)
    (hb_ker : ∀ j : Fin m, b (Sum.inr j) ∈ LinearMap.ker f) :
    ∃ _hmn : m + 1 = n, ∃ e : Unit ⊕ Fin m ≃ Fin n,
      ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
        bFin (e (Sum.inl ())) = x ∧
          (∀ j : Fin m, bFin (e (Sum.inr j)) ∈ LinearMap.ker f) ∧
            ∃ P : Matrix (Fin n) (Fin n) ℤ,
              IsUnit P ∧ ∀ i j, P i j = bFin j i := by
  classical
  have hmn : m + 1 = n := by
    have h := Module.finrank_eq_card_basis b
    simp at h
    omega
  have hmn' : 1 + m = n := by omega
  let e : Unit ⊕ Fin m ≃ Fin n :=
    ((Equiv.sumCongr (finOneEquiv.symm) (Equiv.refl (Fin m))).trans
      finSumFinEquiv).trans (finCongr hmn')
  let bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ) := b.reindex e
  let P : Matrix (Fin n) (Fin n) ℤ := (Pi.basisFun ℤ (Fin n)).toMatrix bFin
  refine ⟨hmn, e, bFin, ?_, ?_, P, ?_, ?_⟩
  · simp [bFin, hb_line]
  · intro j
    simpa [bFin] using hb_ker j
  · haveI : Invertible P := (Pi.basisFun ℤ (Fin n)).invertibleToMatrix bFin
    exact isUnit_of_invertible P
  · intro i j
    change (Pi.basisFun ℤ (Fin n)).toMatrix bFin i j = bFin j i
    rw [Module.Basis.toMatrix_apply]
    rfl

/-- A primitive coordinate vector admits a Bezout row whose kernel has finite
coordinates extending the primitive line to an ambient basis. -/
lemma exists_linearForm_basis_sum_ker_of_isPrimitiveVector
    (x : Fin n → ℤ) (hx : IsPrimitiveVector x) :
    ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ, ∃ m : ℕ,
      ∃ b : Module.Basis (Unit ⊕ Fin m) ℤ (Fin n → ℤ),
        f x = 1 ∧ b (Sum.inl ()) = x ∧
          ∀ j : Fin m, b (Sum.inr j) ∈ LinearMap.ker f := by
  rcases exists_linearForm_apply_eq_one_of_isPrimitiveVector x hx with ⟨f, hf⟩
  rcases exists_basis_sum_ker_linearForm_of_apply_eq_one x f hf with
    ⟨m, b, hb_line, hb_ker⟩
  exact ⟨f, m, b, hf, hb_line, hb_ker⟩

/-- A primitive coordinate vector admits a `Fin n`-indexed ambient basis with
an explicit unimodular coordinate matrix.

This packages the Bezout dual row, the finite kernel basis, and the
`Unit ⊕ Fin m` to `Fin n` reindexing.  It is the square-matrix normalization
input for the remaining fixed-index source reconstruction: the primitive
vector is one distinguished column of a unimodular coordinate matrix, and the
other columns lie in the kernel of the chosen dual functional. -/
lemma exists_linearForm_fin_basis_unimodular_matrix_of_isPrimitiveVector
    (x : Fin n → ℤ) (hx : IsPrimitiveVector x) :
    ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ, ∃ m : ℕ, ∃ _hmn : m + 1 = n,
      ∃ e : Unit ⊕ Fin m ≃ Fin n,
        ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
          f x = 1 ∧ bFin (e (Sum.inl ())) = x ∧
            (∀ j : Fin m, bFin (e (Sum.inr j)) ∈ LinearMap.ker f) ∧
              ∃ P : Matrix (Fin n) (Fin n) ℤ,
                IsUnit P ∧ ∀ i j, P i j = bFin j i := by
  rcases exists_linearForm_basis_sum_ker_of_isPrimitiveVector x hx with
    ⟨f, m, b, hf, hb_line, hb_ker⟩
  rcases exists_fin_basis_unimodular_matrix_of_basis_sum_ker_linearForm
      x f b hb_line hb_ker with
    ⟨hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP⟩
  exact ⟨f, m, hmn, e, bFin, hf, hbFin_line, hbFin_ker, P, hP_unit, hP⟩

/-- The primitive-line basis normalization can be read as a matrix-vector
identity: the coordinate unit vector attached to the distinguished line is
sent to the primitive vector by the unimodular basis matrix. -/
lemma exists_linearForm_fin_basis_unimodular_matrix_mulVec_single_of_isPrimitiveVector
    (x : Fin n → ℤ) (hx : IsPrimitiveVector x) :
    ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ, ∃ m : ℕ, ∃ _hmn : m + 1 = n,
      ∃ e : Unit ⊕ Fin m ≃ Fin n,
        ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
          f x = 1 ∧ bFin (e (Sum.inl ())) = x ∧
            (∀ j : Fin m, bFin (e (Sum.inr j)) ∈ LinearMap.ker f) ∧
              ∃ P : Matrix (Fin n) (Fin n) ℤ,
                IsUnit P ∧ (∀ i j, P i j = bFin j i) ∧
                  P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = x := by
  rcases exists_linearForm_fin_basis_unimodular_matrix_of_isPrimitiveVector
      x hx with
    ⟨f, m, hmn, e, bFin, hf, hbFin_line, hbFin_ker, P, hP_unit, hP⟩
  refine ⟨f, m, hmn, e, bFin, hf, hbFin_line, hbFin_ker, P, hP_unit, hP, ?_⟩
  ext i
  simp only [Matrix.mulVec, dotProduct, hP]
  rw [← hbFin_line]
  change (∑ j : Fin n,
      bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j) =
    bFin (e (Sum.inl ())) i
  calc
    (∑ j : Fin n,
        bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j) =
        bFin (e (Sum.inl ())) i *
          ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) (e (Sum.inl ())) := by
          refine Finset.sum_eq_single
            (s := (Finset.univ : Finset (Fin n)))
            (f := fun j : Fin n =>
              bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j)
            (e (Sum.inl ())) ?_ ?_
          · intro j _hj hne
            simp [Pi.single_eq_of_ne hne]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ _))
    _ = bFin (e (Sum.inl ())) i := by
      simp

/-- For a primitive-line/kernel basis matrix, the Bezout row reads off the
distinguished coordinate.

If the columns of `P` are the basis vectors extending `x`, the left
distinguished column is `x`, and all other columns lie in `ker f`, then
applying `f` to `P.mulVec y` keeps only the distinguished coefficient of `y`.
This is the row-coordinate consequence needed for the fixed-index normal-form
step. -/
lemma linearForm_apply_basis_matrix_mulVec_eq_distinguished_coord
    {m : ℕ} (x : Fin n → ℤ) (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (e : Unit ⊕ Fin m ≃ Fin n)
    (bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hf : f x = 1)
    (hbFin_line : bFin (e (Sum.inl ())) = x)
    (hbFin_ker : ∀ j : Fin m, bFin (e (Sum.inr j)) ∈ LinearMap.ker f)
    (P : Matrix (Fin n) (Fin n) ℤ)
    (hP : ∀ i j, P i j = bFin j i) :
    ∀ y : Fin n → ℤ, f (P.mulVec y) = y (e (Sum.inl ())) := by
  classical
  intro y
  have hvec : P.mulVec y = ∑ j : Fin n, y j • bFin j := by
    ext i
    simp [Matrix.mulVec, dotProduct, hP, mul_comm]
  rw [hvec, map_sum]
  have hker_of_ne :
      ∀ j : Fin n, j ≠ e (Sum.inl ()) → bFin j ∈ LinearMap.ker f := by
    intro j hj
    cases hpre : e.symm j with
    | inl u =>
        have hunit : u = () := Subsingleton.elim u ()
        have hj_eq : j = e (Sum.inl ()) := by
          calc
            j = e (e.symm j) := by simp
            _ = e (Sum.inl ()) := by rw [hpre, hunit]
        exact False.elim (hj hj_eq)
    | inr k =>
        have hj_eq : j = e (Sum.inr k) := by
          calc
            j = e (e.symm j) := by simp
            _ = e (Sum.inr k) := by rw [hpre]
        simpa [hj_eq] using hbFin_ker k
  refine Finset.sum_eq_single (e (Sum.inl ())) ?_ ?_ |>.trans ?_
  · intro j _hj hj_ne
    have hjker : bFin j ∈ LinearMap.ker f := hker_of_ne j hj_ne
    rw [LinearMap.mem_ker] at hjker
    rw [map_smul, hjker]
    simp
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · rw [map_smul, hbFin_line, hf]
    simp

/-- A basis matrix built from a `Fin n`-indexed basis sends the coordinate
vector of the basis representation back to the represented vector. -/
lemma basis_matrix_mulVec_repr
    (bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (P : Matrix (Fin n) (Fin n) ℤ)
    (hP : ∀ i j, P i j = bFin j i)
    (v : Fin n → ℤ) :
    P.mulVec (fun j : Fin n => bFin.repr v j) = v := by
  have hvec :
      P.mulVec (fun j : Fin n => bFin.repr v j) =
        ∑ j : Fin n, (bFin.repr v j) • bFin j := by
    ext i
    simp [Matrix.mulVec, dotProduct, hP, mul_comm]
  rw [hvec]
  simpa using bFin.sum_repr v

/-- The coordinate block with columns the non-distinguished coordinate
vectors for an index equivalence `Unit ⊕ Fin m ≃ Fin n`. -/
def distinguishedKernelBlockMatrix {m : ℕ}
    (e : Unit ⊕ Fin m ≃ Fin n) : Matrix (Fin n) (Fin m) ℤ :=
  fun i j => if i = e (Sum.inr j) then (1 : ℤ) else 0

/-- The explicit block matrix selecting the non-distinguished coordinates of a
primitive-row basis has transformed column range equal to the row kernel.

This is the elementary Smith/block normal form for a surjective integral row
once a basis has been chosen with the row reading off the distinguished
coordinate. -/
lemma linearForm_basis_matrix_kernel_block_range_eq_ker
    {m : ℕ} (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (e : Unit ⊕ Fin m ≃ Fin n)
    (bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (P : Matrix (Fin n) (Fin n) ℤ)
    (hP : ∀ i j, P i j = bFin j i)
    (hrow : ∀ y : Fin n → ℤ, f (P.mulVec y) = y (e (Sum.inl ()))) :
    LinearMap.range (Matrix.toLin' (P * distinguishedKernelBlockMatrix e)) =
      LinearMap.ker f := by
  classical
  let C : Matrix (Fin n) (Fin m) ℤ := distinguishedKernelBlockMatrix e
  ext v
  constructor
  · intro hv
    rcases hv with ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    have hmul :
        Matrix.toLin' (P * C) z = P.mulVec (C.mulVec z) := by
      ext i
      simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    rw [hmul, hrow]
    simp [C, distinguishedKernelBlockMatrix, Matrix.mulVec, dotProduct]
  · intro hv
    rw [LinearMap.mem_ker] at hv
    let y : Fin n → ℤ := fun j => bFin.repr v j
    have hy_eq : P.mulVec y = v :=
      basis_matrix_mulVec_repr bFin P hP v
    have hy_dist : y (e (Sum.inl ())) = 0 := by
      have hfy : f (P.mulVec y) = 0 := by
        rw [hy_eq]
        exact hv
      rw [hrow y] at hfy
      exact hfy
    let z : Fin m → ℤ := fun j => y (e (Sum.inr j))
    refine ⟨z, ?_⟩
    change Matrix.toLin' (P * C) z = v
    calc
      Matrix.toLin' (P * C) z = P.mulVec (C.mulVec z) := by
        ext i
        simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct,
          Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = P.mulVec y := by
        congr 1
        ext j
        cases hpre : e.symm j with
        | inl u =>
            have hu : u = () := Subsingleton.elim u ()
            have hj : j = e (Sum.inl ()) := by
              calc
                j = e (e.symm j) := by simp
                _ = e (Sum.inl ()) := by rw [hpre, hu]
            rw [hj, hy_dist]
            simp only [C, distinguishedKernelBlockMatrix, Matrix.mulVec, dotProduct]
            refine Finset.sum_eq_zero fun k _hk => ?_
            have hne : e (Sum.inl ()) ≠ e (Sum.inr k) := by
              intro heq
              exact Sum.inl_ne_inr (e.injective heq)
            simp [hne]
        | inr k =>
            have hj : j = e (Sum.inr k) := by
              calc
                j = e (e.symm j) := by simp
                _ = e (Sum.inr k) := by rw [hpre]
            rw [hj]
            simp only [C, distinguishedKernelBlockMatrix, Matrix.mulVec, dotProduct]
            calc
              (∑ l : Fin m,
                  (if e (Sum.inr k) = e (Sum.inr l) then (1 : ℤ) else 0) * z l) =
                  (if e (Sum.inr k) = e (Sum.inr k) then (1 : ℤ) else 0) * z k := by
                    refine Finset.sum_eq_single k ?_ ?_
                    · intro l _hl hlk
                      have hne : e (Sum.inr k) ≠ e (Sum.inr l) := by
                        intro heq
                        have hkl : k = l := Sum.inr.inj (e.injective heq)
                        exact hlk hkl.symm
                      simp [hne]
                    · intro hk
                      exact False.elim (hk (Finset.mem_univ k))
              _ = y (e (Sum.inr k)) := by simp [z]
      _ = v := hy_eq

/-- A surjective integral row admits a unimodular coordinate basis in which
the row is the distinguished coordinate and the remaining coordinate block
spans its kernel.

This is the primitive-row Smith/block normal form used in the fixed-index
reconstruction step. -/
lemma exists_surjective_linearForm_unimodular_kernel_block_normal_form
    (f : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (hf_surj : LinearMap.range f = ⊤) :
    ∃ x : Fin n → ℤ, f x = 1 ∧
      ∃ m : ℕ, ∃ _hmn : m + 1 = n,
        ∃ e : Unit ⊕ Fin m ≃ Fin n,
          ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
            bFin (e (Sum.inl ())) = x ∧
              (∀ j : Fin m, bFin (e (Sum.inr j)) ∈ LinearMap.ker f) ∧
                ∃ P : Matrix (Fin n) (Fin n) ℤ,
                  IsUnit P ∧ (∀ i j, P i j = bFin j i) ∧
                    P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = x ∧
                      (∀ y : Fin n → ℤ, f (P.mulVec y) = y (e (Sum.inl ()))) ∧
                        LinearMap.range
                            (Matrix.toLin' (P * distinguishedKernelBlockMatrix e)) =
                          LinearMap.ker f := by
  have h_one : (1 : ℤ) ∈ LinearMap.range f := by
    rw [hf_surj]
    trivial
  rcases h_one with ⟨x, hf_x⟩
  rcases exists_basis_sum_ker_linearForm_of_apply_eq_one x f hf_x with
    ⟨m, b, hb_line, hb_ker⟩
  rcases exists_fin_basis_unimodular_matrix_of_basis_sum_ker_linearForm
      x f b hb_line hb_ker with
    ⟨hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP⟩
  have hP_single :
      P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = x := by
    ext i
    simp only [Matrix.mulVec, dotProduct, hP]
    rw [← hbFin_line]
    change (∑ j : Fin n,
        bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j) =
      bFin (e (Sum.inl ())) i
    calc
      (∑ j : Fin n,
          bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j) =
          bFin (e (Sum.inl ())) i *
            ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) (e (Sum.inl ())) := by
            refine Finset.sum_eq_single
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n =>
                bFin j i * ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) j)
              (e (Sum.inl ())) ?_ ?_
            · intro j _hj hne
              simp [Pi.single_eq_of_ne hne]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ _))
      _ = bFin (e (Sum.inl ())) i := by
        simp
  have hrow :
      ∀ y : Fin n → ℤ, f (P.mulVec y) = y (e (Sum.inl ())) :=
    linearForm_apply_basis_matrix_mulVec_eq_distinguished_coord
      x f e bFin hf_x hbFin_line hbFin_ker P hP
  exact ⟨x, hf_x, m, hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP,
    hP_single, hrow,
    linearForm_basis_matrix_kernel_block_range_eq_ker
      (f := f) (e := e) (bFin := bFin) (P := P) hP hrow⟩

/-- Reindexing the columns of an integer matrix by an equivalence does not
change its column range. -/
lemma matrix_toLin_range_submatrix_col_equiv
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (C : Matrix (Fin n) κ ℤ) (e : κ' ≃ κ) :
    LinearMap.range (Matrix.toLin' (C.submatrix id e)) =
      LinearMap.range (Matrix.toLin' C) := by
  ext v
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨fun k : κ => z (e.symm k), ?_⟩
    rw [← hz]
    ext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Matrix.submatrix, id_eq]
    simpa using
      (Equiv.sum_comp e (fun k : κ => C i k * z (e.symm k))).symm
  · rintro ⟨z, hz⟩
    refine ⟨fun j : κ' => z (e j), ?_⟩
    rw [← hz]
    ext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Matrix.submatrix, id_eq]
    simpa using Equiv.sum_comp e (fun k : κ => C i k * z k)

/-- The ideal generated by a finite family of integers is generated by their
`Finset.gcd`.

This is the coordinate-content bridge used to relate the project definition of
primitive vectors to the standard gcd normalization of an integral vector. -/
lemma span_finset_image_eq_span_gcd {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) :
    Ideal.span (Set.image f (s : Set α)) = Ideal.span ({s.gcd f} : Set ℤ) := by
  classical
  refine s.induction_on ?empty ?insert
  · simp
  · intro a s _ha ih
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, ih]
    rw [Finset.gcd_insert]
    rw [span_gcd]
    simp [Ideal.span_insert]

/-- If the gcd of the coordinates is one, then the vector is primitive in the
coordinate-ideal sense. -/
lemma isPrimitiveVector_of_finset_gcd_eq_one (x : Fin n → ℤ)
    (hgcd : (Finset.univ.gcd x) = 1) : IsPrimitiveVector x := by
  simpa [IsPrimitiveVector, hgcd]
    using span_finset_image_eq_span_gcd
      (s := (Finset.univ : Finset (Fin n))) (f := x)

/-- Every nonzero integral coordinate vector is a nonzero integer multiple of
a vector whose coordinate gcd is one.

This is the formal version of dividing a vector by the gcd of its coordinates,
which is the first algebraic step behind choosing a primitive minimum vector
in Schulze--Pillot's fixed-determinant class-number proof. -/
lemma exists_gcd_one_multiple_of_nonzero (x : Fin n → ℤ) (hx : x ≠ 0) :
    ∃ c : ℤ, ∃ z : Fin n → ℤ,
      c ≠ 0 ∧ (Finset.univ.gcd z) = 1 ∧ x = c • z := by
  classical
  obtain ⟨i, hxi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let c : ℤ := Finset.univ.gcd x
  let z : Fin n → ℤ := fun i => x i / c
  have hc_ne : c ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨i, Finset.mem_univ i, hxi⟩
  have hz_gcd : (Finset.univ.gcd z) = 1 :=
    Finset.gcd_div_eq_one (s := (Finset.univ : Finset (Fin n)))
      (f := x) (i := i) (Finset.mem_univ i) hxi
  refine ⟨c, z, hc_ne, hz_gcd, ?_⟩
  ext j
  change x j = c * (x j / c)
  rw [Int.mul_ediv_cancel']
  exact Finset.gcd_dvd (s := (Finset.univ : Finset (Fin n))) (f := x)
    (Finset.mem_univ j)

/-- A vector attaining the positive minimum of the quadratic form is primitive.

If a minimum vector were a nonunit multiple of another integral vector, the
quadratic homogeneity would divide its positive value by a square and produce
a smaller nonzero value, contradicting minimality. -/
lemma isPrimitiveVector_of_quadForm_minimum (L : PositiveDefiniteIntegralLattice n) {μ : ℤ}
    (hμ : 0 < μ) {x : Fin n → ℤ} (hx_ne : x ≠ 0)
    (hx_value : L.quadForm x = μ)
    (hx_minimum : ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) :
    IsPrimitiveVector x := by
  classical
  rcases exists_gcd_one_multiple_of_nonzero x hx_ne with
    ⟨c, z, hc_ne, hz_gcd, hx_eq⟩
  have hz_ne : z ≠ 0 := by
    intro hz
    apply hx_ne
    rw [hx_eq, hz]
    simp
  have hquad_z_pos : 0 < L.quadForm z := L.quadForm_pos hz_ne
  have hμ_eq : μ = c ^ 2 * L.quadForm z := by
    rw [← hx_value, hx_eq, L.quadForm_smul]
  have hmul_le : c ^ 2 * L.quadForm z ≤ L.quadForm z := by
    rw [← hμ_eq]
    exact hx_minimum z hz_ne
  have hc_sq_one : c ^ 2 = 1 := by
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc_ne
    nlinarith
  rcases sq_eq_one_iff.mp hc_sq_one with hc | hc
  · simpa [hx_eq, hc] using isPrimitiveVector_of_finset_gcd_eq_one z hz_gcd
  · apply isPrimitiveVector_of_finset_gcd_eq_one
    have hx_gcd : Finset.univ.gcd x = 1 := by
      rw [hx_eq, hc]
      simpa [hz_gcd] using
        (Finset.gcd_mul_left (s := (Finset.univ : Finset (Fin n)))
          (f := z) (a := (-1 : ℤ)))
    exact hx_gcd

/-- A nonzero integral vector attaining a positive real matrix minimum is
primitive.

This is the matrix-form analogue of
`isPrimitiveVector_of_quadForm_minimum`, needed in the Hermite normal-form
setup before extending a minimum vector to a unimodular integral basis. -/
lemma _root_.Matrix.isPrimitiveVector_of_dotProduct_mulVec_minimum
    (S : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ} {x : Fin n → ℤ}
    (hμ : 0 < μ) (hx_ne : x ≠ 0)
    (hx_value :
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) = μ)
    (hx_minimum :
      ∀ y : Fin n → ℤ, y ≠ 0 →
        μ ≤
          (let yℝ : Fin n → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ S.mulVec yℝ)) :
    IsPrimitiveVector x := by
  classical
  rcases exists_gcd_one_multiple_of_nonzero x hx_ne with
    ⟨c, z, hc_ne, hz_gcd, hx_eq⟩
  have hz_ne : z ≠ 0 := by
    intro hz
    apply hx_ne
    rw [hx_eq, hz]
    simp
  let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
  let qz : ℝ := zℝ ⬝ᵥ S.mulVec zℝ
  have hx_value_scaled : μ = (c : ℝ) ^ 2 * qz := by
    rw [← hx_value]
    dsimp only
    subst x
    simp [zℝ, qz, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm, pow_two]
  have hqz_pos : 0 < qz := by
    have hc_sq_pos : 0 < (c : ℝ) ^ 2 := by
      exact sq_pos_of_ne_zero (by exact_mod_cast hc_ne)
    nlinarith [hμ, hx_value_scaled]
  have hmul_le : (c : ℝ) ^ 2 * qz ≤ qz := by
    rw [← hx_value_scaled]
    exact hx_minimum z hz_ne
  have hc_sq_le_one : (c : ℝ) ^ 2 ≤ 1 := by
    nlinarith [hqz_pos, hmul_le]
  have hc_sq_one : c ^ 2 = 1 := by
    have hc_sq_pos : (0 : ℤ) < c ^ 2 := sq_pos_of_ne_zero hc_ne
    have hc_sq_le_one_int : c ^ 2 ≤ 1 := by
      exact_mod_cast hc_sq_le_one
    omega
  rcases sq_eq_one_iff.mp hc_sq_one with hc | hc
  · simpa [hx_eq, hc] using isPrimitiveVector_of_finset_gcd_eq_one z hz_gcd
  · apply isPrimitiveVector_of_finset_gcd_eq_one
    have hx_gcd : Finset.univ.gcd x = 1 := by
      rw [hx_eq, hc]
      simpa [hz_gcd] using
        (Finset.gcd_mul_left (s := (Finset.univ : Finset (Fin n)))
          (f := z) (a := (-1 : ℤ)))
    exact hx_gcd

/-- Rank-at-least-two Hermite normal-form data up to the final reindexing.

For an arbitrary positive definite real matrix, Lean now chooses an integral
minimum vector, proves it primitive, extends it to a unimodular integral
basis, and transports the matrix-minimum hypotheses through the corresponding
basis-change congruence.  The remaining normal-form work is to reindex the
resulting `Fin n` matrix along `e : Unit ⊕ Fin m ≃ Fin n` and apply
`Matrix.hermite_rank_succ_bound_of_schurComplement`. -/
lemma _root_.Matrix.exists_rankAtLeastTwo_minimum_basis_change_to_distinguished
    (S : Matrix (Fin n) (Fin n) ℝ) (hS_symm : S.IsSymm) (hS_pos : S.PosDef)
    (hn : 2 ≤ n) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ x : Fin n → ℤ, x ≠ 0 ∧
      IsPrimitiveVector x ∧
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) = μ ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤
        (let yℝ : Fin n → ℝ := fun i => (y i : ℝ)
         yℝ ⬝ᵥ S.mulVec yℝ)) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ _hmn : m + 1 = n,
        ∃ e : Unit ⊕ Fin m ≃ Fin n,
          ∃ P : Matrix (Fin n) (Fin n) ℤ,
            IsUnit P ∧
              P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = x ∧
              ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
                  (P.map (Int.cast : ℤ → ℝ))).IsSymm ∧
              ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
                  (P.map (Int.cast : ℤ → ℝ))).PosDef ∧
              ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
                  (P.map (Int.cast : ℤ → ℝ))).det = S.det ∧
              ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
                  (P.map (Int.cast : ℤ → ℝ)))
                    (e (Sum.inl ())) (e (Sum.inl ())) = μ ∧
              ∀ z : Fin n → ℤ, z ≠ 0 →
                μ ≤
                  (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
                   zℝ ⬝ᵥ
                    (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
                      (P.map (Int.cast : ℤ → ℝ))).mulVec zℝ)) := by
  classical
  rcases Matrix.exists_dotProduct_mulVec_int_minimum_value S hS_pos (by omega) with
    ⟨μ, hμ_pos, x, hx_ne, hx_value, hx_minimum⟩
  have hx_primitive : IsPrimitiveVector x :=
    Matrix.isPrimitiveVector_of_dotProduct_mulVec_minimum
      S hμ_pos hx_ne hx_value hx_minimum
  rcases exists_linearForm_fin_basis_unimodular_matrix_mulVec_single_of_isPrimitiveVector
      x hx_primitive with
    ⟨_f, m, hmn, e, _bFin, _hf, _hbFin_line, _hbFin_ker,
      P, hP_unit, _hP, hP_mul⟩
  have hm_pos : 0 < m := by omega
  have hT_symm :
      ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ))).IsSymm :=
    Matrix.IsSymm.basis_change_intCast hS_symm P
  have hT_pos :
      ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ))).PosDef :=
    Matrix.PosDef.basis_change_intCast_of_isUnit hS_pos P hP_unit
  have hT_det :
      ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ))).det = S.det :=
    Matrix.det_basis_change_intCast_of_isUnit S P hP_unit
  have hT_diag :
      ((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
          (P.map (Int.cast : ℤ → ℝ)))
            (e (Sum.inl ())) (e (Sum.inl ())) = μ := by
    have hdiag :=
      Matrix.basis_change_intCast_apply_self_eq_quadratic_of_mulVec
        S P (e (Sum.inl ())) x hP_mul
    simpa [hx_value] using hdiag
  have hT_min :
      ∀ z : Fin n → ℤ, z ≠ 0 →
        μ ≤
          (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
           zℝ ⬝ᵥ
            (((P.map (Int.cast : ℤ → ℝ))ᵀ * S *
              (P.map (Int.cast : ℤ → ℝ))).mulVec zℝ)) :=
    Matrix.minimum_le_basis_change_intCast_of_isUnit S P hP_unit μ hx_minimum
  exact
    ⟨μ, hμ_pos, x, hx_ne, hx_primitive, hx_value, hx_minimum,
      m, hm_pos, hmn, e, P, hP_unit, hP_mul, hT_symm, hT_pos,
      hT_det, hT_diag, hT_min⟩

/-- Apply the `Unit ⊕ Fin m` Hermite induction step, with an explicit
lower-rank Hermite hypothesis, after reindexing a transported `Fin n` matrix
along the equivalence supplied by the normal-form construction.

This is the induction-hypothesis form of the final reindexing bridge: the
block theorem sees the reindexed matrix `T.submatrix e e`, while downstream
statements use the original `Fin n`-indexed transported matrix `T`. -/
lemma _root_.Matrix.hermite_bound_of_reindexed_distinguished_minimum_of_lower_rank_bound
    {n m : ℕ} (hm : 0 < m) (hmn : m + 1 = n)
    (hlower :
      ∀ W : Matrix (Fin m) (Fin m) ℝ, W.IsSymm → W.PosDef →
        ∃ y : Fin m → ℤ, y ≠ 0 ∧
          (let yℝ : Fin m → ℝ := fun i => (y i : ℝ)
           yℝ ⬝ᵥ W.mulVec yℝ) ≤
            Real.rpow (4 / 3 : ℝ) (((m : ℝ) - 1) / 2) *
              Real.rpow W.det ((m : ℝ)⁻¹))
    (T : Matrix (Fin n) (Fin n) ℝ) (e : Unit ⊕ Fin m ≃ Fin n)
    (hT_symm : T.IsSymm) (hT_pos : T.PosDef)
    (μ : ℝ) (hdiag : T (e (Sum.inl ())) (e (Sum.inl ())) = μ)
    (hmin :
      ∀ z : Fin n → ℤ, z ≠ 0 →
        μ ≤
          (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
           zℝ ⬝ᵥ T.mulVec zℝ)) :
    μ ≤ Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
      Real.rpow T.det ((n : ℝ)⁻¹) := by
  classical
  let U : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) ℝ := T.submatrix e e
  have hU_symm : U.IsSymm := Matrix.IsSymm.submatrix_equiv T e hT_symm
  have hU_pos : U.PosDef := Matrix.PosDef.submatrix_equiv T e hT_pos
  have hU_diag : U (Sum.inl ()) (Sum.inl ()) = μ := by
    simpa [U, Matrix.submatrix] using hdiag
  have hU_min :
      ∀ z : Unit ⊕ Fin m → ℤ, z ≠ 0 →
        μ ≤
          (let zℝ : Unit ⊕ Fin m → ℝ := fun i => (z i : ℝ)
           zℝ ⬝ᵥ U.mulVec zℝ) := by
    intro z hz
    let zFin : Fin n → ℤ := fun i => z (e.symm i)
    have hzFin_ne : zFin ≠ 0 := by
      intro hzFin
      apply hz
      ext i
      have hi := congr_fun hzFin (e i)
      simpa [zFin] using hi
    have hz_bound := hmin zFin hzFin_ne
    have hz_reindex :=
      Matrix.dotProduct_mulVec_submatrix_equiv_int T e z
    simpa [U, zFin] using hz_reindex.symm ▸ hz_bound
  have hblock :
      μ ≤ Real.rpow (4 / 3 : ℝ) ((m : ℝ) / 2) *
        Real.rpow U.det (((m : ℝ) + 1)⁻¹) :=
    Matrix.hermite_rank_succ_bound_of_schurComplement_of_lower_rank_bound
      hm hlower U hU_symm hU_pos μ hU_diag hU_min
  have hn_real : (n : ℝ) = (m : ℝ) + 1 := by
    exact_mod_cast hmn.symm
  have hconst_exp : (m : ℝ) / 2 = (((n : ℝ) - 1) / 2) := by
    rw [hn_real]
    ring
  have hdet_exp : (((m : ℝ) + 1)⁻¹) = ((n : ℝ)⁻¹) := by
    rw [hn_real]
  simpa [U, Matrix.det_submatrix_equiv_self, hconst_exp, hdet_exp] using hblock

/-- Combine the rank-at-least-two normal-form package with the reindexed block
Hermite bridge, using an explicit lower-rank Hermite hypothesis, to recover
the original `Fin n` short-vector statement.

This is the induction-hypothesis form of the normal-form assembly.  The
minimum vector chosen for the original matrix is moved to a distinguished
coordinate, the transported matrix is reindexed as `Unit ⊕ Fin m`, the block
lemma gives the Hermite bound for the transported minimum, and the determinant
is transported back to the original matrix. -/
lemma _root_.Matrix.hermite_positive_definite_matrix_short_vector_bound_rankAtLeastTwo_of_lower_rank_bound
    (n : ℕ) (hn : 2 ≤ n)
    (hlower :
      ∀ ⦃m : ℕ⦄, 0 < m → m + 1 = n →
        ∀ W : Matrix (Fin m) (Fin m) ℝ, W.IsSymm → W.PosDef →
          ∃ y : Fin m → ℤ, y ≠ 0 ∧
            (let yℝ : Fin m → ℝ := fun i => (y i : ℝ)
             yℝ ⬝ᵥ W.mulVec yℝ) ≤
              Real.rpow (4 / 3 : ℝ) (((m : ℝ) - 1) / 2) *
                Real.rpow W.det ((m : ℝ)⁻¹))
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) ≤
        Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
          Real.rpow S.det ((n : ℝ)⁻¹) := by
  classical
  rcases Matrix.exists_rankAtLeastTwo_minimum_basis_change_to_distinguished
      S hS_symm hS_pos hn with
    ⟨μ, _hμ_pos, x, hx_ne, _hx_primitive, hx_value, _hx_minimum,
      m, hm_pos, hmn, e, P, _hP_unit, _hP_mul, hT_symm, hT_pos,
      hT_det, hT_diag, hT_min⟩
  let T : Matrix (Fin n) (Fin n) ℝ :=
    (P.map (Int.cast : ℤ → ℝ))ᵀ * S * (P.map (Int.cast : ℤ → ℝ))
  have hT_det' : T.det = S.det := by
    simpa [T] using hT_det
  have hμ_bound_T :
      μ ≤ Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
        Real.rpow T.det ((n : ℝ)⁻¹) := by
    exact
      Matrix.hermite_bound_of_reindexed_distinguished_minimum_of_lower_rank_bound
        hm_pos hmn (hlower hm_pos hmn) T e (by simpa [T] using hT_symm)
        (by simpa [T] using hT_pos) μ (by simpa [T] using hT_diag)
        (by simpa [T] using hT_min)
  have hμ_bound_S :
      μ ≤ Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
        Real.rpow S.det ((n : ℝ)⁻¹) := by
    simpa [hT_det'] using hμ_bound_T
  refine ⟨x, hx_ne, ?_⟩
  simpa [hx_value] using hμ_bound_S

/-- Rank-at-least-two Hermite matrix bound by genuine induction on the rank.

This consumes the explicit lower-rank normal-form lemma
`Matrix.hermite_positive_definite_matrix_short_vector_bound_rankAtLeastTwo_of_lower_rank_bound`.
The base lower-rank case is the formal rank-one theorem, and the successor
lower-rank cases are supplied by the strong induction hypothesis. -/
theorem hermite_positive_definite_matrix_short_vector_bound_rankAtLeastTwo_induction
    (n : ℕ) (hn : 2 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) ≤
        Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
          Real.rpow S.det ((n : ℝ)⁻¹) := by
  revert hn S hS_symm hS_pos
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn S hS_symm hS_pos
      exact
        Matrix.hermite_positive_definite_matrix_short_vector_bound_rankAtLeastTwo_of_lower_rank_bound
          n hn
          (fun {m} hm hmn W hW_symm hW_pos => by
            by_cases hm_one : m = 1
            · subst m
              simpa using
                hermite_positive_definite_matrix_short_vector_bound_rank_one
                  W hW_symm hW_pos
            · have hm_two : 2 ≤ m := by omega
              have hm_lt : m < n := by omega
              exact ih m hm_lt hm_two W hW_symm hW_pos)
          S hS_symm hS_pos

/-- Hermite's matrix short-vector theorem for positive rank, using the formal
rank-one theorem and the rank-at-least-two induction theorem. -/
theorem hermite_positive_definite_matrix_short_vector_bound
    (n : ℕ) (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
       xℝ ⬝ᵥ S.mulVec xℝ) ≤
        Real.rpow (4 / 3 : ℝ) (((n : ℝ) - 1) / 2) *
          Real.rpow S.det ((n : ℝ)⁻¹) := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          simpa using
            hermite_positive_definite_matrix_short_vector_bound_rank_one
              S hS_symm hS_pos
      | succ n =>
          exact
            hermite_positive_definite_matrix_short_vector_bound_rankAtLeastTwo_induction
              (n + 2) (by omega) S hS_symm hS_pos

/-- Hermite bound for a symmetric positive definite matrix indexed by
`Unit ⊕ Fin k` whose distinguished diagonal entry `μ` is its minimum.
The block algebra is in
`Matrix.hermite_rank_succ_bound_of_schurComplement_of_lower_rank_bound`, and
the lower-rank bound comes from the positive-rank Hermite theorem. -/
lemma _root_.Matrix.hermite_rank_succ_bound_of_schurComplement
    {k : ℕ} (hk : 0 < k)
    (S : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ)
    (hS_symm : S.IsSymm) (hS_pos : S.PosDef)
    (μ : ℝ) (hdiag : S (Sum.inl ()) (Sum.inl ()) = μ)
    (hmin :
      ∀ x : Unit ⊕ Fin k → ℤ, x ≠ 0 →
        μ ≤
          (let xℝ : Unit ⊕ Fin k → ℝ := fun i => (x i : ℝ)
           xℝ ⬝ᵥ S.mulVec xℝ)) :
    μ ≤ Real.rpow (4 / 3 : ℝ) ((k : ℝ) / 2) *
      Real.rpow S.det (((k : ℝ) + 1)⁻¹) := by
  exact
    Matrix.hermite_rank_succ_bound_of_schurComplement_of_lower_rank_bound
      hk
      (fun W hW_symm hW_pos =>
        PositiveDefiniteIntegralLattice.hermite_positive_definite_matrix_short_vector_bound
          k hk W hW_symm hW_pos)
      S hS_symm hS_pos μ hdiag hmin

/-- The fixed-`pairingDeterminant` Hermite minimum bound in ranks at least two, now using
the formal matrix induction theorem rather than the early source axiom. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_hermite_minimum_real_bound
    (hn : 2 ≤ n) (d : ℤ) (_hd : 0 < d) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∀ μ : ℤ, 0 < μ →
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          (μ : ℝ) ≤ hermiteShortVectorRealBound n d := by
  intro L hdet μ _hμ hminimum
  obtain ⟨_xμ, _hxμ_ne, _hxμ_value, hμ_min⟩ := hminimum
  let S : Matrix (Fin n) (Fin n) ℝ := L.pairingMatrix.map (Int.cast : ℤ → ℝ)
  have hn_pos : 0 < n := by omega
  have hS_symm : S.IsSymm := by
    ext i j
    simp [S, Matrix.transpose_apply, L.form_symm.apply]
  obtain ⟨z, hz_ne, hz_bound⟩ :=
    hermite_positive_definite_matrix_short_vector_bound
      n hn_pos S hS_symm L.form_posDef
  have hμ_le_z : (μ : ℝ) ≤ (L.quadForm z : ℝ) := by
    exact_mod_cast hμ_min z hz_ne
  have hz_quad :
      (L.quadForm z : ℝ) =
        (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
         zℝ ⬝ᵥ S.mulVec zℝ) := by
    simp [S, L.quadForm_eq_dotProduct, Matrix.mulVec, dotProduct]
  have hdet_real : S.det = (d : ℝ) := by
    change (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).det = (d : ℝ)
    rw [← Int.cast_det]
    simpa [pairingDeterminant] using congrArg (fun z : ℤ => (z : ℝ)) hdet
  calc
    (μ : ℝ) ≤ (L.quadForm z : ℝ) := hμ_le_z
    _ = (let zℝ : Fin n → ℝ := fun i => (z i : ℝ)
         zℝ ⬝ᵥ S.mulVec zℝ) := hz_quad
    _ ≤ hermiteShortVectorRealBound n d := by
      simpa [hermiteShortVectorRealBound, hdet_real] using hz_bound

/-- The fixed-`pairingDeterminant` Hermite short-vector bound in ranks at least two,
deduced from the formal minimum-value bound. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_hermite_real_bound
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ x : Fin n → ℤ, x ≠ 0 ∧
        (L.quadForm x : ℝ) ≤ hermiteShortVectorRealBound n d := by
  intro L hdet
  have hn_pos : 0 < n := by omega
  obtain ⟨μ, hμ_pos, x, hx_ne, hx_value, hx_minimum⟩ :=
    exists_quadForm_minimum_value L hn_pos
  refine ⟨x, hx_ne, ?_⟩
  rw [hx_value]
  exact fixed_rank_atLeastTwo_positive_pairingDeterminant_hermite_minimum_real_bound
    hn d hd L hdet μ hμ_pos ⟨x, hx_ne, hx_value, hx_minimum⟩

/-- The fixed-`pairingDeterminant` Hermite short-vector bound in positive rank, using
only formal matrix Hermite results. -/
theorem fixed_rank_positive_pairingDeterminant_hermite_real_bound
    (hn : 0 < n) (d : ℤ) (hd : 0 < d) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ x : Fin n → ℤ, x ≠ 0 ∧
        (L.quadForm x : ℝ) ≤ hermiteShortVectorRealBound n d := by
  cases n with
  | zero =>
      cases hn
  | succ n =>
      cases n with
      | zero =>
          exact fixed_rank_one_positive_pairingDeterminant_hermite_real_bound d hd
      | succ n =>
          exact fixed_rank_atLeastTwo_positive_pairingDeterminant_hermite_real_bound
            (by omega) d hd

/-- The integer-rounded fixed-`pairingDeterminant` Hermite short-vector bound, using the
formal positive-rank Hermite real bound. -/
theorem fixed_rank_positive_pairingDeterminant_positive_short_vector_bound
    (hn : 0 < n) (d : ℤ) (hd : 0 < d) :
    ∃ B : ℕ, 0 < B ∧ ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x ≤ (B : ℤ) := by
  refine ⟨Nat.ceil (hermiteShortVectorRealBound n d), ?_⟩
  refine ⟨Nat.ceil_pos.mpr (hermiteShortVectorRealBound_pos n d hd), ?_⟩
  intro L hdet
  obtain ⟨x, hx, hx_bound⟩ :=
    fixed_rank_positive_pairingDeterminant_hermite_real_bound hn d hd L hdet
  refine ⟨x, hx, ?_⟩
  have hx_bound_int :
      (L.quadForm x : ℝ) ≤
        ((Nat.ceil (hermiteShortVectorRealBound n d) : ℕ) : ℝ) :=
    le_trans hx_bound (Nat.le_ceil _)
  exact Int.cast_le.mp (by
    exact_mod_cast hx_bound_int)

/-- Hermite's fixed-`pairingDeterminant` short-vector bound, using the formal
positive-rank Hermite real bound. -/
theorem fixed_rank_positive_pairingDeterminant_short_vector_bound
    (hn : 0 < n) (d : ℤ) (hd : 0 < d) :
    ∃ B : ℕ, ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x ≤ (B : ℤ) := by
  obtain ⟨B, _hB_pos, hB⟩ :=
    fixed_rank_positive_pairingDeterminant_positive_short_vector_bound hn d hd
  exact ⟨B, hB⟩

/-- Hermite's fixed-`pairingDeterminant` short-vector bound applied to the actual
minimum value, with no dependence on the early Hermite source axiom. -/
theorem fixed_rank_positive_pairingDeterminant_hermite_minimum_bound_of_matrix_induction
    (hn : 0 < n) (d : ℤ) (hd : 0 < d) :
    ∃ B : ℕ, ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ μ : ℤ, 0 < μ ∧ μ ≤ (B : ℤ) ∧
        ∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y := by
  obtain ⟨B, hB⟩ :=
    fixed_rank_positive_pairingDeterminant_short_vector_bound hn d hd
  refine ⟨B, ?_⟩
  intro L hdet
  obtain ⟨μ, hμ_pos, x, hx, hx_eq, hμ_min⟩ := exists_quadForm_minimum_value L hn
  obtain ⟨z, hz, hz_bound⟩ := hB L hdet
  refine ⟨μ, hμ_pos, ?_, x, hx, hx_eq, hμ_min⟩
  exact le_trans (hμ_min z hz) hz_bound

/-- The ideal `B(x,Λ)` generated by all Schulze--Pillot bilinear values
against lattice vectors. -/
def bilinearImageIdeal (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) : Ideal ℤ :=
  Ideal.span (Set.range fun y : Fin n → ℤ => L.bilinearFormValue x y)

/-- The ideal generated by the row values `B(x,-)` is exactly the range of the
corresponding integral linear functional. -/
lemma bilinearImageIdeal_eq_bilinearFormLinear_range
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    L.bilinearImageIdeal x = LinearMap.range (L.bilinearFormLinear x) := by
  ext z
  constructor
  · intro hz
    change z ∈
      Submodule.span ℤ (Set.range fun y : Fin n → ℤ => L.bilinearFormValue x y) at hz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    rcases hz with ⟨c, hc⟩
    refine ⟨c.sum fun y r => r • y, ?_⟩
    have hmap :
        L.bilinearFormLinear x (c.sum fun y r => r • y) =
          c.sum fun y r => r • L.bilinearFormLinear x y := by
      rw [map_finsuppSum]
      refine Finsupp.sum_congr ?_
      intro y _hy
      change L.bilinearFormValue x ((c y) • y) =
        c y * L.bilinearFormValue x y
      rw [bilinearFormValue_smul_right]
    rw [hmap]
    simpa [bilinearFormLinear_apply] using hc
  · rintro ⟨y, rfl⟩
    change L.bilinearFormValue x y ∈ L.bilinearImageIdeal x
    exact Ideal.subset_span (Set.mem_range_self y)

/-- The ideal `B(x,Λ)` is principal over `ℤ`. -/
lemma exists_bilinearImageIdeal_eq_span_singleton
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    ∃ a : ℤ, L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) := by
  classical
  exact ⟨Submodule.IsPrincipal.generator (L.bilinearImageIdeal x),
    (Ideal.span_singleton_generator (L.bilinearImageIdeal x)).symm⟩

/-- If `B(x,Λ)=aℤ`, then every pairing `B(x,y)` is divisible by `a`. -/
lemma dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ}
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (y : Fin n → ℤ) :
    a ∣ L.bilinearFormValue x y := by
  have hy_mem : L.bilinearFormValue x y ∈ L.bilinearImageIdeal x := by
    exact Ideal.subset_span (Set.mem_range_self y)
  rw [hindex, Ideal.mem_span_singleton] at hy_mem
  exact hy_mem

/-- If `B(x,Λ)=aℤ` with `a ≠ 0`, the bilinear row divided by `a` is an
integral linear functional.

This is the row that appears in the fixed-index normal form: it is the
primitive integral quotient of the Schulze--Pillot pairing row
`y ↦ B(x,y)`. -/
def quotientBilinearFormLinearOfIndex
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun y := L.bilinearFormValue x y / a
  map_add' y z := by
    obtain ⟨ky, hky⟩ :=
      L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex y
    obtain ⟨kz, hkz⟩ :=
      L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex z
    have hadd :
        L.bilinearFormValue x (y + z) =
          L.bilinearFormValue x y + L.bilinearFormValue x z := by
      change L.bilinearFormLinear x (y + z) =
        L.bilinearFormValue x y + L.bilinearFormValue x z
      rw [map_add]
      simp [bilinearFormLinear_apply]
    have hsum : a * ky + a * kz = a * (ky + kz) := by ring
    calc
      L.bilinearFormValue x (y + z) / a
          = (a * (ky + kz)) / a := by rw [hadd, hky, hkz, hsum]
      _ = ky + kz := Int.mul_ediv_cancel_left _ ha
      _ = a * ky / a + a * kz / a := by
          rw [Int.mul_ediv_cancel_left ky ha, Int.mul_ediv_cancel_left kz ha]
      _ = L.bilinearFormValue x y / a + L.bilinearFormValue x z / a := by
          rw [hky, hkz]
  map_smul' r y := by
    obtain ⟨k, hk⟩ :=
      L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex y
    have hmul : r * (a * k) = a * (r * k) := by ring
    calc
      L.bilinearFormValue x (r • y) / a
          = (a * (r * k)) / a := by
          rw [bilinearFormValue_smul_right, hk, hmul]
      _ = r * k := Int.mul_ediv_cancel_left _ ha
      _ = r • (a * k / a) := by
          rw [Int.mul_ediv_cancel_left k ha]
          simp
      _ = r • (L.bilinearFormValue x y / a) := by rw [hk]

@[simp]
lemma quotientBilinearFormLinearOfIndex_apply
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    quotientBilinearFormLinearOfIndex L x ha hindex y =
      L.bilinearFormValue x y / a := rfl

/-- If `B(x,Λ)=aℤ`, the quotient row `B(x,-)/a` is primitive: it takes the
value `1` on some integral vector. -/
lemma exists_quotientBilinearFormLinearOfIndex_apply_eq_one
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    ∃ y : Fin n → ℤ, quotientBilinearFormLinearOfIndex L x ha hindex y = 1 := by
  have ha_mem : a ∈ L.bilinearImageIdeal x := by
    rw [hindex]
    exact Ideal.mem_span_singleton_self a
  rw [bilinearImageIdeal_eq_bilinearFormLinear_range] at ha_mem
  rcases ha_mem with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [quotientBilinearFormLinearOfIndex_apply]
  have hvalue : L.bilinearFormValue x y = a := by
    simpa [bilinearFormLinear_apply] using hy
  rw [hvalue]
  exact Int.ediv_self ha

/-- Equivalently, the quotient row `B(x,-)/a` has full range.  This is the
row-primitivity input needed for the remaining Smith/normal-form source step. -/
lemma quotientBilinearFormLinearOfIndex_range_eq_top
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    LinearMap.range (quotientBilinearFormLinearOfIndex L x ha hindex) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro z
  rcases exists_quotientBilinearFormLinearOfIndex_apply_eq_one L x ha hindex with
    ⟨y, hy⟩
  refine ⟨z • y, ?_⟩
  rw [map_smul, hy]
  simp

/-- The quotient row really clears the chosen index generator:
`a * (B(x,y)/a) = B(x,y)`. -/
lemma mul_quotientBilinearFormLinearOfIndex_apply
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    a * quotientBilinearFormLinearOfIndex L x ha hindex y =
      L.bilinearFormValue x y := by
  obtain ⟨k, hk⟩ :=
    L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex y
  rw [quotientBilinearFormLinearOfIndex_apply, hk]
  simp [Int.mul_ediv_cancel_left _ ha]

/-- The kernel of the quotient bilinear row is exactly the full
`B`-orthogonal complement.

This turns the remaining fixed-index normal-form problem into a normal form
for a specific integral row, rather than an abstract orthogonal-submodule
containment. -/
lemma ker_quotientBilinearFormLinearOfIndex
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    LinearMap.ker (quotientBilinearFormLinearOfIndex L x ha hindex) =
      L.bilinearOrthogonalSubmodule x := by
  ext y
  constructor
  · intro hy
    rw [LinearMap.mem_ker] at hy
    rw [mem_bilinearOrthogonalSubmodule]
    rw [← mul_quotientBilinearFormLinearOfIndex_apply L x y ha hindex, hy]
    simp
  · intro hy
    rw [LinearMap.mem_ker]
    rw [mem_bilinearOrthogonalSubmodule] at hy
    rw [quotientBilinearFormLinearOfIndex_apply, hy]
    exact Int.zero_ediv a

/-- The quotient row `B(x,-)/a` has an explicit primitive-row block normal
form: after a unimodular coordinate change, the row is the distinguished
coordinate and the remaining coordinate block spans the full bilinear
orthogonal complement of `x`.

This specializes the abstract row normal form to the concrete
Schulze--Pillot quotient row, removing row-primitivity and kernel
identification from the fixed-index step. -/
lemma exists_quotientBilinearFormLinearOfIndex_unimodular_kernel_block_normal_form
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    ∃ w : Fin n → ℤ,
      quotientBilinearFormLinearOfIndex L x ha hindex w = 1 ∧
        ∃ m : ℕ, ∃ _hmn : m + 1 = n,
          ∃ e : Unit ⊕ Fin m ≃ Fin n,
            ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
              bFin (e (Sum.inl ())) = w ∧
                (∀ j : Fin m,
                  bFin (e (Sum.inr j)) ∈ L.bilinearOrthogonalSubmodule x) ∧
                  ∃ P : Matrix (Fin n) (Fin n) ℤ,
                    IsUnit P ∧ (∀ i j, P i j = bFin j i) ∧
                      P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = w ∧
                        (∀ y : Fin n → ℤ,
                          quotientBilinearFormLinearOfIndex L x ha hindex
                              (P.mulVec y) = y (e (Sum.inl ()))) ∧
                          LinearMap.range
                              (Matrix.toLin' (P * distinguishedKernelBlockMatrix e)) =
                            L.bilinearOrthogonalSubmodule x := by
  let q : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
    quotientBilinearFormLinearOfIndex L x ha hindex
  rcases exists_surjective_linearForm_unimodular_kernel_block_normal_form q
      (quotientBilinearFormLinearOfIndex_range_eq_top L x ha hindex) with
    ⟨w, hw, m, hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP,
      hP_single, hrow, hrange⟩
  refine ⟨w, hw, m, hmn, e, bFin, hbFin_line, ?_, P, hP_unit, hP,
    hP_single, hrow, ?_⟩
  · intro j
    simpa [q, ker_quotientBilinearFormLinearOfIndex L x ha hindex]
      using hbFin_ker j
  · simpa [q, ker_quotientBilinearFormLinearOfIndex L x ha hindex]
      using hrange

/-- In the quotient-row normal form, the original vector `x` has distinguished
coordinate `μ / a` when `Q(x)=μ`.

The kernel-block normal form chooses a vector `w` on which `B(x,-)/a` has value
`1`; this lemma records the complementary coordinate fact for the actual
minimum vector `x`.  This is the fixed vector-coordinate datum needed by the
remaining uniform normal-form step. -/
lemma exists_quotientBilinearFormLinearOfIndex_unimodular_kernel_block_normal_form_with_vector_coordinate
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a μ : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (hx_value : L.quadForm x = μ) :
    ∃ w : Fin n → ℤ,
      quotientBilinearFormLinearOfIndex L x ha hindex w = 1 ∧
        ∃ m : ℕ, ∃ _hmn : m + 1 = n,
          ∃ e : Unit ⊕ Fin m ≃ Fin n,
            ∃ bFin : Module.Basis (Fin n) ℤ (Fin n → ℤ),
              bFin (e (Sum.inl ())) = w ∧
                (∀ j : Fin m,
                  bFin (e (Sum.inr j)) ∈ L.bilinearOrthogonalSubmodule x) ∧
                  ∃ P : Matrix (Fin n) (Fin n) ℤ,
                    IsUnit P ∧ (∀ i j, P i j = bFin j i) ∧
                      P.mulVec ((Pi.basisFun ℤ (Fin n)) (e (Sum.inl ()))) = w ∧
                        (∀ y : Fin n → ℤ,
                          quotientBilinearFormLinearOfIndex L x ha hindex
                              (P.mulVec y) = y (e (Sum.inl ()))) ∧
                          LinearMap.range
                              (Matrix.toLin' (P * distinguishedKernelBlockMatrix e)) =
                            L.bilinearOrthogonalSubmodule x ∧
                            ∃ yx : Fin n → ℤ,
                              P.mulVec yx = x ∧ yx (e (Sum.inl ())) = μ / a := by
  rcases exists_quotientBilinearFormLinearOfIndex_unimodular_kernel_block_normal_form
      L x ha hindex with
    ⟨w, hw, m, hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP,
      hP_single, hrow, hrange⟩
  let yx : Fin n → ℤ := fun j => bFin.repr x j
  have hyx_eq : P.mulVec yx = x :=
    basis_matrix_mulVec_repr bFin P hP x
  have hyx_coord : yx (e (Sum.inl ())) = μ / a := by
    rw [← hrow yx, hyx_eq]
    rw [quotientBilinearFormLinearOfIndex_apply, bilinearFormValue_self, hx_value]
  exact ⟨w, hw, m, hmn, e, bFin, hbFin_line, hbFin_ker, P, hP_unit, hP,
    hP_single, hrow, hrange, yx, hyx_eq, hyx_coord⟩

/-- A standard-shaped quotient-kernel block complement matrix, together with
the coordinate of the original vector in the same quotient-row normal form. -/
def quotientKernelBlockComplementCoordinateData
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (a μ : ℤ) : Prop :=
  ∃ m : ℕ, ∃ _hmn : m + 1 = n,
    ∃ e : Unit ⊕ Fin m ≃ Fin n,
      ∃ P : Matrix (Fin n) (Fin n) ℤ,
        IsUnit P ∧
          LinearMap.range (Matrix.toLin' (P * distinguishedKernelBlockMatrix e)) =
            L.bilinearOrthogonalSubmodule x ∧
          (∃ hsub : n - 1 = m,
            C = (P * distinguishedKernelBlockMatrix e).submatrix id
              (finCongr hsub)) ∧
          ∃ yx : Fin n → ℤ,
            P.mulVec yx = x ∧ yx (e (Sum.inl ())) = μ / a

/-- The distinguished kernel block is injective after scalar extension to
`ℝ`. -/
lemma distinguishedKernelBlockMatrix_real_mulVec_injective
    {m : ℕ} (e : Unit ⊕ Fin m ≃ Fin n) :
    Function.Injective
      (((distinguishedKernelBlockMatrix e).map (Int.cast : ℤ → ℝ)).mulVec) := by
  classical
  intro z w hzw
  ext j
  have hcoord := congr_fun hzw (e (Sum.inr j))
  have hz :
      (((distinguishedKernelBlockMatrix e).map (Int.cast : ℤ → ℝ)).mulVec z)
          (e (Sum.inr j)) = z j := by
    simp only [Matrix.map_apply, distinguishedKernelBlockMatrix, Matrix.mulVec,
      dotProduct]
    calc
      (∑ l : Fin m,
          ((if e (Sum.inr j) = e (Sum.inr l) then (1 : ℤ) else 0 : ℤ) : ℝ) *
            z l) =
          ((if e (Sum.inr j) = e (Sum.inr j) then (1 : ℤ) else 0 : ℤ) : ℝ) *
            z j := by
            refine Finset.sum_eq_single j ?_ ?_
            · intro l _hl hlj
              have hne : e (Sum.inr j) ≠ e (Sum.inr l) := by
                intro heq
                have hjl : j = l := Sum.inr.inj (e.injective heq)
                exact hlj hjl.symm
              simp [hne]
            · intro hj
              exact False.elim (hj (Finset.mem_univ j))
      _ = z j := by simp
  have hw :
      (((distinguishedKernelBlockMatrix e).map (Int.cast : ℤ → ℝ)).mulVec w)
          (e (Sum.inr j)) = w j := by
    simp only [Matrix.map_apply, distinguishedKernelBlockMatrix, Matrix.mulVec,
      dotProduct]
    calc
      (∑ l : Fin m,
          ((if e (Sum.inr j) = e (Sum.inr l) then (1 : ℤ) else 0 : ℤ) : ℝ) *
            w l) =
          ((if e (Sum.inr j) = e (Sum.inr j) then (1 : ℤ) else 0 : ℤ) : ℝ) *
            w j := by
            refine Finset.sum_eq_single j ?_ ?_
            · intro l _hl hlj
              have hne : e (Sum.inr j) ≠ e (Sum.inr l) := by
                intro heq
                have hjl : j = l := Sum.inr.inj (e.injective heq)
                exact hlj hjl.symm
              simp [hne]
            · intro hj
              exact False.elim (hj (Finset.mem_univ j))
      _ = w j := by simp
  simpa [hz, hw] using hcoord

/-- The standard-shaped quotient-kernel block recorded in
`quotientKernelBlockComplementCoordinateData` has column range equal to the
bilinear orthogonal complement. -/
lemma quotientKernelBlockComplementCoordinateData.bilinearOrthogonalSubmodule_eq_range
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ} {a μ : ℤ}
    (hdata : quotientKernelBlockComplementCoordinateData L x C a μ) :
    L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) := by
  rcases hdata with
    ⟨m, _hmn, e, P, _hP_unit, hrange, hC, _yx, _hyx_eq, _hyx_coord⟩
  rcases hC with ⟨hsub, hC⟩
  rw [hC, ← hrange]
  exact (matrix_toLin_range_submatrix_col_equiv
    (C := P * distinguishedKernelBlockMatrix e) (finCongr hsub)).symm

/-- The quotient-kernel complement matrix recorded by
`quotientKernelBlockComplementCoordinateData` has injective real column map.

This is the exact injectivity input needed to feed that concrete complement
matrix to `complementLatticeOfMatrix`. -/
lemma quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ} {a μ : ℤ}
    (hdata : quotientKernelBlockComplementCoordinateData L x C a μ) :
    Function.Injective ((C.map (Int.cast : ℤ → ℝ)).mulVec) := by
  classical
  rcases hdata with
    ⟨m, _hmn, e, P, hP_unit, _hrange, hC, _yx, _hyx_eq, _hyx_coord⟩
  rcases hC with ⟨hsub, hC⟩
  subst C
  let D : Matrix (Fin n) (Fin m) ℤ := distinguishedKernelBlockMatrix e
  let E : Fin (n - 1) ≃ Fin m := finCongr hsub
  have hP_real_unit : IsUnit (P.map (Int.cast : ℤ → ℝ)) := by
    exact hP_unit.map (RingHom.mapMatrix (Int.castRingHom ℝ))
  have hP_real_inj : Function.Injective (P.map (Int.cast : ℤ → ℝ)).mulVec :=
    Matrix.mulVec_injective_of_isUnit hP_real_unit
  have hD_real_inj : Function.Injective ((D.map (Int.cast : ℤ → ℝ)).mulVec) := by
    simpa [D] using distinguishedKernelBlockMatrix_real_mulVec_injective e
  have hPD_real_inj :
      Function.Injective (((P * D).map (Int.cast : ℤ → ℝ)).mulVec) := by
    have hmap :
        (P * D).map (Int.cast : ℤ → ℝ) =
          (P.map (Int.cast : ℤ → ℝ)) * (D.map (Int.cast : ℤ → ℝ)) := by
      ext i j
      simp [Matrix.mul_apply, D]
    intro v w hvw
    apply hD_real_inj
    apply hP_real_inj
    rw [Matrix.mulVec_mulVec v (P.map (Int.cast : ℤ → ℝ)) (D.map (Int.cast : ℤ → ℝ)),
      Matrix.mulVec_mulVec w (P.map (Int.cast : ℤ → ℝ)) (D.map (Int.cast : ℤ → ℝ))]
    rw [← hmap]
    exact hvw
  intro v w hvw
  have hsub_v :
      ((((P * D).submatrix id E).map (Int.cast : ℤ → ℝ)).mulVec v) =
        (((P * D).map (Int.cast : ℤ → ℝ)).mulVec
          (fun j : Fin m => v (E.symm j))) := by
    ext i
    simp only [Matrix.map_apply, Matrix.submatrix, Matrix.mulVec, dotProduct, id_eq]
    simpa using
      (Equiv.sum_comp E
        (fun k : Fin m => (((P * D) i k : ℤ) : ℝ) * v (E.symm k)))
  have hsub_w :
      ((((P * D).submatrix id E).map (Int.cast : ℤ → ℝ)).mulVec w) =
        (((P * D).map (Int.cast : ℤ → ℝ)).mulVec
          (fun j : Fin m => w (E.symm j))) := by
    ext i
    simp only [Matrix.map_apply, Matrix.submatrix, Matrix.mulVec, dotProduct, id_eq]
    simpa using
      (Equiv.sum_comp E
        (fun k : Fin m => (((P * D) i k : ℤ) : ℝ) * w (E.symm k)))
  have hvw_reindexed :
      (fun j : Fin m => v (E.symm j)) = (fun j : Fin m => w (E.symm j)) := by
    apply hPD_real_inj
    rw [← hsub_v, ← hsub_w]
    simpa [D] using hvw
  ext j
  simpa using congr_fun hvw_reindexed (E j)

/-- The quotient-row kernel block can be reindexed as a standard complement
matrix while retaining the fixed coordinate of the original vector `x`.

This is the standard-shaped normal-form datum needed by the fixed-index step:
the complement matrix is explicitly the
non-distinguished quotient-row kernel block, and `x` has distinguished source
coordinate `μ / a` in the same unimodular coordinate system. -/
lemma exists_quotientBilinearFormLinearOfIndex_kernel_block_complement_matrix_with_vector_coordinate
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a μ : ℤ} (ha : a ≠ 0)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (hx_value : L.quadForm x = μ) :
    ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
      L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) ∧
        quotientKernelBlockComplementCoordinateData L x C a μ := by
  classical
  rcases exists_quotientBilinearFormLinearOfIndex_unimodular_kernel_block_normal_form_with_vector_coordinate
      L x ha hindex hx_value with
    ⟨_w, _hw, m, hmn, e, _bFin, _hbFin_line, _hbFin_ker, P, hP_unit, _hP,
      _hP_single, _hrow, hrange, yx, hyx_eq, hyx_coord⟩
  have hsub : n - 1 = m := by omega
  let C : Matrix (Fin n) (Fin (n - 1)) ℤ :=
    (P * distinguishedKernelBlockMatrix e).submatrix id (finCongr hsub)
  have horth : L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) := by
    rw [← hrange]
    exact (matrix_toLin_range_submatrix_col_equiv
      (C := P * distinguishedKernelBlockMatrix e) (finCongr hsub)).symm
  refine ⟨C, horth, m, hmn, e, P, hP_unit, hrange, ?_, yx, hyx_eq, hyx_coord⟩
  exact ⟨hsub, rfl⟩

/-- If `B(x,Λ)=aℤ`, then `a` divides the quadratic value `Q(x)=B(x,x)`. -/
lemma bilinearImageIdeal_generator_dvd_quadForm
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ}
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    a ∣ L.quadForm x := by
  rw [← L.bilinearFormValue_self x]
  exact L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex x

/-- A positive index generator dividing a positive minimum value gives a
nonzero normalized quotient `μ / a`.

This is the arithmetic input needed in the remaining primitive-complement
determinant calculation: the quotient-row normal form uses the distinguished
coordinate `μ / a`, and the determinant argument must be allowed to cancel
this coordinate. -/
lemma quotient_index_ediv_ne_zero_of_positive_quadForm
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a μ : ℤ}
    (ha : 0 < a) (hμ : 0 < μ)
    (hx_value : L.quadForm x = μ)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    μ / a ≠ 0 := by
  obtain ⟨m, hμ_factor⟩ :
      ∃ m : ℤ, μ = a * m := by
    simpa [hx_value] using L.bilinearImageIdeal_generator_dvd_quadForm x hindex
  have hm_pos : 0 < m := by
    have hprod_pos : 0 < a * m := by
      simpa [← hμ_factor] using hμ
    have hprod_pos' : 0 < m * a := by
      rwa [mul_comm] at hprod_pos
    exact pos_of_mul_pos_left hprod_pos' ha.le
  have hden : μ / a = m := by
    rw [hμ_factor]
    exact Int.mul_ediv_cancel_left m (ne_of_gt ha)
  exact hden.symm ▸ ne_of_gt hm_pos

/-- A positive generator of `B(x,Λ)` is bounded above by a positive quadratic
value `Q(x)`. -/
lemma bilinearImageIdeal_positive_generator_pos_and_le_quadForm_of_quadForm_pos
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ}
    (ha : 0 < a) (hx_pos : 0 < L.quadForm x)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    0 < a ∧ a ≤ L.quadForm x := by
  exact ⟨ha,
    Int.le_of_dvd hx_pos (L.bilinearImageIdeal_generator_dvd_quadForm x hindex)⟩

/-- A generator of `B(x,Λ)` is nonzero when it divides a nonzero minimum value
`μ = Q(x)`. -/
lemma bilinearImageIdeal_generator_ne_zero_of_quadForm_eq
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a μ : ℤ}
    (hμ : μ ≠ 0) (hx_value : L.quadForm x = μ)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    a ≠ 0 := by
  intro ha
  have hdiv : a ∣ μ := by
    rw [← hx_value]
    exact L.bilinearImageIdeal_generator_dvd_quadForm x hindex
  rw [ha] at hdiv
  exact hμ (zero_dvd_iff.mp hdiv)

/-- The same index ideal can be generated by the absolute value of any chosen
generator. -/
lemma bilinearImageIdeal_eq_span_abs_of_eq_span_singleton
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) {a : ℤ}
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ)) :
    L.bilinearImageIdeal x = Ideal.span ({|a|} : Set ℤ) := by
  rcases le_total 0 a with ha | ha
  · rwa [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha]
    rw [hindex, Ideal.span_singleton_neg]

/-- If `Q(x)>0`, then `B(x,Λ)` has a positive generator, bounded by `Q(x)`. -/
lemma exists_positive_bilinearImageIdeal_eq_span_singleton_of_quadForm_pos
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) (hx_pos : 0 < L.quadForm x) :
    ∃ a : ℤ, 0 < a ∧ a ≤ L.quadForm x ∧
      L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) := by
  rcases L.exists_bilinearImageIdeal_eq_span_singleton x with ⟨b, hb⟩
  have hb_ne : b ≠ 0 :=
    L.bilinearImageIdeal_generator_ne_zero_of_quadForm_eq x
      (ne_of_gt hx_pos) rfl hb
  have hindex_abs :
      L.bilinearImageIdeal x = Ideal.span ({|b|} : Set ℤ) :=
    L.bilinearImageIdeal_eq_span_abs_of_eq_span_singleton x hb
  have hpos : 0 < |b| := abs_pos.mpr hb_ne
  have hbound :
      0 < |b| ∧ |b| ≤ L.quadForm x :=
    L.bilinearImageIdeal_positive_generator_pos_and_le_quadForm_of_quadForm_pos
      x hpos hx_pos hindex_abs
  exact ⟨|b|, hbound.1, hbound.2, hindex_abs⟩

/-- The primitive-complement index relation clears the projection residual
into a denominator-controlled complement overmodule.

If `B(x,Λ)=aℤ`, `Q(x)=a*m`, and the columns of `C` parametrize `x⊥`, then
for every integral vector `y` the standard residual
`y - B(x,y) Q(x)⁻¹x` is a vector of the scaled complement
`m⁻¹ Cℤ^{n-1}`.  This is the elementary algebra behind the fixed-index
upper-control statement when the positive index `a` merely divides the
minimum value. -/
lemma orthogonalProjectionResidual_mem_scaledComplementOvermodule_of_bilinearImageIdeal_eq_span_singleton
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) {a m : ℤ}
    (ha : a ≠ 0) (hm : m ≠ 0)
    (hquad : L.quadForm x = a * m)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (horth : L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C)) :
    intVectorToRatLinear n y +
        (-(L.bilinearFormValue x y) : ℤ) •
          ((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x) ∈
      scaledComplementOvermodule C m := by
  obtain ⟨k, hk⟩ :=
    L.dvd_bilinearFormValue_of_bilinearImageIdeal_eq_span_singleton x hindex y
  have hz_orth : m • y - k • x ∈ L.bilinearOrthogonalSubmodule x := by
    change L.bilinearFormValue x (m • y - k • x) = 0
    calc
      L.bilinearFormValue x (m • y - k • x)
          = m * L.bilinearFormValue x y - k * L.bilinearFormValue x x := by
            change L.bilinearFormLinear x (m • y - k • x) =
              m * L.bilinearFormValue x y - k * L.bilinearFormValue x x
            rw [map_sub, map_smul, map_smul]
            simp [bilinearFormLinear_apply]
      _ = 0 := by
            rw [hk, bilinearFormValue_self, hquad]
            ring
  rw [horth] at hz_orth
  obtain ⟨z, hz⟩ := hz_orth
  refine ⟨z, ?_⟩
  ext i
  symm
  have hCz : C.mulVec z = m • y - k • x := by
    simpa [Matrix.toLin'_apply] using hz
  have ha_rat : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hm_rat : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hquad_rat : (L.quadForm x : ℚ) = (a : ℚ) * (m : ℚ) := by
    exact_mod_cast hquad
  have hk_rat : (L.bilinearFormValue x y : ℚ) = (a : ℚ) * (k : ℚ) := by
    exact_mod_cast hk
  have hCz_i_rat :
      (C.mulVec z i : ℚ) = (m : ℚ) * (y i : ℚ) - (k : ℚ) * (x i : ℚ) := by
    rw [congr_fun hCz i]
    simp [sub_eq_add_neg]
  calc
    (intVectorToRatLinear n y +
        (-(L.bilinearFormValue x y) : ℤ) •
          ((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)) i
        = (y i : ℚ) -
            (L.bilinearFormValue x y : ℚ) *
              ((L.quadForm x : ℚ)⁻¹ * (x i : ℚ)) := by
            simp [smul_eq_mul]
            ring
    _ = (m : ℚ)⁻¹ * ((m : ℚ) * (y i : ℚ) - (k : ℚ) * (x i : ℚ)) := by
            rw [hk_rat, hquad_rat]
            field_simp [ha_rat, hm_rat]
    _ = (scaledComplementMap C m z) i := by
            rw [← hCz_i_rat]
            simp [scaledComplementMap, smul_eq_mul]

/-- Once the fixed-index equation is normalized as `μ = a*m`, the denominator
is the fixed quotient `μ / a`.

This removes the per-lattice choice in the denominator of the value-based
fixed-upper coordinate submodule used in the fixed-index reconstruction
step. -/
lemma fixed_denominator_eq_ediv_of_fixed_value_eq
    {μ a m : ℤ} (ha : a ≠ 0) (hμ_factor : μ = a * m) :
    μ / a = m := by
  rw [hμ_factor]
  exact Int.mul_ediv_cancel_left m ha

/-- `N` is presented as the primitive `B`-orthogonal complement of a primitive
minimum vector `x` of value `μ`, with `B(x,Λ) = aℤ`.

The matrix `C` has as columns a `ℤ`-basis of the full orthogonal complement:
the spanning condition says exactly that a vector is `B`-orthogonal to `x`
iff it is an integral linear combination of those columns.  The complement
quadratic matrix is then `Cᵀ F C`. -/
def IsPrimitiveMinimumComplementWithIndex
    (μ : ℤ) (L : PositiveDefiniteIntegralLattice n) (N : PositiveDefiniteIntegralLattice (n - 1)) (a : ℤ) :
    Prop :=
  ∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
    IsPrimitiveVector x ∧
      x ≠ 0 ∧
      L.quadForm x = μ ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
      L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
      (∀ y : Fin n → ℤ,
        L.bilinearFormValue x y = 0 ↔
          ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) ∧
      Cᵀ * L.pairingMatrix * C = N.pairingMatrix

/-- In a primitive minimum-complement presentation, the imprimitivity index
`a` divides the minimum value `μ`.

This is the immediate algebraic consequence of `B(x,Λ)=aℤ` and
`B(x,x)=Q(x)=μ`. -/
lemma IsPrimitiveMinimumComplementWithIndex.index_dvd_minimum
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (h : IsPrimitiveMinimumComplementWithIndex μ L N a) : a ∣ μ := by
  rcases h with
    ⟨x, _C, _hx_primitive, _hx_ne, hx_value, _hx_minimum, hindex, _hspan, _hmatrix⟩
  have hμ_mem : μ ∈ L.bilinearImageIdeal x := by
    rw [← hx_value, ← L.bilinearFormValue_self x]
    exact Ideal.subset_span (Set.mem_range_self x)
  rw [hindex, Ideal.mem_span_singleton] at hμ_mem
  exact hμ_mem

/-- The primitive-complement index is nonzero whenever the minimum value is
nonzero. -/
lemma IsPrimitiveMinimumComplementWithIndex.index_ne_zero_of_minimum_ne_zero
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (hμ : μ ≠ 0) (h : IsPrimitiveMinimumComplementWithIndex μ L N a) :
    a ≠ 0 := by
  intro ha
  have hdvd : a ∣ μ := h.index_dvd_minimum
  rw [ha] at hdvd
  exact hμ (zero_dvd_iff.mp hdvd)

/-- Replacing the primitive-complement index by its negative preserves the
same presentation, since `aℤ = (-a)ℤ`. -/
lemma IsPrimitiveMinimumComplementWithIndex.neg_index
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (h : IsPrimitiveMinimumComplementWithIndex μ L N a) :
    IsPrimitiveMinimumComplementWithIndex μ L N (-a) := by
  rcases h with
    ⟨x, C, hx_primitive, hx_ne, hx_value, hx_minimum, hindex, hspan, hmatrix⟩
  refine ⟨x, C, hx_primitive, hx_ne, hx_value, hx_minimum, ?_, hspan, hmatrix⟩
  rw [hindex, Ideal.span_singleton_neg]

/-- The primitive-complement index can be normalized to its absolute value. -/
lemma IsPrimitiveMinimumComplementWithIndex.abs_index
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (h : IsPrimitiveMinimumComplementWithIndex μ L N a) :
    IsPrimitiveMinimumComplementWithIndex μ L N |a| := by
  rcases le_total 0 a with ha | ha
  · rwa [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha]
    exact h.neg_index

/-- For positive minimum, the normalized primitive-complement index is a
positive integer. -/
lemma IsPrimitiveMinimumComplementWithIndex.abs_index_pos_of_minimum_pos
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (hμ : 0 < μ) (h : IsPrimitiveMinimumComplementWithIndex μ L N a) :
    0 < |a| := by
  exact abs_pos.mpr (h.index_ne_zero_of_minimum_ne_zero hμ.ne')

/-- A primitive-complement presentation supplies a complement matrix whose
linear range is exactly the `B`-orthogonal submodule of the chosen minimum
vector.  This is the submodule form of the concrete complement data needed for
the Schulze--Pillot finite-overlattice sandwich. -/
lemma IsPrimitiveMinimumComplementWithIndex.exists_orthogonalSubmodule_eq_range
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (h : IsPrimitiveMinimumComplementWithIndex μ L N a) :
    ∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
      IsPrimitiveVector x ∧
        x ≠ 0 ∧
        L.quadForm x = μ ∧
        (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
        L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
        L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) ∧
        Cᵀ * L.pairingMatrix * C = N.pairingMatrix := by
  rcases h with
    ⟨x, C, hx_primitive, hx_ne, hx_value, hx_minimum, hindex, hspan, hmatrix⟩
  refine ⟨x, C, hx_primitive, hx_ne, hx_value, hx_minimum, hindex, ?_, hmatrix⟩
  exact bilinearOrthogonalSubmodule_eq_range_of_forall hspan

/-- A primitive-complement presentation whose complement is globally isometric
to a fixed representative can be rebased so that the complement matrix is
exactly the fixed representative's matrix.

This removes the auxiliary complement lattice from the fixed-index
step: after replacing the complement basis by the integral isometry
matrix from `N₀` to `N`, the columns span the same ambient orthogonal
submodule and their pulled-back quadratic matrix is `N₀.pairingMatrix`. -/
lemma IsPrimitiveMinimumComplementWithIndex.exists_fixed_complement_matrix_of_isGlobalIsometry
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N N₀ : PositiveDefiniteIntegralLattice (n - 1)} {a : ℤ}
    (h : IsPrimitiveMinimumComplementWithIndex μ L N a)
    (hN : N₀.IsGlobalIsometry N) :
    ∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
      IsPrimitiveVector x ∧
        x ≠ 0 ∧
        L.quadForm x = μ ∧
        (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
        L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
        (∀ y : Fin n → ℤ,
          L.bilinearFormValue x y = 0 ↔
            ∃ z : Fin (n - 1) → ℤ, y = (C.mulVec z)) ∧
        Cᵀ * L.pairingMatrix * C = N₀.pairingMatrix := by
  rcases h with
    ⟨x, C, hx_primitive, hx_ne, hx_value, hx_minimum, hindex, hspan, hmatrix⟩
  rcases hN with ⟨U, hU_unit, hU_matrix⟩
  refine ⟨x, C * U, hx_primitive, hx_ne, hx_value, hx_minimum, hindex, ?_, ?_⟩
  · intro y
    have hUdet_unit : IsUnit U.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
    have hUUinv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUdet_unit
    constructor
    · intro hy
      rcases (hspan y).1 hy with ⟨z, rfl⟩
      refine ⟨U⁻¹.mulVec z, ?_⟩
      calc
        C.mulVec z = (C * (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ)).mulVec z := by
          simp
        _ = (C * (U * U⁻¹)).mulVec z := by rw [hUUinv]
        _ = ((C * U) * U⁻¹).mulVec z := by rw [Matrix.mul_assoc]
        _ = (C * U).mulVec (U⁻¹.mulVec z) := by
          exact (Matrix.mulVec_mulVec z (C * U) U⁻¹).symm
    · rintro ⟨z, rfl⟩
      exact (hspan ((C * U).mulVec z)).2
        ⟨U.mulVec z, (Matrix.mulVec_mulVec z C U).symm⟩
  · calc
      (C * U)ᵀ * L.pairingMatrix * (C * U)
          = Uᵀ * (Cᵀ * L.pairingMatrix * C) * U := by
              rw [Matrix.transpose_mul]
              simp [Matrix.mul_assoc]
      _ = Uᵀ * N.pairingMatrix * U := by rw [hmatrix]
      _ = N₀.pairingMatrix := hU_matrix

/-- The rectangular matrix whose first column is the primitive line generator
and whose remaining columns are the chosen complement basis. -/
def primitiveLineComplementMatrix (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin n) (Unit ⊕ Fin (n - 1)) ℤ :=
  fun i j =>
    match j with
    | Sum.inl _ => x i
    | Sum.inr k => C i k

/-- The column index `Unit ⊕ Fin (n - 1)` of the primitive-line/complement
matrix, reindexed as `Fin n` when the ambient rank is positive. -/
def primitiveLineComplementColumnEquiv (hn : 0 < n) :
    Unit ⊕ Fin (n - 1) ≃ Fin n :=
  ((Equiv.sumCongr (finOneEquiv.symm) (Equiv.refl (Fin (n - 1)))).trans
    finSumFinEquiv).trans (finCongr (by omega))

/-- The primitive-line/complement matrix as a square `Fin n`-indexed matrix.

The source notation treats the columns `(x,C)` as an `n`-tuple.  Lean stores
that tuple with the more informative column index `Unit ⊕ Fin (n - 1)`, so
determinant statements use this reindexed square matrix. -/
def primitiveLineComplementSquareMatrix (hn : 0 < n)
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  (primitiveLineComplementMatrix x C).submatrix id
    (primitiveLineComplementColumnEquiv hn).symm

/-- A nonzero scalar multiple of the full coordinate lattice has full rank. -/
lemma smul_top_integral_coordinate_submodule_finrank (e : ℤ) (he : e ≠ 0) :
    Module.finrank ℤ
      (LinearMap.range
        ((e : ℤ) •
          (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)))) = n := by
  rw [LinearMap.finrank_range_of_inj]
  · simp [Module.finrank_fintype_fun_eq_card]
  · intro v w hvw
    ext i
    have hi : e * v i = e * w i := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hvw i
    exact mul_left_cancel₀ he hi

lemma denominatorClearedSubmodule_finrank_eq
    (d : ℤ) (hd : d ≠ 0) {Ω : Submodule ℤ (Fin n → ℚ)}
    (hΩ : embeddedIntegralLatticeSubmodule n ≤ Ω) :
    Module.finrank ℤ (denominatorClearedSubmodule (n := n) d Ω) = n := by
  let E : Submodule ℤ (Fin n → ℤ) :=
    LinearMap.range
      ((d : ℤ) •
        (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)))
  have hE_rank : Module.finrank ℤ E = n := by
    simpa [E] using smul_top_integral_coordinate_submodule_finrank (n := n) d hd
  have hle : E ≤ denominatorClearedSubmodule (n := n) d Ω :=
    smul_top_le_denominatorClearedSubmodule_of_embedded_le
      (n := n) d hd hΩ
  have hmono := Submodule.finrank_mono hle
  have hupper : Module.finrank ℤ
      (denominatorClearedSubmodule (n := n) d Ω) ≤ n := by
    simpa [Module.finrank_pi] using
      (denominatorClearedSubmodule (n := n) d Ω).finrank_le
  exact le_antisymm hupper (by simpa [hE_rank] using hmono)

/-- The fixed block matrix of the lower lattice `M ⊥ N₀`, indexed by the
primitive line and the fixed complement coordinates. -/
def primitiveLineComplementFormMatrix (μ : ℤ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    Matrix (Unit ⊕ Fin (n - 1)) (Unit ⊕ Fin (n - 1)) ℤ :=
  fun i j =>
    match i, j with
    | Sum.inl _, Sum.inl _ => μ
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr k, Sum.inr l => N₀.pairingMatrix k l

/-- The primitive-line/complement lower-block matrix is the block diagonal
matrix with line entry `μ` and complement block `N₀.pairingMatrix`. -/
lemma primitiveLineComplementFormMatrix_eq_fromBlocks
    (μ : ℤ) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    primitiveLineComplementFormMatrix μ N₀ =
      Matrix.fromBlocks
        (fun _ _ : Unit => μ)
        0 0 N₀.pairingMatrix := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The fixed lower block `M ⊥ N₀` is symmetric. -/
lemma primitiveLineComplementFormMatrix_isSymm
    (μ : ℤ) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    (primitiveLineComplementFormMatrix μ N₀).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  cases i <;> cases j <;>
    simp [primitiveLineComplementFormMatrix, N₀.form_symm.apply]

/-- The fixed lower block `M ⊥ N₀` is positive definite when the line value is
positive.

This packages the source's lower lattice `M ⊥ N₀` as a genuine positive
definite block, not just as a determinant identity. -/
lemma primitiveLineComplementFormMatrix_posDef
    {μ : ℤ} (hμ : 0 < μ) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    ((primitiveLineComplementFormMatrix μ N₀).map
      (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    cases i <;> cases j <;>
      simp [primitiveLineComplementFormMatrix, N₀.form_symm.apply]
  · intro v hv
    let vN : Fin (n - 1) → ℝ := fun i => v (Sum.inr i)
    have hμℝ : 0 < (μ : ℝ) := by exact_mod_cast hμ
    have hquad :
        star v ⬝ᵥ
            (((primitiveLineComplementFormMatrix μ N₀).map
                (Int.cast : ℤ → ℝ)) *ᵥ v) =
          (μ : ℝ) * (v (Sum.inl ())) ^ 2 +
            star vN ⬝ᵥ
              ((N₀.pairingMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ vN) := by
      simp [primitiveLineComplementFormMatrix, vN, dotProduct, Matrix.mulVec,
        pow_two, mul_assoc, mul_comm, mul_left_comm]
    by_cases hvN : vN = 0
    · have hv_line : v (Sum.inl ()) ≠ 0 := by
        intro hline
        apply hv
        ext i
        cases i with
        | inl u =>
            have hu : u = () := Subsingleton.elim u ()
            subst u
            simpa using hline
        | inr i =>
            exact congr_fun hvN i
      have htail :
          star vN ⬝ᵥ
              ((N₀.pairingMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ vN) = 0 := by
        simp [hvN]
      rw [hquad, htail, add_zero]
      exact mul_pos hμℝ (sq_pos_of_ne_zero hv_line)
    · have htail_pos :
          0 <
            star vN ⬝ᵥ
              ((N₀.pairingMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ vN) :=
        N₀.form_posDef.dotProduct_mulVec_pos hvN
      have hline_nonneg : 0 ≤ (μ : ℝ) * (v (Sum.inl ())) ^ 2 :=
        mul_nonneg hμℝ.le (sq_nonneg _)
      rw [hquad]
      exact add_pos_of_nonneg_of_pos hline_nonneg htail_pos

/-- The fixed lower block `M ⊥ N₀` has determinant `μ * det(N₀)`.

This is the determinant bookkeeping attached to the exact fixed-complement
matrix in the Schulze--Pillot sandwich.  It makes the lower-block determinant
depend only on the fixed minimum value and the fixed complement representative,
not on the ambient lattice presentation. -/
lemma primitiveLineComplementFormMatrix_det
    (μ : ℤ) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    (primitiveLineComplementFormMatrix μ N₀).det = μ * N₀.pairingDeterminant := by
  rw [primitiveLineComplementFormMatrix_eq_fromBlocks, Matrix.det_fromBlocks_zero₁₂]
  simp [pairingDeterminant, Matrix.det_fin_one]

/-- The fixed lower block `M ⊥ N₀`, reindexed by `Fin n`, is symmetric. -/
lemma primitiveLineComplementReindexedFormMatrix_isSymm
    (hn : 0 < n) (μ : ℤ) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    ((primitiveLineComplementFormMatrix μ N₀).submatrix
      (primitiveLineComplementColumnEquiv hn).symm
      (primitiveLineComplementColumnEquiv hn).symm).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  exact (primitiveLineComplementFormMatrix_isSymm μ N₀).apply
    ((primitiveLineComplementColumnEquiv hn).symm i)
    ((primitiveLineComplementColumnEquiv hn).symm j)

/-- The fixed lower block `M ⊥ N₀`, reindexed by `Fin n`, is positive
definite. -/
lemma primitiveLineComplementReindexedFormMatrix_posDef
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    (((primitiveLineComplementFormMatrix μ N₀).submatrix
      (primitiveLineComplementColumnEquiv hn).symm
      (primitiveLineComplementColumnEquiv hn).symm).map
        (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  let e := primitiveLineComplementColumnEquiv hn
  let B : Matrix (Unit ⊕ Fin (n - 1)) (Unit ⊕ Fin (n - 1)) ℝ :=
    (primitiveLineComplementFormMatrix μ N₀).map (Int.cast : ℤ → ℝ)
  let P : Matrix (Unit ⊕ Fin (n - 1)) (Fin n) ℝ :=
    fun i j => if i = e.symm j then 1 else 0
  have hP_inj : Function.Injective P.mulVec := by
    intro v w hvw
    ext j
    have hcoord := congr_fun hvw (e.symm j)
    simpa [P, Matrix.mulVec, dotProduct] using hcoord
  have hpos := (primitiveLineComplementFormMatrix_posDef hμ N₀).conjTranspose_mul_mul_same hP_inj
  convert hpos using 1
  ext i j
  simp [B, P, Matrix.mul_apply, Matrix.conjTranspose_apply, e]

/-- The fixed lower lattice `M ⊥ N₀`, indexed by `Fin n`.

This is the lattice object corresponding to the fixed lower block in the
Schulze--Pillot finite-overlattice step. -/
noncomputable def primitiveLineComplementReindexedLattice
    (hn : 0 < n) (μ : ℤ) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1)) : PositiveDefiniteIntegralLattice n where
  pairingMatrix :=
    (primitiveLineComplementFormMatrix μ N₀).submatrix
      (primitiveLineComplementColumnEquiv hn).symm
      (primitiveLineComplementColumnEquiv hn).symm
  form_symm := primitiveLineComplementReindexedFormMatrix_isSymm hn μ N₀
  form_posDef := primitiveLineComplementReindexedFormMatrix_posDef hn hμ N₀

/-- The pullback overlattice attached to a primitive-line/complement
presentation.

For the square presentation matrix `P`, this is the rational submodule
`P⁻¹ ℤ^n = {v ∈ ℚ^n | P v ∈ ℤ^n}`.  This is the basis-independent finite
object suggested by the discriminant-group formulation of the remaining
uniform finite-overlattice step. -/
def primitiveLineComplementPullbackOverlattice
    (hn : 0 < n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Submodule ℤ (Fin n → ℚ) where
  carrier :=
    { v : Fin n → ℚ |
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C) v ∈
        embeddedIntegralLatticeSubmodule n }
  zero_mem' := by
    simp
  add_mem' := by
    intro v w hv hw
    simpa using (add_mem hv hw)
  smul_mem' := by
    intro r v hv
    change intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C) (r • v) ∈
      embeddedIntegralLatticeSubmodule n
    rw [map_zsmul]
    exact Submodule.smul_mem (embeddedIntegralLatticeSubmodule n) r hv

@[simp]
lemma mem_primitiveLineComplementPullbackOverlattice
    (hn : 0 < n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (v : Fin n → ℚ) :
    v ∈ primitiveLineComplementPullbackOverlattice hn x C ↔
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C) v ∈
        embeddedIntegralLatticeSubmodule n := by
  rfl

/-- The fixed lower coordinate lattice embeds into the pullback overlattice:
integer vectors map to integer vectors under the integral presentation matrix. -/
lemma embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
    (hn : 0 < n) (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    embeddedIntegralLatticeSubmodule n ≤
      primitiveLineComplementPullbackOverlattice hn x C := by
  rintro v ⟨z, _hz, rfl⟩
  rw [mem_primitiveLineComplementPullbackOverlattice,
    intMatrixRatLinear_intVectorToRatLinear]
  exact ⟨(primitiveLineComplementSquareMatrix hn x C).mulVec z, trivial, rfl⟩

lemma dotProduct_conjTranspose_mul_mulVec_rat
    (P F : Matrix (Fin n) (Fin n) ℚ) (v w : Fin n → ℚ) :
    dotProduct v (((Pᵀ * F * P).mulVec w)) =
      dotProduct (P.mulVec v) (F.mulVec (P.mulVec w)) := by
  calc
    dotProduct v (((Pᵀ * F * P).mulVec w))
        = (v ᵥ* (Pᵀ * F * P)) ⬝ᵥ w := by
          rw [dotProduct_mulVec]
    _ = (((v ᵥ* Pᵀ) ᵥ* F) ᵥ* P) ⬝ᵥ w := by
          simp [Matrix.mul_assoc]
    _ = ((P *ᵥ v) ᵥ* F) ⬝ᵥ (P *ᵥ w) := by
          rw [← dotProduct_mulVec]
          rw [vecMul_transpose]
    _ = dotProduct (P.mulVec v) (F.mulVec (P.mulVec w)) := by
          exact (dotProduct_mulVec (P *ᵥ v) F (P *ᵥ w)).symm

/-- The `Fin n`-reindexed primitive-line/complement square matrix pulls the
ambient form back to the corresponding `Fin n` reindexing of the fixed lower
block.

This is the matrix identity needed when the fixed-span reconstruction uses
Lean's square coordinate-submodule basis machinery: the source block is
indexed by `Unit ⊕ Fin (n - 1)`, while coordinate-overmodule representatives
are indexed by `Fin n`. -/
lemma primitiveLineComplementSquareMatrix_transpose_mul_pairingMatrix_mul_eq
    {μ : ℤ} (hn : 0 < n) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    (primitiveLineComplementSquareMatrix hn x C)ᵀ * L.pairingMatrix *
        primitiveLineComplementSquareMatrix hn x C =
      (primitiveLineComplementFormMatrix μ N₀).submatrix
        (primitiveLineComplementColumnEquiv hn).symm
        (primitiveLineComplementColumnEquiv hn).symm := by
  ext i j
  simpa [primitiveLineComplementSquareMatrix, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum] using
    congr_fun (congr_fun hblock
      ((primitiveLineComplementColumnEquiv hn).symm i))
      ((primitiveLineComplementColumnEquiv hn).symm j)

/-- A realized block identity places the pullback overlattice inside the dual
of the fixed lower lattice `M₀`.

Mathematically, if `Pᵀ F_L P = F₀` and `P v` is integral, then for every
integral `y`,
`b₀(v,y) = b_L(Pv, Py)` is integral.  This is the first formal bridge toward
enumerating `P⁻¹ ℤ^n / ℤ^n` inside the finite discriminant group
`M₀# / M₀`. -/
lemma primitiveLineComplementPullbackOverlattice_le_dualSubmodule_reindexed_of_block_eq
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    primitiveLineComplementPullbackOverlattice hn x C ≤
      (primitiveLineComplementReindexedLattice hn μ hμ N₀).dualSubmodule
        (⊤ : Submodule ℤ (Fin n → ℤ)) := by
  classical
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := primitiveLineComplementSquareMatrix hn x C
  let Pℚ : Matrix (Fin n) (Fin n) ℚ := Pℤ.map (Int.cast : ℤ → ℚ)
  let Fℚ : Matrix (Fin n) (Fin n) ℚ := L.pairingMatrix.map (Int.cast : ℤ → ℚ)
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  have hblock_sq :
      Pℤᵀ * L.pairingMatrix * Pℤ = K.pairingMatrix := by
    simpa [Pℤ, K, primitiveLineComplementReindexedLattice] using
      primitiveLineComplementSquareMatrix_transpose_mul_pairingMatrix_mul_eq
        hn L N₀ x C hblock
  have hblock_rat :
      Pℚᵀ * Fℚ * Pℚ = K.pairingMatrix.map (Int.cast : ℤ → ℚ) := by
    have hmap :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℤ =>
        M.map (Int.cast : ℤ → ℚ)) hblock_sq
    have hmap_left :
        (Pℤᵀ * L.pairingMatrix * Pℤ).map (Int.cast : ℤ → ℚ) =
          Pℚᵀ * Fℚ * Pℚ := by
      rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast, transpose_map]
    rw [← hmap_left]
    exact hmap
  intro v hv
  rw [mem_dualSubmodule]
  intro y _hy
  rw [mem_primitiveLineComplementPullbackOverlattice] at hv
  rcases hv with ⟨z, _hz, hz⟩
  refine ⟨L.bilinearFormValue z (Pℤ.mulVec y), ?_⟩
  calc
    K.bilinearFormValueRat v (intVectorToRatLinear n y)
        = dotProduct v (((Pℚᵀ * Fℚ * Pℚ).mulVec
            (intVectorToRatLinear n y))) := by
          simp [K, bilinearFormValueRat, hblock_rat]
    _ = dotProduct (Pℚ.mulVec v)
          (Fℚ.mulVec (Pℚ.mulVec (intVectorToRatLinear n y))) := by
          exact dotProduct_conjTranspose_mul_mulVec_rat Pℚ Fℚ v
            (intVectorToRatLinear n y)
    _ = dotProduct (intVectorToRatLinear n z)
          (Fℚ.mulVec (intVectorToRatLinear n (Pℤ.mulVec y))) := by
          have hzP : Pℚ.mulVec v = intVectorToRatLinear n z := by
            simpa [Pℚ, Pℤ, intMatrixRatLinear] using hz.symm
          have hyP :
              Pℚ.mulVec (intVectorToRatLinear n y) =
                intVectorToRatLinear n (Pℤ.mulVec y) := by
            simpa [Pℚ, Pℤ, intMatrixRatLinear] using
              intMatrixRatLinear_intVectorToRatLinear Pℤ y
          rw [hzP, hyP]
    _ = (L.bilinearFormValue z (Pℤ.mulVec y) : ℚ) := by
          change L.bilinearFormValueRat (intVectorToRatLinear n z)
              (intVectorToRatLinear n (Pℤ.mulVec y)) =
            (L.bilinearFormValue z (Pℤ.mulVec y) : ℚ)
          simp

/-- For a fixed primitive-line/complement lower block, only finitely many
pullback overlattices `P⁻¹ℤ^n` can arise.

This is the formal discriminant-group count: each realized presentation gives
an intermediate rational submodule
`ℤ^n ≤ P⁻¹ℤ^n ≤ (M₀)#`, and the quotient `(M₀)# / ℤ^n` is finite. -/
lemma finite_primitiveLineComplementPullbackOverlattices_of_fixed_block
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    Set.Finite { Ω : Submodule ℤ (Fin n → ℚ) |
      ∃ L : PositiveDefiniteIntegralLattice n, ∃ x : Fin n → ℤ,
        ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
          (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
              primitiveLineComplementMatrix x C =
            primitiveLineComplementFormMatrix μ N₀ ∧
          Ω = primitiveLineComplementPullbackOverlattice hn x C } := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  have hintermediate :
      Set.Finite { Ω : Submodule ℤ (Fin n → ℚ) |
        embeddedIntegralLatticeSubmodule n ≤ Ω ∧
          Ω ≤ K.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ)) } := by
    exact finite_intermediate_submodules_of_finite_overmodule_quotient
      (R := ℤ) (M := Fin n → ℚ)
      (A := embeddedIntegralLatticeSubmodule n)
      (B := K.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ)))
      (Ω := K.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ)))
      (embeddedIntegralLatticeSubmodule_le_dualSubmodule K
        (⊤ : Submodule ℤ (Fin n → ℤ)))
      le_rfl
      (finite_quotient_image_dualSubmodule_top K)
  refine hintermediate.subset ?_
  intro Ω hΩ
  rcases hΩ with ⟨L, x, C, hblock, rfl⟩
  exact ⟨embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C,
    by
      simpa [K] using
        primitiveLineComplementPullbackOverlattice_le_dualSubmodule_reindexed_of_block_eq
          hn hμ L N₀ x C hblock⟩

/-- A realized pullback overlattice is integral for the fixed lower block form.

If `Pᵀ F_L P = F₀` and `P v`, `P w` are integral, then
`b₀(v,w) = b_L(Pv,Pw)` is integral. -/
lemma primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    rationalSubmoduleIntegralOnLattice
      (primitiveLineComplementReindexedLattice hn μ hμ N₀)
      (primitiveLineComplementPullbackOverlattice hn x C) := by
  classical
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := primitiveLineComplementSquareMatrix hn x C
  let Pℚ : Matrix (Fin n) (Fin n) ℚ := Pℤ.map (Int.cast : ℤ → ℚ)
  let Fℚ : Matrix (Fin n) (Fin n) ℚ := L.pairingMatrix.map (Int.cast : ℤ → ℚ)
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  have hblock_sq :
      Pℤᵀ * L.pairingMatrix * Pℤ = K.pairingMatrix := by
    simpa [Pℤ, K, primitiveLineComplementReindexedLattice] using
      primitiveLineComplementSquareMatrix_transpose_mul_pairingMatrix_mul_eq
        hn L N₀ x C hblock
  have hblock_rat :
      Pℚᵀ * Fℚ * Pℚ = K.pairingMatrix.map (Int.cast : ℤ → ℚ) := by
    have hmap :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℤ =>
        M.map (Int.cast : ℤ → ℚ)) hblock_sq
    have hmap_left :
        (Pℤᵀ * L.pairingMatrix * Pℤ).map (Int.cast : ℤ → ℚ) =
          Pℚᵀ * Fℚ * Pℚ := by
      rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast, transpose_map]
    rw [← hmap_left]
    exact hmap
  intro v hv w hw
  rw [mem_primitiveLineComplementPullbackOverlattice] at hv hw
  rcases hv with ⟨z, _hz, hz⟩
  rcases hw with ⟨y, _hy, hy⟩
  refine ⟨L.bilinearFormValue z y, ?_⟩
  calc
    K.bilinearFormValueRat v w =
        dotProduct v (((Pℚᵀ * Fℚ * Pℚ).mulVec w)) := by
          simp [K, bilinearFormValueRat, hblock_rat]
    _ = dotProduct (Pℚ.mulVec v) (Fℚ.mulVec (Pℚ.mulVec w)) := by
          exact dotProduct_conjTranspose_mul_mulVec_rat Pℚ Fℚ v w
    _ = dotProduct (intVectorToRatLinear n z)
          (Fℚ.mulVec (intVectorToRatLinear n y)) := by
          have hzP : Pℚ.mulVec v = intVectorToRatLinear n z := by
            simpa [Pℚ, Pℤ, intMatrixRatLinear] using hz.symm
          have hyP : Pℚ.mulVec w = intVectorToRatLinear n y := by
            simpa [Pℚ, Pℤ, intMatrixRatLinear] using hy.symm
          rw [hzP, hyP]
    _ = (L.bilinearFormValue z y : ℚ) := by
          change L.bilinearFormValueRat (intVectorToRatLinear n z)
              (intVectorToRatLinear n y) =
            (L.bilinearFormValue z y : ℚ)
          simp

/-- The rational ambient form forced by a fixed primitive-line/complement
lower block.

If the square column matrix `P` built from `(x,C)` satisfies
`Pᵀ F P = F₀`, then the ambient rational matrix is necessarily
`P⁻ᵀ F₀ P⁻¹`.  This definition isolates that matrix before imposing
integrality on a candidate overmodule. -/
noncomputable def primitiveLineComplementAmbientRatFormMatrix
    (hn : 0 < n) (μ : ℤ) (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let P : Matrix (Fin n) (Fin n) ℚ :=
    (primitiveLineComplementSquareMatrix hn x C).map (Int.cast : ℤ → ℚ)
  let F₀ : Matrix (Fin n) (Fin n) ℚ :=
    ((primitiveLineComplementFormMatrix μ N₀).submatrix
      (primitiveLineComplementColumnEquiv hn).symm
      (primitiveLineComplementColumnEquiv hn).symm).map (Int.cast : ℤ → ℚ)
  P⁻¹ᵀ * F₀ * P⁻¹

/-- Pulling the ambient form back to the fixed lower block forces the
determinant of the ambient lattice and the determinant of the coordinate
embedding to multiply to the fixed block determinant.

This is the determinant bookkeeping behind the fixed sandwich
`M ⊥ N₀ ≤ Λ`: once the block identity is known, the index/determinant
relation for the lower coordinate span follows. -/
lemma primitiveLineComplementSquareMatrix_det_sq_mul_pairingDeterminant_of_block_eq
    {μ : ℤ} (hn : 0 < n) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    (primitiveLineComplementSquareMatrix hn x C).det ^ 2 * L.pairingDeterminant =
      μ * N₀.pairingDeterminant := by
  let e := primitiveLineComplementColumnEquiv hn
  let P := primitiveLineComplementSquareMatrix hn x C
  have hblock_fin :
      Pᵀ * L.pairingMatrix * P =
        (primitiveLineComplementFormMatrix μ N₀).submatrix e.symm e.symm := by
    simpa [P, e] using
      primitiveLineComplementSquareMatrix_transpose_mul_pairingMatrix_mul_eq
        hn L N₀ x C hblock
  have hdet := congrArg Matrix.det hblock_fin
  calc
    P.det ^ 2 * L.pairingDeterminant = (Pᵀ * L.pairingMatrix * P).det := by
      simp [pairingDeterminant, Matrix.det_mul, Matrix.det_transpose, pow_two]
      ring
    _ = ((primitiveLineComplementFormMatrix μ N₀).submatrix e.symm e.symm).det :=
      hdet
    _ = (primitiveLineComplementFormMatrix μ N₀).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = μ * N₀.pairingDeterminant := primitiveLineComplementFormMatrix_det μ N₀

/-- The ambient lattice determinant itself divides the fixed lower-block
determinant whenever the primitive-line/complement columns pull the ambient
form back to that block.

This is the determinant bound on the possible ambient lattices inside the
fixed sandwich: given the block equation, `L.pairingDeterminant` ranges over
positive divisors of the fixed integer `μ * N₀.pairingDeterminant`. -/
lemma primitiveLineComplementMatrix_col_inl (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    (primitiveLineComplementMatrix x C).col (Sum.inl ()) = x := by
  ext i
  rfl

lemma primitiveLineComplementMatrix_col_inr (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (j : Fin (n - 1)) :
    (primitiveLineComplementMatrix x C).col (Sum.inr j) = C.col j := by
  ext i
  rfl

lemma primitiveLineComplementMatrix_mulVec (x : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (v : Unit ⊕ Fin (n - 1) → ℤ) :
    (primitiveLineComplementMatrix x C).mulVec v =
      v (Sum.inl ()) • x + C.mulVec (fun j => v (Sum.inr j)) := by
  ext i
  simp [primitiveLineComplementMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- The integral column span of the primitive-line/complement matrix is the
join of the line generated by `x` and the column span of `C`.

This is the purely algebraic lower-block identity underlying the fixed
Schulze--Pillot sandwich, before any orthogonality interpretation is attached
to the complement columns. -/
lemma primitiveLineComplementMatrix_range_eq_span_sup_range
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C)) =
      Submodule.span ℤ ({x} : Set (Fin n → ℤ)) ⊔
        LinearMap.range (Matrix.toLin' C) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    change (primitiveLineComplementMatrix x C).mulVec v ∈
      Submodule.span ℤ ({x} : Set (Fin n → ℤ)) ⊔
        LinearMap.range (Matrix.toLin' C)
    rw [primitiveLineComplementMatrix_mulVec]
    refine Submodule.mem_sup.2 ⟨v (Sum.inl ()) • x, ?_,
      C.mulVec (fun j => v (Sum.inr j)), ?_, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · exact ⟨fun j => v (Sum.inr j), by simp [Matrix.toLin'_apply]⟩
  · intro hy
    rw [Submodule.mem_sup] at hy
    rcases hy with ⟨line, hline, orth, horth, rfl⟩
    rw [Submodule.mem_span_singleton] at hline
    rcases hline with ⟨r, rfl⟩
    rcases horth with ⟨z, hz⟩
    refine ⟨fun j => match j with | Sum.inl _ => r | Sum.inr k => z k, ?_⟩
    change (primitiveLineComplementMatrix x C).mulVec
        (fun j => match j with | Sum.inl _ => r | Sum.inr k => z k) =
      r • x + orth
    rw [primitiveLineComplementMatrix_mulVec, ← hz]
    rfl

/-- The columns of the primitive-line/complement matrix span exactly the lower
coordinate sandwich `ℤx ⊔ x⊥` when the complement columns span `x⊥`.

This identifies the fixed lower block matrix `M ⊥ N₀` with the lower
submodule already used by the finite intermediate-overlattice API. -/
lemma primitiveLineComplementMatrix_range_eq_lowerSandwichSubmodule
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) :
    LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C)) =
      L.lowerSandwichSubmodule x := by
  classical
  have horth : L.bilinearOrthogonalSubmodule x =
      LinearMap.range (Matrix.toLin' C) :=
    bilinearOrthogonalSubmodule_eq_range_of_forall hspan
  rw [lowerSandwichSubmodule, horth,
    primitiveLineComplementMatrix_range_eq_span_sup_range]

lemma transpose_mul_rat_form_mul_apply_dot {κ : Type*} [Fintype κ]
    (P : Matrix (Fin n) κ ℚ) (F : Matrix (Fin n) (Fin n) ℚ) (i j : κ) :
    (Pᵀ * F * P) i j = dotProduct (P.col i) (F.mulVec (P.col j)) := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf

/-- The integral Gram matrix obtained by clearing the determinant denominator
of an integral rational overlattice `Ω`.

For `Ω` with `ℤ^n ≤ Ω` and integer-valued restricted form, clear the fixed
denominator `det(K)`, choose Lean's basis of the numerator submodule
`{z | det(K)⁻¹ z ∈ Ω}`, and extract the Gram matrix of the corresponding
rational basis vectors of `Ω`. -/
noncomputable def rationalOverlatticeClearedFormMatrix
    (K : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω)
    (hΩ_int : rationalSubmoduleIntegralOnLattice K Ω) :
    Matrix (Fin n) (Fin n) ℤ :=
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let F : Matrix (Fin n) (Fin n) ℚ :=
    ((d : ℚ)⁻¹ * (d : ℚ)⁻¹) •
      K.pairingMatrix.map (Int.cast : ℤ → ℚ)
  let G : Matrix (Fin n) (Fin n) ℚ :=
    (Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
      (Pℤ.map (Int.cast : ℤ → ℚ))
  integerMatrixOfRatMatrix G (by
    intro i j
    have hi : Pℤ.col i ∈ B :=
      fullRankCoordinateSubmoduleBasisMatrix_col_mem B hB_rank i
    have hj : Pℤ.col j ∈ B :=
      fullRankCoordinateSubmoduleBasisMatrix_col_mem B hB_rank j
    have hvi :
        (d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i) ∈ Ω := by
      simpa [B] using hi
    have hvj :
        (d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j) ∈ Ω := by
      simpa [B] using hj
    rcases hΩ_int
        ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i)) hvi
        ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) hvj with
      ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change (((Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
        (Pℤ.map (Int.cast : ℤ → ℚ))) i j) = (z : ℚ)
    rw [transpose_mul_rat_form_mul_apply_dot]
    rw [← hz]
    simp [F, bilinearFormValueRat, intVectorToRatLinear, Matrix.mulVec,
      dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm,
      mul_comm])

@[simp]
lemma rationalOverlatticeClearedFormMatrix_cast
    (K : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω)
    (hΩ_int : rationalSubmoduleIntegralOnLattice K Ω) :
    (rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
        (Int.cast : ℤ → ℚ) =
      let d : ℤ := K.pairingDeterminant
      let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
      let hB_rank : Module.finrank ℤ B = n :=
        denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
      let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
      let F : Matrix (Fin n) (Fin n) ℚ :=
        ((d : ℚ)⁻¹ * (d : ℚ)⁻¹) •
          K.pairingMatrix.map (Int.cast : ℤ → ℚ)
      (Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
        (Pℤ.map (Int.cast : ℤ → ℚ)) := by
  simp [rationalOverlatticeClearedFormMatrix]

/-- The determinant-cleared Gram matrix of an integral rational overlattice is
symmetric. -/
lemma rationalOverlatticeClearedFormMatrix_symm
    (K : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω)
    (hΩ_int : rationalSubmoduleIntegralOnLattice K Ω) :
    (rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).IsSymm := by
  classical
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let F : Matrix (Fin n) (Fin n) ℚ :=
    ((d : ℚ)⁻¹ * (d : ℚ)⁻¹) •
      K.pairingMatrix.map (Int.cast : ℤ → ℚ)
  have hcast :=
    rationalOverlatticeClearedFormMatrix_cast K Ω hΩ_lower hΩ_int
  have hentry := congr_fun (congr_fun hcast i) j
  have hentry_symm := congr_fun (congr_fun hcast j) i
  change
    ((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
        (Int.cast : ℤ → ℚ)) j i =
      ((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
        (Int.cast : ℤ → ℚ)) i j
  rw [hentry, hentry_symm]
  have hF_symm : F.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro a b
    simp [F, K.form_symm.apply a b]
  have htranspose :
      (Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
          (Pℤ.map (Int.cast : ℤ → ℚ)) =
        ((Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
          (Pℤ.map (Int.cast : ℤ → ℚ)))ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hF_symm.eq]
    simp [Matrix.mul_assoc]
  exact (congr_fun (congr_fun htranspose i) j).symm

/-- The determinant-cleared Gram matrix of an integral rational overlattice is
positive definite. -/
lemma rationalOverlatticeClearedFormMatrix_posDef
    (K : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω)
    (hΩ_int : rationalSubmoduleIntegralOnLattice K Ω) :
    ((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
      (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let Pℝ : Matrix (Fin n) (Fin n) ℝ := Pℤ.map (Int.cast : ℤ → ℝ)
  let s : ℝ := (d : ℝ)⁻¹ * (d : ℝ)⁻¹
  let Fℝ : Matrix (Fin n) (Fin n) ℝ :=
    s • K.pairingMatrix.map (Int.cast : ℤ → ℝ)
  have hs_pos : 0 < s := by
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast K.pairingDeterminant_pos
    exact mul_pos (inv_pos.mpr hd_pos) (inv_pos.mpr hd_pos)
  have hF_pos : Fℝ.PosDef := by
    exact K.form_posDef.smul hs_pos
  have hdetℤ : Pℤ.det ≠ 0 := by
    simpa [Pℤ] using fullRankCoordinateSubmoduleBasisMatrix_det_ne_zero B hB_rank
  have hdetℝ : Pℝ.det ≠ 0 := by
    change ((Pℤ.map (Int.cast : ℤ → ℝ)).det) ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hdetℤ
  have hPunit : IsUnit Pℝ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetℝ
  have hPinj : Function.Injective Pℝ.mulVec :=
    Matrix.mulVec_injective_of_isUnit hPunit
  have hpos := hF_pos.conjTranspose_mul_mul_same (B := Pℝ) hPinj
  have hmatrix :
      (rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
          (Int.cast : ℤ → ℝ) =
        Pℝᵀ * Fℝ * Pℝ := by
    have hcastQ :=
      rationalOverlatticeClearedFormMatrix_cast K Ω hΩ_lower hΩ_int
    ext i j
    have hq := congr_fun (congr_fun hcastQ i) j
    have hqR := congrArg (fun q : ℚ => (q : ℝ)) hq
    calc
      ((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
          (Int.cast : ℤ → ℝ)) i j =
          (((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
            (Int.cast : ℤ → ℚ)) i j : ℝ) := by
            simp
      _ = (((((fullRankCoordinateSubmoduleBasisMatrix
              (denominatorClearedSubmodule K.pairingDeterminant Ω)
              (denominatorClearedSubmodule_finrank_eq K.pairingDeterminant
                (ne_of_gt K.pairingDeterminant_pos) hΩ_lower)).map (Int.cast : ℤ → ℚ))ᵀ *
              (((K.pairingDeterminant : ℚ)⁻¹ * (K.pairingDeterminant : ℚ)⁻¹) •
                K.pairingMatrix.map (Int.cast : ℤ → ℚ)) *
            ((fullRankCoordinateSubmoduleBasisMatrix
              (denominatorClearedSubmodule K.pairingDeterminant Ω)
              (denominatorClearedSubmodule_finrank_eq K.pairingDeterminant
                (ne_of_gt K.pairingDeterminant_pos) hΩ_lower)).map (Int.cast : ℤ → ℚ))) i j) : ℝ) := by
            exact hqR
      _ = (Pℝᵀ * Fℝ * Pℝ) i j := by
            simp [Pℝ, Fℝ, s, d, Pℤ, B, Matrix.mul_apply, Finset.mul_sum,
              Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [hmatrix]
  simpa [Pℝ, Fℝ, Matrix.conjTranspose_apply] using hpos

/-- The integral lattice attached to an integral rational overlattice of a
fixed lattice `K`, after clearing the determinant denominator. -/
noncomputable def rationalOverlatticeClearedLattice
    (K : PositiveDefiniteIntegralLattice n) (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω)
    (hΩ_int : rationalSubmoduleIntegralOnLattice K Ω) :
    PositiveDefiniteIntegralLattice n where
  pairingMatrix := rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int
  form_symm := rationalOverlatticeClearedFormMatrix_symm K Ω hΩ_lower hΩ_int
  form_posDef := rationalOverlatticeClearedFormMatrix_posDef K Ω hΩ_lower hΩ_int

/-- Columns of the determinant-cleared pullback basis map integrally through
the primitive-line/complement presentation matrix. -/
lemma primitiveLineComplementPullbackClearedImageMatrix_col_exists
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (j : Fin n) :
    let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      primitiveLineComplementPullbackOverlattice hn x C
    let d : ℤ := K.pairingDeterminant
    let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
    let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
      embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
        hn x C
    let hB_rank : Module.finrank ℤ B = n :=
      denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
    let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
    ∃ z : Fin n → ℤ,
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
          ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) =
        intVectorToRatLinear n z := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let Ω : Submodule ℤ (Fin n → ℚ) :=
    primitiveLineComplementPullbackOverlattice hn x C
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
    embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  have hcol : Pℤ.col j ∈ B :=
    fullRankCoordinateSubmoduleBasisMatrix_col_mem B hB_rank j
  have hv :
      (d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j) ∈ Ω := by
    simpa [B] using hcol
  have hv_int :
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
          ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) ∈
        embeddedIntegralLatticeSubmodule n := by
    simpa [Ω, mem_primitiveLineComplementPullbackOverlattice] using hv
  rcases hv_int with ⟨z, _hz, hz⟩
  exact ⟨z, hz.symm⟩

/-- The integer matrix obtained by mapping the determinant-cleared basis of a
primitive-line/complement pullback overlattice through the presentation
matrix `P`.

Its columns are `P (det(K)^{-1} b_j)`, where the `b_j` are Lean's chosen
integer basis of the numerator submodule of `P^{-1}ℤ^n`.  By definition of
the pullback overlattice these columns are integral. -/
noncomputable def primitiveLineComplementPullbackClearedImageMatrix
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    Classical.choose
      (primitiveLineComplementPullbackClearedImageMatrix_col_exists
        hn hμ N₀ x C j) i

lemma primitiveLineComplementPullbackClearedImageMatrix_col_cast
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (j : Fin n) :
    intVectorToRatLinear n
        ((primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C).col j) =
      let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
      let Ω : Submodule ℤ (Fin n → ℚ) :=
        primitiveLineComplementPullbackOverlattice hn x C
      let d : ℤ := K.pairingDeterminant
      let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
      let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
        embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
          hn x C
      let hB_rank : Module.finrank ℤ B = n :=
        denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
      let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
        ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) := by
  have hspec :=
    Classical.choose_spec
      (primitiveLineComplementPullbackClearedImageMatrix_col_exists
        hn hμ N₀ x C j)
  have hcol :
      (primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C).col j =
        Classical.choose
          (primitiveLineComplementPullbackClearedImageMatrix_col_exists
            hn hμ N₀ x C j) := by
    ext i
    rfl
  rw [hcol]
  simpa [primitiveLineComplementPullbackClearedImageMatrix] using hspec.symm

lemma primitiveLineComplementPullbackClearedImageMatrix_mulVec_cast
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (c : Fin n → ℤ) :
    intVectorToRatLinear n
        ((primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C).mulVec c) =
      let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
      let Ω : Submodule ℤ (Fin n → ℚ) :=
        primitiveLineComplementPullbackOverlattice hn x C
      let d : ℤ := K.pairingDeterminant
      let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
      let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
        embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
          hn x C
      let hB_rank : Module.finrank ℤ B = n :=
        denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
      let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
      intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
        ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.mulVec c)) := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let Ω : Submodule ℤ (Fin n → ℚ) :=
    primitiveLineComplementPullbackOverlattice hn x C
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
    embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let U : Matrix (Fin n) (Fin n) ℤ :=
    primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C
  ext i
  calc
    (intVectorToRatLinear n (U.mulVec c)) i =
        ∑ j, (c j : ℚ) * (intVectorToRatLinear n (U.col j)) i := by
          simp [U, intVectorToRatLinear, Matrix.mulVec, dotProduct,
            Matrix.col, mul_comm]
    _ = ∑ j, (c j : ℚ) *
        (intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
          ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j))) i := by
          apply Finset.sum_congr rfl
          intro j _hj
          have hcol :=
            primitiveLineComplementPullbackClearedImageMatrix_col_cast
              (μ := μ) hn hμ N₀ x C j
          have hcol' :
              intVectorToRatLinear n (U.col j) =
                intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
                  ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) := by
            convert hcol using 1
          rw [hcol']
    _ = (intMatrixRatLinear (primitiveLineComplementSquareMatrix hn x C)
        ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.mulVec c))) i := by
          simp [intMatrixRatLinear, intVectorToRatLinear, Matrix.mulVec,
            dotProduct, Matrix.col, Finset.mul_sum, Finset.sum_mul,
            mul_assoc, mul_left_comm, mul_comm]
          rw [Finset.sum_comm]

lemma primitiveLineComplementSquareMatrix_det_ne_zero_of_block_eq
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    (primitiveLineComplementSquareMatrix hn x C).det ≠ 0 := by
  intro hdet_zero
  have hdet :=
    primitiveLineComplementSquareMatrix_det_sq_mul_pairingDeterminant_of_block_eq
      hn L N₀ x C hblock
  have hfixed_zero : μ * N₀.pairingDeterminant = 0 := by
    simpa [hdet_zero] using hdet.symm
  exact (ne_of_gt (mul_pos hμ N₀.pairingDeterminant_pos)) hfixed_zero

lemma primitiveLineComplementPullbackClearedImageMatrix_isUnit_of_block_eq
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    IsUnit (primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C) := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let Ω : Submodule ℤ (Fin n → ℚ) :=
    primitiveLineComplementPullbackOverlattice hn x C
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
    embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let P : Matrix (Fin n) (Fin n) ℤ := primitiveLineComplementSquareMatrix hn x C
  let Pℚ : Matrix (Fin n) (Fin n) ℚ := P.map (Int.cast : ℤ → ℚ)
  let U : Matrix (Fin n) (Fin n) ℤ :=
    primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C
  have hdetPℤ : P.det ≠ 0 := by
    simpa [P] using
      primitiveLineComplementSquareMatrix_det_ne_zero_of_block_eq
        hn hμ L N₀ x C hblock
  have hdetPℚ : Pℚ.det ≠ 0 := by
    have hmapdet : ((P.det : ℤ) : ℚ) = Pℚ.det := by
      simpa [Pℚ] using (RingHom.map_det (Int.castRingHom ℚ) P)
    rw [← hmapdet]
    exact_mod_cast hdetPℤ
  have hP_det_unit : IsUnit Pℚ.det := isUnit_iff_ne_zero.mpr hdetPℚ
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro y
  let yℚ : Fin n → ℚ := intVectorToRatLinear n y
  let v : Fin n → ℚ := Pℚ⁻¹.mulVec yℚ
  have hPv : Pℚ.mulVec v = yℚ := by
    calc
      Pℚ.mulVec v = (Pℚ * Pℚ⁻¹).mulVec yℚ := by
        simp [v, Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℚ).mulVec yℚ := by
        rw [Matrix.mul_nonsing_inv Pℚ hP_det_unit]
      _ = yℚ := by simp
  have hv : v ∈ Ω := by
    rw [mem_primitiveLineComplementPullbackOverlattice]
    refine ⟨y, trivial, ?_⟩
    simpa [P, Pℚ, yℚ, intMatrixRatLinear] using hPv.symm
  have hΩden : Ω ≤ invScalarIntegralLatticeSubmodule d n := by
    intro q hq
    have hdual :
        q ∈ K.dualSubmodule (⊤ : Submodule ℤ (Fin n → ℤ)) := by
      simpa [K, Ω] using
        primitiveLineComplementPullbackOverlattice_le_dualSubmodule_reindexed_of_block_eq
          hn hμ L N₀ x C hblock hq
    simpa [K, d] using dualSubmodule_top_le_invScalarIntegralLatticeSubmodule K hdual
  rcases (mem_iff_exists_denominatorClearedSubmodule d hΩden v).mp hv with
    ⟨z, hzB, hv_eq⟩
  have hzrange : z ∈ LinearMap.range (Matrix.toLin' Pℤ) := by
    rw [fullRankCoordinateSubmoduleBasisMatrix_range_eq B hB_rank]
    exact hzB
  rcases hzrange with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply intVectorToRatLinear_injective n
  have hpc : Pℤ.mulVec c = z := by
    simpa [Matrix.toLin'_apply] using hc
  have hUcast :=
    primitiveLineComplementPullbackClearedImageMatrix_mulVec_cast
      (μ := μ) hn hμ N₀ x C c
  calc
    intVectorToRatLinear n (U.mulVec c) =
        intMatrixRatLinear P
          ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.mulVec c)) := by
          convert hUcast using 1
    _ = intMatrixRatLinear P v := by
          rw [hpc, ← hv_eq]
    _ = yℚ := by
          simpa [P, Pℚ, yℚ, intMatrixRatLinear] using hPv
    _ = intVectorToRatLinear n y := rfl

lemma primitiveLineComplementPullbackClearedLattice_pairingMatrix_eq_conj
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      primitiveLineComplementPullbackOverlattice hn x C
    let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
      embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
        hn x C
    let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω :=
      primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
        hn hμ L N₀ x C hblock
    let U : Matrix (Fin n) (Fin n) ℤ :=
      primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C
    (rationalOverlatticeClearedLattice K Ω hΩ_lower hΩ_int).pairingMatrix =
      Uᵀ * L.pairingMatrix * U := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let Ω : Submodule ℤ (Fin n → ℚ) :=
    primitiveLineComplementPullbackOverlattice hn x C
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
    embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω :=
    primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
      hn hμ L N₀ x C hblock
  let U : Matrix (Fin n) (Fin n) ℤ :=
    primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C
  let d : ℤ := K.pairingDeterminant
  let B : Submodule ℤ (Fin n → ℤ) := denominatorClearedSubmodule d Ω
  let hB_rank : Module.finrank ℤ B = n :=
    denominatorClearedSubmodule_finrank_eq d (ne_of_gt K.pairingDeterminant_pos) hΩ_lower
  let Pℤ : Matrix (Fin n) (Fin n) ℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let P : Matrix (Fin n) (Fin n) ℤ := primitiveLineComplementSquareMatrix hn x C
  let Pℚ : Matrix (Fin n) (Fin n) ℚ := P.map (Int.cast : ℤ → ℚ)
  let Fℚ : Matrix (Fin n) (Fin n) ℚ := L.pairingMatrix.map (Int.cast : ℤ → ℚ)
  have hblock_sq : Pᵀ * L.pairingMatrix * P = K.pairingMatrix := by
    simpa [P, K, primitiveLineComplementReindexedLattice] using
      primitiveLineComplementSquareMatrix_transpose_mul_pairingMatrix_mul_eq
        hn L N₀ x C hblock
  have hblock_rat : Pℚᵀ * Fℚ * Pℚ = K.pairingMatrix.map (Int.cast : ℤ → ℚ) := by
    have hmap :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℤ =>
        M.map (Int.cast : ℤ → ℚ)) hblock_sq
    have hmap_left :
        (Pᵀ * L.pairingMatrix * P).map (Int.cast : ℤ → ℚ) =
          Pℚᵀ * Fℚ * Pℚ := by
      rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast, transpose_map]
    rw [← hmap_left]
    exact hmap
  ext i j
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  have hcleared :=
    rationalOverlatticeClearedFormMatrix_cast K Ω hΩ_lower hΩ_int
  have hcleared_entry := congr_fun (congr_fun hcleared i) j
  have hU_i :=
    primitiveLineComplementPullbackClearedImageMatrix_col_cast
      (μ := μ) hn hμ N₀ x C i
  have hU_j :=
    primitiveLineComplementPullbackClearedImageMatrix_col_cast
      (μ := μ) hn hμ N₀ x C j
  change
    ((rationalOverlatticeClearedFormMatrix K Ω hΩ_lower hΩ_int).map
        (Int.cast : ℤ → ℚ)) i j =
      ((Uᵀ * L.pairingMatrix * U).map (Int.cast : ℤ → ℚ)) i j
  rw [hcleared_entry]
  calc
    (((Pℤ.map (Int.cast : ℤ → ℚ))ᵀ *
          (((d : ℚ)⁻¹ * (d : ℚ)⁻¹) •
            K.pairingMatrix.map (Int.cast : ℤ → ℚ)) *
        (Pℤ.map (Int.cast : ℤ → ℚ))) i j)
        =
          K.bilinearFormValueRat
            ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i))
            ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) := by
          rw [transpose_mul_rat_form_mul_apply_dot]
          simp [K, d, Pℤ, B, bilinearFormValueRat, intVectorToRatLinear,
            Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
            mul_assoc, mul_left_comm, mul_comm]
    _ = dotProduct
          (Pℚ.mulVec ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i)))
          (Fℚ.mulVec
            (Pℚ.mulVec ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)))) := by
          calc
            K.bilinearFormValueRat
                ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i))
                ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)) =
              dotProduct ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i))
                (((Pℚᵀ * Fℚ * Pℚ).mulVec
                  ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)))) := by
                simp [K, bilinearFormValueRat, hblock_rat]
            _ = dotProduct
                (Pℚ.mulVec ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i)))
                (Fℚ.mulVec
                  (Pℚ.mulVec
                    ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j)))) := by
                exact dotProduct_conjTranspose_mul_mulVec_rat Pℚ Fℚ
                  ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col i))
                  ((d : ℚ)⁻¹ • intVectorToRatLinear n (Pℤ.col j))
    _ = dotProduct
          ((d : ℚ)⁻¹ • Pℚ.mulVec (intVectorToRatLinear n (Pℤ.col i)))
          (Fℚ.mulVec
            ((d : ℚ)⁻¹ • Pℚ.mulVec (intVectorToRatLinear n (Pℤ.col j)))) := by
          rw [Matrix.mulVec_smul Pℚ (d : ℚ)⁻¹
            (intVectorToRatLinear n (Pℤ.col i))]
          rw [Matrix.mulVec_smul Pℚ (d : ℚ)⁻¹
            (intVectorToRatLinear n (Pℤ.col j))]
    _ = dotProduct (intVectorToRatLinear n (U.col i))
          (Fℚ.mulVec (intVectorToRatLinear n (U.col j))) := by
          have hUi :
              intVectorToRatLinear n (U.col i) =
                (d : ℚ)⁻¹ • Pℚ.mulVec (intVectorToRatLinear n (Pℤ.col i)) := by
            convert hU_i using 1
            simp [U, K, Ω, d, B, hΩ_lower, hB_rank, Pℤ, P, Pℚ,
              intMatrixRatLinear]
          have hUj :
              intVectorToRatLinear n (U.col j) =
                (d : ℚ)⁻¹ • Pℚ.mulVec (intVectorToRatLinear n (Pℤ.col j)) := by
            convert hU_j using 1
            simp [U, K, Ω, d, B, hΩ_lower, hB_rank, Pℤ, P, Pℚ,
              intMatrixRatLinear]
          rw [← hUi, ← hUj]
    _ = (((U.map (Int.cast : ℤ → ℚ))ᵀ * Fℚ *
          (U.map (Int.cast : ℤ → ℚ))) i j) := by
          rw [transpose_mul_rat_form_mul_apply_dot]
          change ((fun k : Fin n => (U k i : ℚ)) ⬝ᵥ
              Fℚ.mulVec (fun k : Fin n => (U k j : ℚ))) =
            ((fun k : Fin n => (U k i : ℚ)) ⬝ᵥ
              Fℚ.mulVec (fun k : Fin n => (U k j : ℚ)))
          rfl
    _ = ((Uᵀ * L.pairingMatrix * U).map (Int.cast : ℤ → ℚ)) i j := by
          rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast, transpose_map]

lemma primitiveLineComplementPullbackClearedLattice_isGlobalIsometry_of_block_eq
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ) (L : PositiveDefiniteIntegralLattice n)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N₀) :
    let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      primitiveLineComplementPullbackOverlattice hn x C
    let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
      embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
        hn x C
    let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω :=
      primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
        hn hμ L N₀ x C hblock
    (rationalOverlatticeClearedLattice K Ω hΩ_lower hΩ_int).IsGlobalIsometry L := by
  classical
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let Ω : Submodule ℤ (Fin n → ℚ) :=
    primitiveLineComplementPullbackOverlattice hn x C
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
    embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω :=
    primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
      hn hμ L N₀ x C hblock
  let U : Matrix (Fin n) (Fin n) ℤ :=
    primitiveLineComplementPullbackClearedImageMatrix hn hμ N₀ x C
  refine ⟨U, ?_, ?_⟩
  · simpa [U] using
      primitiveLineComplementPullbackClearedImageMatrix_isUnit_of_block_eq
        hn hμ L N₀ x C hblock
  · have hform :=
      primitiveLineComplementPullbackClearedLattice_pairingMatrix_eq_conj
        hn hμ L N₀ x C hblock
    simpa [K, Ω, hΩ_lower, hΩ_int, U] using hform.symm

def primitiveLineComplementPullbackOverlatticeSet
    {μ : ℤ} (hn : 0 < n) (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    Set (Submodule ℤ (Fin n → ℚ)) :=
  { Ω : Submodule ℤ (Fin n → ℚ) |
    ∃ L : PositiveDefiniteIntegralLattice n, ∃ x : Fin n → ℤ,
      ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
        (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
            primitiveLineComplementMatrix x C =
          primitiveLineComplementFormMatrix μ N₀ ∧
        Ω = primitiveLineComplementPullbackOverlattice hn x C }

noncomputable def primitiveLineComplementPullbackOverlatticeRepresentative
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (Ω : Submodule ℤ (Fin n → ℚ))
    (hΩ : Ω ∈ primitiveLineComplementPullbackOverlatticeSet (μ := μ) hn N₀) :
    PositiveDefiniteIntegralLattice n :=
  let K : PositiveDefiniteIntegralLattice n := primitiveLineComplementReindexedLattice hn μ hμ N₀
  let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω := by
    rcases hΩ with ⟨L, x, C, hblock, rfl⟩
    exact embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
      hn x C
  let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω := by
    rcases hΩ with ⟨L, x, C, hblock, rfl⟩
    exact primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
      hn hμ L N₀ x C hblock
  rationalOverlatticeClearedLattice K Ω hΩ_lower hΩ_int

theorem finite_primitiveLineComplementPullbackOverlattice_lattice_representatives_of_fixed_block
    {μ : ℤ} (hn : 0 < n) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
    ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
      ∀ (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ)
        (C : Matrix (Fin n) (Fin (n - 1)) ℤ),
        (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
            primitiveLineComplementMatrix x C =
          primitiveLineComplementFormMatrix μ N₀ →
          ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  classical
  let S : Set (Submodule ℤ (Fin n → ℚ)) :=
    primitiveLineComplementPullbackOverlatticeSet (μ := μ) hn N₀
  have hS_finite : S.Finite := by
    simpa [S, primitiveLineComplementPullbackOverlatticeSet] using
      finite_primitiveLineComplementPullbackOverlattices_of_fixed_block
        hn hμ N₀
  let repOf : S → PositiveDefiniteIntegralLattice n := fun Ω =>
    primitiveLineComplementPullbackOverlatticeRepresentative
      hn hμ N₀ Ω.1 Ω.2
  let representatives : Set (PositiveDefiniteIntegralLattice n) := repOf '' Set.univ
  haveI : Fintype S := hS_finite.fintype
  refine ⟨representatives, ?_, ?_⟩
  · exact Set.Finite.image repOf Set.finite_univ
  · intro L x C hblock
    let Ω : Submodule ℤ (Fin n → ℚ) :=
      primitiveLineComplementPullbackOverlattice hn x C
    have hΩ_mem : Ω ∈ S := by
      exact ⟨L, x, C, hblock, rfl⟩
    refine ⟨repOf ⟨Ω, hΩ_mem⟩, ?_, ?_⟩
    · exact ⟨⟨Ω, hΩ_mem⟩, trivial, rfl⟩
    · let K : PositiveDefiniteIntegralLattice n :=
        primitiveLineComplementReindexedLattice hn μ hμ N₀
      let hΩ_lower : embeddedIntegralLatticeSubmodule n ≤ Ω :=
        embeddedIntegralLatticeSubmodule_le_primitiveLineComplementPullbackOverlattice
          hn x C
      let hΩ_int : rationalSubmoduleIntegralOnLattice K Ω :=
        primitiveLineComplementPullbackOverlattice_integralOn_reindexed_of_block_eq
          hn hμ L N₀ x C hblock
      have hrep_eq :
          repOf ⟨Ω, hΩ_mem⟩ =
            rationalOverlatticeClearedLattice K Ω hΩ_lower hΩ_int := by
        dsimp [repOf, primitiveLineComplementPullbackOverlatticeRepresentative]
      rw [hrep_eq]
      simpa [K, Ω, hΩ_lower, hΩ_int] using
        primitiveLineComplementPullbackClearedLattice_isGlobalIsometry_of_block_eq
          hn hμ L N₀ x C hblock

/-- The integral Gram matrix induced on an admissible coordinate submodule by
the forced primitive-line/complement rational form.

This is the matrix-level object from which the remaining reconstruction step
should build an `PositiveDefiniteIntegralLattice`: choose Lean's basis matrix for `B`, compute
the rational Gram matrix of the forced ambient form on that basis, and use the
admissibility witness to regard its entries as integers. -/
noncomputable def primitiveLineComplementAdmissibleSubmoduleFormMatrix
    {μ : ℤ} (hn : 0 < n) (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (B : Submodule ℤ (Fin n → ℤ)) (hB_rank : Module.finrank ℤ B = n)
    (hB_int :
      rationalMatrixIntegralOnSubmodule
        (primitiveLineComplementAmbientRatFormMatrix hn μ N₀ x C) B) :
    Matrix (Fin n) (Fin n) ℤ :=
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
  let F := primitiveLineComplementAmbientRatFormMatrix hn μ N₀ x C
  let G : Matrix (Fin n) (Fin n) ℚ :=
    (Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
      (Pℤ.map (Int.cast : ℤ → ℚ))
  integerMatrixOfRatMatrix G (by
    intro i j
    have hi : Pℤ.col i ∈ B :=
      fullRankCoordinateSubmoduleBasisMatrix_col_mem B hB_rank i
    have hj : Pℤ.col j ∈ B :=
      fullRankCoordinateSubmoduleBasisMatrix_col_mem B hB_rank j
    rcases hB_int (Pℤ.col i) hi (Pℤ.col j) hj with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change (((Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
        (Pℤ.map (Int.cast : ℤ → ℚ))) i j) = (z : ℚ)
    rw [transpose_mul_rat_form_mul_apply_dot]
    simpa [Pℤ, F, intVectorToRatLinear] using hz)

@[simp]
lemma primitiveLineComplementAdmissibleSubmoduleFormMatrix_cast
    {μ : ℤ} (hn : 0 < n) (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (x : Fin n → ℤ) (C : Matrix (Fin n) (Fin (n - 1)) ℤ)
    (B : Submodule ℤ (Fin n → ℤ)) (hB_rank : Module.finrank ℤ B = n)
    (hB_int :
      rationalMatrixIntegralOnSubmodule
        (primitiveLineComplementAmbientRatFormMatrix hn μ N₀ x C) B) :
    (primitiveLineComplementAdmissibleSubmoduleFormMatrix hn N₀ x C B hB_rank hB_int).map
        (Int.cast : ℤ → ℚ) =
      let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB_rank
      let F := primitiveLineComplementAmbientRatFormMatrix hn μ N₀ x C
      (Pℤ.map (Int.cast : ℤ → ℚ))ᵀ * F *
        (Pℤ.map (Int.cast : ℤ → ℚ)) := by
  simp [primitiveLineComplementAdmissibleSubmoduleFormMatrix]

lemma matrix_col_eq_mulVec_basisFun
    (C : Matrix (Fin n) (Fin (n - 1)) ℤ) (j : Fin (n - 1)) :
    C.col j = C.mulVec ((Pi.basisFun ℤ (Fin (n - 1))) j) := by
  rw [Pi.basisFun_apply, Matrix.mulVec_single_one]

lemma transpose_mul_form_mul_apply_dot {κ : Type*} [Fintype κ]
    (P : Matrix (Fin n) κ ℤ) (F : Matrix (Fin n) (Fin n) ℤ) (i j : κ) :
    (Pᵀ * F * P) i j = dotProduct (P.col i) (F.mulVec (P.col j)) := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf

/-- Exact fixed-complement data pulls the ambient quadratic matrix back to the
block form `M ⊥ N₀`.

This is the matrix-level bridge for the remaining Schulze--Pillot fixed-index
step: once the complement matrix has been rebased to satisfy
`Cᵀ F_L C = N₀.pairingMatrix`, the lower lattice generated by the primitive line
and the complement has fixed block matrix with diagonal blocks `μ` and
`N₀.pairingMatrix` and zero cross terms. -/
lemma primitiveLineComplementMatrix_transpose_mul_pairingMatrix_mul_eq
    {μ : ℤ} {L : PositiveDefiniteIntegralLattice n} {N₀ : PositiveDefiniteIntegralLattice (n - 1)}
    {x : Fin n → ℤ} {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hx_value : L.quadForm x = μ)
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z)
    (hmatrix : Cᵀ * L.pairingMatrix * C = N₀.pairingMatrix) :
    (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
        primitiveLineComplementMatrix x C =
      primitiveLineComplementFormMatrix μ N₀ := by
  classical
  ext i j
  cases i with
  | inl u =>
      cases j with
      | inl v =>
          have hu : u = () := Subsingleton.elim u ()
          have hv : v = () := Subsingleton.elim v ()
          subst u
          subst v
          rw [transpose_mul_form_mul_apply_dot]
          simp only [primitiveLineComplementMatrix_col_inl]
          change L.bilinearFormValue x x = μ
          rw [L.bilinearFormValue_self, hx_value]
      | inr j =>
          have hu : u = () := Subsingleton.elim u ()
          subst u
          have hcol : C.col j = C.mulVec ((Pi.basisFun ℤ (Fin (n - 1))) j) :=
            matrix_col_eq_mulVec_basisFun C j
          have horth : L.bilinearFormValue x (C.col j) = 0 := by
            rw [hspan (C.col j)]
            exact ⟨(Pi.basisFun ℤ (Fin (n - 1))) j, hcol⟩
          rw [transpose_mul_form_mul_apply_dot]
          simp only [primitiveLineComplementMatrix_col_inl,
            primitiveLineComplementMatrix_col_inr, primitiveLineComplementFormMatrix]
          change L.bilinearFormValue x (C.col j) = 0
          exact horth
  | inr i =>
      cases j with
      | inl v =>
          have hv : v = () := Subsingleton.elim v ()
          subst v
          have hcol : C.col i = C.mulVec ((Pi.basisFun ℤ (Fin (n - 1))) i) :=
            matrix_col_eq_mulVec_basisFun C i
          have horth : L.bilinearFormValue x (C.col i) = 0 := by
            rw [hspan (C.col i)]
            exact ⟨(Pi.basisFun ℤ (Fin (n - 1))) i, hcol⟩
          have horth' : L.bilinearFormValue (C.col i) x = 0 := by
            rwa [L.bilinearFormValue_comm (C.col i) x]
          rw [transpose_mul_form_mul_apply_dot]
          simp only [primitiveLineComplementMatrix_col_inl,
            primitiveLineComplementMatrix_col_inr, primitiveLineComplementFormMatrix]
          change L.bilinearFormValue (C.col i) x = 0
          exact horth'
      | inr j =>
          change (Cᵀ * L.pairingMatrix * C) i j = N₀.pairingMatrix i j
          exact congr_fun (congr_fun hmatrix i) j

/-- The fixed lower-block column span lies inside the embedded ambient
coordinate lattice.

In the exact complement matrix language, this is the formal lower inclusion
`M ⊥ N₀ ≤ Λ` in the rational-submodule sandwich. -/
lemma primitiveLineComplementMatrix_embedded_range_le_embeddedIntegralLatticeSubmodule
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) :
    embeddedSubmodule
        (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤
      embeddedIntegralLatticeSubmodule n := by
  rw [primitiveLineComplementMatrix_range_eq_lowerSandwichSubmodule hspan]
  exact embedded_lowerSandwichSubmodule_le_embeddedIntegralLatticeSubmodule L x

/-- Fixed-index primitive-line/complement data gives the sharper
denominator-controlled upper sandwich and the corresponding finite
intermediate rational-submodule count.

This is the formal `M ⊥ N ≤ Λ ≤ M# ⊥ N#` upper-control step for one exact
presentation: the index ideal `B(x,Λ)=aℤ` gives `Q(x)=a*m`, every projection
residual lands in `m⁻¹Cℤ^{n-1}`, and therefore all rational submodules between
the fixed lower block generated by `primitiveLineComplementMatrix x C` and the
embedded coordinate lattice form a finite set. -/
lemma primitiveLineComplementMatrix_fixed_index_upper_sandwich
    {μ a : ℤ} {L : PositiveDefiniteIntegralLattice n}
    {x : Fin n → ℤ} {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hμ : 0 < μ) (ha_pos : 0 < a)
    (hx_value : L.quadForm x = μ)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) :
    ∃ m : ℤ, m ≠ 0 ∧
      L.quadForm x = a * m ∧
      embeddedSubmodule
          (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤
        embeddedIntegralLatticeSubmodule n ∧
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((μ : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔
          scaledComplementOvermodule C m ∧
      Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
        embeddedSubmodule
            (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤ D ∧
          D ≤ embeddedIntegralLatticeSubmodule n } := by
  classical
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  obtain ⟨m, hquad_factor⟩ :=
    L.bilinearImageIdeal_generator_dvd_quadForm x hindex
  have hm_ne : m ≠ 0 := by
    intro hm
    have hx_zero : L.quadForm x = 0 := by
      simpa [hm] using hquad_factor
    exact hμ.ne' (hx_value ▸ hx_zero)
  have hx_quad_ne : L.quadForm x ≠ 0 := hx_value.trans_ne hμ.ne'
  have horth :
      L.bilinearOrthogonalSubmodule x = LinearMap.range (Matrix.toLin' C) :=
    bilinearOrthogonalSubmodule_eq_range_of_forall hspan
  have hresidual : ∀ y : Fin n → ℤ,
      intVectorToRatLinear n y +
          (-(L.bilinearFormValue x y) : ℤ) •
            ((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x) ∈
        scaledComplementOvermodule C m := by
    intro y
    exact
      orthogonalProjectionResidual_mem_scaledComplementOvermodule_of_bilinearImageIdeal_eq_span_singleton
        L x y C ha_ne hm_ne hquad_factor hindex horth
  have hupper_lattice :
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((L.quadForm x : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔
          scaledComplementOvermodule C m :=
    embeddedIntegralLatticeSubmodule_le_line_sup_scaledComplementOvermodule_of_residual_mem_scaledComplement
      L x C m hresidual
  have hupper :
      embeddedIntegralLatticeSubmodule n ≤
        Submodule.span ℤ
            ({((μ : ℚ)⁻¹ • intVectorToRatLinear n x)} :
              Set (Fin n → ℚ)) ⊔
          scaledComplementOvermodule C m := by
    simpa [hx_value] using hupper_lattice
  have hfinite_lower :
      Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
        embeddedSubmodule (L.lowerSandwichSubmodule x) ≤ D ∧
          D ≤ embeddedIntegralLatticeSubmodule n } :=
    finite_intermediate_submodules_embeddedIntegralLattice_of_le_line_sup_scaledComplementOvermodule
      L x C hx_quad_ne hm_ne horth hupper_lattice
  have hfinite :
      Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
        embeddedSubmodule
            (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤ D ∧
          D ≤ embeddedIntegralLatticeSubmodule n } := by
    simpa [primitiveLineComplementMatrix_range_eq_lowerSandwichSubmodule hspan]
      using hfinite_lower
  exact ⟨m, hm_ne, hquad_factor,
    primitiveLineComplementMatrix_embedded_range_le_embeddedIntegralLatticeSubmodule
      hspan,
    hupper, hfinite⟩

/-- Fixed-index primitive-line/complement data gives the upper sandwich with
the denominator normalized to the fixed quotient `μ / a`.

This removes the presentation-dependent existential denominator from
`primitiveLineComplementMatrix_fixed_index_upper_sandwich`: once
`Q_L(x)=μ` and `B(x,Λ)=aℤ` with `a>0`, the denominator in the complement
overmodule is forced to be `μ/a`.  The remaining uniform fixed-overlattice
selection can therefore use only the fixed data `(μ, a, N₀)`. -/
lemma primitiveLineComplementMatrix_fixed_index_upper_sandwich_fixed_denominator
    {μ a : ℤ} {L : PositiveDefiniteIntegralLattice n}
    {x : Fin n → ℤ} {C : Matrix (Fin n) (Fin (n - 1)) ℤ}
    (hμ : 0 < μ) (ha_pos : 0 < a)
    (hx_value : L.quadForm x = μ)
    (hindex : L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ))
    (hspan : ∀ y : Fin n → ℤ,
      L.bilinearFormValue x y = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) :
    embeddedSubmodule
        (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤
      embeddedIntegralLatticeSubmodule n ∧
    embeddedIntegralLatticeSubmodule n ≤
      Submodule.span ℤ
          ({((μ : ℚ)⁻¹ • intVectorToRatLinear n x)} :
            Set (Fin n → ℚ)) ⊔
        scaledComplementOvermodule C (μ / a) ∧
    Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
      embeddedSubmodule
          (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤ D ∧
        D ≤ embeddedIntegralLatticeSubmodule n } := by
  rcases primitiveLineComplementMatrix_fixed_index_upper_sandwich
      hμ ha_pos hx_value hindex hspan with
    ⟨m, _hm_ne, hquad_factor, hlower, hupper, hfinite⟩
  have hμ_factor : μ = a * m := hx_value.symm.trans hquad_factor
  have hden : μ / a = m :=
    fixed_denominator_eq_ediv_of_fixed_value_eq (ne_of_gt ha_pos) hμ_factor
  exact ⟨hlower, by simpa [hden] using hupper, hfinite⟩

/-- The possible positive normalized primitive-complement indices are finite:
they are positive divisors of the fixed minimum `μ`. -/
lemma finite_positive_primitive_complement_indices (μ : ℤ) (hμ : 0 < μ) :
    Set.Finite { a : ℤ | 0 < a ∧ a ∣ μ } :=
  finite_positive_int_divisors μ hμ

/-- For quotient-kernel complement data, the determinant of the full
primitive-line/complement square matrix relates the ambient determinant to the
constructed complement lattice determinant.

This is the formal block-determinant part of the primitive-complement step.
After this lemma, the remaining
determinant/index content is the quotient-row index calculation identifying
`det(x,C)^2` with `(μ / a)^2`. -/
lemma quotientKernelBlockComplementCoordinateData.primitiveLineComplementSquareMatrix_det_sq_mul_pairingDeterminant
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ} {a μ : ℤ}
    (hn : 0 < n)
    (hdata : quotientKernelBlockComplementCoordinateData L x C a μ)
    (hx_value : L.quadForm x = μ) :
    let hC_inj :=
      quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
        hdata
    (primitiveLineComplementSquareMatrix hn x C).det ^ 2 * L.pairingDeterminant =
      μ * (complementLatticeOfMatrix L C hC_inj).pairingDeterminant := by
  classical
  let hC_inj :=
    quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
      hdata
  let N : PositiveDefiniteIntegralLattice (n - 1) := complementLatticeOfMatrix L C hC_inj
  have hspan :
      ∀ y : Fin n → ℤ,
        L.bilinearFormValue x y = 0 ↔
          ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z :=
    forall_bilinearFormValue_eq_zero_iff_exists_of_bilinearOrthogonalSubmodule_eq_range
      hdata.bilinearOrthogonalSubmodule_eq_range
  have hmatrix : Cᵀ * L.pairingMatrix * C = N.pairingMatrix := by
    exact (complementLatticeOfMatrix_pairingMatrix L C hC_inj).symm
  have hblock :
      (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
          primitiveLineComplementMatrix x C =
        primitiveLineComplementFormMatrix μ N :=
    primitiveLineComplementMatrix_transpose_mul_pairingMatrix_mul_eq
      hx_value hspan hmatrix
  simpa [N, hC_inj] using
    primitiveLineComplementSquareMatrix_det_sq_mul_pairingDeterminant_of_block_eq
      hn L N x C hblock

/-- The distinguished quotient-row square block with one arbitrary line column
and the standard kernel block as the remaining columns. -/
def primitiveLineKernelBlockMatrix {m : ℕ}
    (e : Unit ⊕ Fin m ≃ Fin n) (yx : Fin n → ℤ) :
    Matrix (Fin n) (Unit ⊕ Fin m) ℤ :=
  fun i j =>
    match j with
    | Sum.inl _ => yx i
    | Sum.inr k => distinguishedKernelBlockMatrix e i k

/-- In distinguished quotient-row coordinates, the primitive-line/kernel-block
matrix has determinant equal to the distinguished coordinate of the vector.

The matrix is block lower triangular with upper-right block zero, line block
`yx (e (Sum.inl ()))`, and identity kernel block. -/
lemma primitiveLineComplementMatrix_distinguishedKernelBlock_det
    {m : ℕ} (e : Unit ⊕ Fin m ≃ Fin n) (yx : Fin n → ℤ) :
    ((primitiveLineKernelBlockMatrix e yx).submatrix e id).det =
      yx (e (Sum.inl ())) := by
  classical
  have hmatrix :
      (primitiveLineKernelBlockMatrix e yx).submatrix e id =
        Matrix.fromBlocks
          (fun _ _ : Unit => yx (e (Sum.inl ())))
          0
          (fun (i : Fin m) (_ : Unit) => yx (e (Sum.inr i)))
          (1 : Matrix (Fin m) (Fin m) ℤ) := by
    ext i j
    cases i with
    | inl u =>
        have hu : u = () := Subsingleton.elim u ()
        subst u
        cases j with
        | inl v =>
            have hv : v = () := Subsingleton.elim v ()
            subst v
            simp [primitiveLineKernelBlockMatrix]
        | inr j =>
            simp [primitiveLineKernelBlockMatrix, distinguishedKernelBlockMatrix]
    | inr i =>
        cases j with
        | inl v =>
            have hv : v = () := Subsingleton.elim v ()
            subst v
            simp [primitiveLineKernelBlockMatrix]
        | inr j =>
            by_cases hij : i = j
            · subst j
              simp [primitiveLineKernelBlockMatrix, distinguishedKernelBlockMatrix]
            · have hne : e (Sum.inr i) ≠ e (Sum.inr j) := by
                intro heq
                exact hij (Sum.inr.inj (e.injective heq))
              simp [primitiveLineKernelBlockMatrix, distinguishedKernelBlockMatrix,
                hne, hij]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂]
  simp [Matrix.det_fin_one]

/-- For quotient-kernel complement data, the full primitive-line/complement
coordinate determinant has square `(μ / a)^2`.

This is the quotient-row normal-form determinant calculation left after the
formal block determinant comparison: the chosen unimodular basis contributes
only a unit determinant, and the remaining block matrix is
`[[μ/a, 0], [*, I]]` up to row and column reindexing. -/
lemma quotientKernelBlockComplementCoordinateData.primitiveLineComplementSquareMatrix_det_sq_eq
    {L : PositiveDefiniteIntegralLattice n} {x : Fin n → ℤ}
    {C : Matrix (Fin n) (Fin (n - 1)) ℤ} {a μ : ℤ}
    (hn : 0 < n)
    (hdata : quotientKernelBlockComplementCoordinateData L x C a μ) :
    (primitiveLineComplementSquareMatrix hn x C).det ^ 2 = (μ / a) ^ 2 := by
  classical
  rcases hdata with
    ⟨m, _hmn, e, P, hP_unit, _hrange, hC, yx, hyx_eq, hyx_coord⟩
  rcases hC with ⟨hsub, hC⟩
  subst C
  let D : Matrix (Fin n) (Fin m) ℤ := distinguishedKernelBlockMatrix e
  let E : Fin (n - 1) ≃ Fin m := finCongr hsub
  let S : Matrix (Fin n) (Unit ⊕ Fin m) ℤ :=
    primitiveLineKernelBlockMatrix e yx
  let T : Matrix (Fin n) (Fin n) ℤ :=
    primitiveLineComplementSquareMatrix hn x ((P * D).submatrix id E)
  let col : Fin n ≃ Unit ⊕ Fin m :=
    (primitiveLineComplementColumnEquiv hn).symm.trans
      (Equiv.sumCongr (Equiv.refl Unit) E)
  let A : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) ℤ :=
    (P * S).submatrix e id
  have hT :
      T = A.submatrix e.symm col := by
    ext i j
    cases hcol : (primitiveLineComplementColumnEquiv hn).symm j with
    | inl u =>
        have hu : u = () := Subsingleton.elim u ()
        subst u
        have hx_i : x i = ∑ k, P i k * yx k := by
          have hcoord := congr_fun hyx_eq i
          simpa [Matrix.mulVec, dotProduct] using hcoord.symm
        simp [T, A, S, D, col, primitiveLineComplementSquareMatrix,
          primitiveLineComplementMatrix, hcol, hyx_eq, Matrix.mulVec,
          Matrix.mul_apply, dotProduct, primitiveLineKernelBlockMatrix,
          hx_i]
    | inr k =>
        simp [T, A, S, D, col, primitiveLineComplementSquareMatrix,
          primitiveLineComplementMatrix, primitiveLineKernelBlockMatrix, hcol,
          Matrix.mul_apply, dotProduct]
  have hA_mul :
      A = (P.submatrix e e) *
          (S.submatrix e id) := by
    ext i j
    simp only [A, S, Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
    simpa using
      (Equiv.sum_comp e
        (fun k : Fin n => P (e i) k *
          S k j)).symm
  have hdetP_unit : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP_unit
  have hdetA_abs :
      |A.det| = |μ / a| := by
    rw [hA_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self,
      primitiveLineComplementMatrix_distinguishedKernelBlock_det e yx,
      hyx_coord, abs_mul, Int.isUnit_iff_abs_eq.mp hdetP_unit, one_mul]
  have hdetT_abs : |T.det| = |μ / a| := by
    calc
      |T.det| = |(A.submatrix e.symm col).det| := by rw [hT]
      _ = |A.det| := Matrix.abs_det_submatrix_equiv_equiv e.symm col A
      _ = |μ / a| := hdetA_abs
  calc
    T.det ^ 2 = |T.det| ^ 2 := by rw [sq_abs]
    _ = |μ / a| ^ 2 := by rw [hdetT_abs]
    _ = (μ / a) ^ 2 := by rw [sq_abs]

/-- **Schulze-Pillot primitive-complement determinant-relation step,
quotient-kernel complement-lattice form**:
for a fixed primitive minimum vector `x` and a chosen positive generator
`B(x,Λ)=aℤ`, Lean constructs the quotient-kernel complement matrix
formally and packages its pulled-back quadratic matrix as
`complementLatticeOfMatrix`.  What remains is only the
Schulze--Pillot determinant/index formula for that formally constructed
complement lattice:
`N.pairingDeterminant * a ^ 2 = μ * d`.

The principality of `B(x,Λ)` is formalized separately as
`exists_bilinearImageIdeal_eq_span_singleton`, the quotient-kernel complement
matrix is supplied by
`exists_quotientBilinearFormLinearOfIndex_kernel_block_complement_matrix_with_vector_coordinate`,
and real column injectivity is supplied by
`quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective`.
The determinant is `pairingDeterminant = det(F) = det_B`, not the bilinear discriminant
`polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_positive_fixed_index_complementLattice_det_relation
    (hn : 2 ≤ n) (d : ℤ) (_hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∀ x : Fin n → ℤ, IsPrimitiveVector x → x ≠ 0 →
        L.quadForm x = μ →
        (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          ∀ a : ℤ, 0 < a →
            L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) →
              ∀ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
                ∀ hdata : quotientKernelBlockComplementCoordinateData L x C a μ,
                  (complementLatticeOfMatrix L C
                    (quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
                      hdata)).pairingDeterminant * a ^ 2 = μ * d := by
  intro L hdet x _hx_primitive _hx_ne hx_value _hx_minimum a ha_pos hindex C hdata
  let hC_inj :=
    quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
      hdata
  let N : PositiveDefiniteIntegralLattice (n - 1) := complementLatticeOfMatrix L C hC_inj
  let P := primitiveLineComplementSquareMatrix (by omega : 0 < n) x C
  have hblock :
      P.det ^ 2 * L.pairingDeterminant = μ * N.pairingDeterminant := by
    simpa [P, N, hC_inj] using
      hdata.primitiveLineComplementSquareMatrix_det_sq_mul_pairingDeterminant
        (by omega : 0 < n) hx_value
  have hsq : P.det ^ 2 = (μ / a) ^ 2 := by
    simpa [P] using
      hdata.primitiveLineComplementSquareMatrix_det_sq_eq (by omega : 0 < n)
  have hdet_relation : (μ / a) ^ 2 * d = μ * N.pairingDeterminant := by
    calc
      (μ / a) ^ 2 * d = P.det ^ 2 * L.pairingDeterminant := by
        rw [← hsq, hdet]
      _ = μ * N.pairingDeterminant := hblock
  have hq_ne : μ / a ≠ 0 :=
    L.quotient_index_ediv_ne_zero_of_positive_quadForm x ha_pos hμ hx_value hindex
  have hdiv : a ∣ μ := by
    rw [← hx_value]
    exact L.bilinearImageIdeal_generator_dvd_quadForm x hindex
  have hμ_factor : μ = a * (μ / a) := by
    have h := Int.ediv_mul_cancel hdiv
    rw [mul_comm] at h
    exact h.symm
  let q : ℤ := μ / a
  have hdet_relation_q : q ^ 2 * d = μ * N.pairingDeterminant := by
    simpa [q] using hdet_relation
  have hq_ne_q : q ≠ 0 := by
    simpa [q] using hq_ne
  have hμ_factor_q : μ = a * q := by
    simpa [q] using hμ_factor
  change N.pairingDeterminant * a ^ 2 = μ * d
  have hcancel : q * d = a * N.pairingDeterminant := by
    apply mul_left_cancel₀ hq_ne_q
    calc
      q * (q * d) = q ^ 2 * d := by ring
      _ = μ * N.pairingDeterminant := hdet_relation_q
      _ = (a * q) * N.pairingDeterminant := by rw [hμ_factor_q]
      _ = q * (a * N.pairingDeterminant) := by ring
  calc
    N.pairingDeterminant * a ^ 2 = a * (a * N.pairingDeterminant) := by ring
    _ = a * (q * d) := by rw [hcancel]
    _ = (a * q) * d := by ring
    _ = μ * d := by rw [hμ_factor_q]

/-- **Schulze-Pillot primitive-complement determinant-relation step,
fixed primitive minimum-vector and positive fixed index-generator form**:
for a fixed primitive minimum vector `x` and a chosen generator
`B(x,Λ)=aℤ` with `a > 0`, Lean constructs the quotient-kernel complement
matrix, packages the complement as `complementLatticeOfMatrix`, and reduces
to the determinant/index step above.

The principality of `B(x,Λ)` is formalized separately as
`exists_bilinearImageIdeal_eq_span_singleton`, and Lean normalizes arbitrary
generators to this positive-generator form below.  The determinant is
`pairingDeterminant = det(F) = det_B`, not the bilinear discriminant `polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_positive_fixed_index_det_relation
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∀ x : Fin n → ℤ, IsPrimitiveVector x → x ≠ 0 →
        L.quadForm x = μ →
        (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          ∀ a : ℤ, 0 < a →
            L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) →
              ∃ N : PositiveDefiniteIntegralLattice (n - 1),
                ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
                  N.pairingDeterminant * a ^ 2 = μ * d ∧
                    (∀ y : Fin n → ℤ,
                      L.bilinearFormValue x y = 0 ↔
                      ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) ∧
                    Cᵀ * L.pairingMatrix * C = N.pairingMatrix := by
  intro L hdet x hx_primitive hx_ne hx_value hx_minimum a ha_pos hindex
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  rcases exists_quotientBilinearFormLinearOfIndex_kernel_block_complement_matrix_with_vector_coordinate
      L x ha_ne hindex hx_value with
    ⟨C, horth, hdata⟩
  let hC_inj :
      Function.Injective ((C.map (Int.cast : ℤ → ℝ)).mulVec) :=
    quotientKernelBlockComplementCoordinateData.complementMatrix_real_mulVec_injective
      hdata
  let N : PositiveDefiniteIntegralLattice (n - 1) := complementLatticeOfMatrix L C hC_inj
  have hdet_relation : N.pairingDeterminant * a ^ 2 = μ * d := by
    simpa [N, hC_inj] using
      fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_positive_fixed_index_complementLattice_det_relation
        hn d hd μ hμ L hdet x hx_primitive hx_ne hx_value hx_minimum a ha_pos
        hindex C hdata
  have hspan :
      ∀ y : Fin n → ℤ,
        L.bilinearFormValue x y = 0 ↔
          ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z :=
    forall_bilinearFormValue_eq_zero_iff_exists_of_bilinearOrthogonalSubmodule_eq_range
      horth
  refine ⟨N, C, hdet_relation, hspan, ?_⟩
  exact (complementLatticeOfMatrix_pairingMatrix L C hC_inj).symm

/-- **Schulze-Pillot primitive-complement determinant-relation step,
fixed primitive minimum-vector form**:
for a fixed primitive minimum vector `x`, Schulze--Pillot's complement
construction supplies the full `B`-orthogonal complement, the index ideal
`B(x,Λ)=aℤ`, and the determinant relation
`N.pairingDeterminant * a ^ 2 = μ * d`.

This is the part that remains after Lean has
formalized the primitive-vector normalization for a vector attaining the
positive minimum, and after Lean has formalized principality of the ideal
`B(x,Λ)`.  The determinant is `pairingDeterminant = det(F) = det_B`, not the bilinear
discriminant `polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_det_relation
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∀ x : Fin n → ℤ, IsPrimitiveVector x → x ≠ 0 →
        L.quadForm x = μ →
        (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            ∃ a : ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
              0 < a ∧
              N.pairingDeterminant * a ^ 2 = μ * d ∧
                L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
                (∀ y : Fin n → ℤ,
                  L.bilinearFormValue x y = 0 ↔
                    ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) ∧
                Cᵀ * L.pairingMatrix * C = N.pairingMatrix := by
  intro L hdet x hx_primitive hx_ne hx_value hx_minimum
  have hx_pos : 0 < L.quadForm x := by
    rw [hx_value]
    exact hμ
  rcases L.exists_positive_bilinearImageIdeal_eq_span_singleton_of_quadForm_pos
      x hx_pos with
    ⟨a, ha_pos, _ha_le, hindex⟩
  rcases fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_positive_fixed_index_det_relation
      hn d hd μ hμ L hdet x hx_primitive hx_ne hx_value hx_minimum a ha_pos hindex with
    ⟨N, C, hdet_relation, hspan, hmatrix⟩
  exact ⟨N, a, C, ha_pos, hdet_relation, hindex, hspan, hmatrix⟩

/-- **Schulze-Pillot primitive-complement determinant-relation step,
signed-index form**:
for fixed `pairingDeterminant = d` and fixed positive minimum `μ`, there is a
mathematical relation saying that a rank `n - 1` lattice is the orthogonal
complement of a primitive minimum vector in a rank-`n` lattice, with
imprimitivity index `a` determined by `B(x, Λ) = aℤ`.  Every rank-`n` lattice
with determinant `d` and minimum `μ` has such a complement `N`, and
Schulze--Pillot's determinant relation is
`N.pairingDeterminant * a ^ 2 = μ * d`.

This signed-index form matches the source convention that the generator of
the ideal `B(x,Λ)` is determined only up to sign.  The positive-index form
below is proved from this by replacing `a` with `|a|`.

This is the first and sharper of the two Schulze--Pillot ingredients used
together with the lower-rank finite determinant union.  The determinant is
`pairingDeterminant = det(F) = det_B`, not the bilinear discriminant
`polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_det_relation_signed_index
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
        ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            ∃ a : ℤ, N.pairingDeterminant * a ^ 2 = μ * d ∧
              IsPrimitiveMinimumComplementWithIndex μ L N a := by
  intro L hdet hminimum
  rcases hminimum with ⟨x, hx_ne, hx_value, hx_minimum⟩
  have hx_primitive : IsPrimitiveVector x :=
    isPrimitiveVector_of_quadForm_minimum L hμ hx_ne hx_value hx_minimum
  rcases fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_for_primitive_minimum_vector_det_relation
      hn d hd μ hμ L hdet x hx_primitive hx_ne hx_value hx_minimum with
    ⟨N, a, C, _ha_pos, hdet_relation, hindex, hspan, hmatrix⟩
  exact ⟨N, a, hdet_relation, x, C, hx_primitive, hx_ne, hx_value,
    hx_minimum, hindex, hspan, hmatrix⟩

/-- **Schulze-Pillot primitive-complement determinant-relation step,
positive-index form**:
the signed Schulze--Pillot determinant-relation source can always be normalized
to a positive primitive-complement index by replacing the generator `a` of
`B(x,Λ)=aℤ` with `|a|`.

This is the form used downstream for finite unions over positive indices. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_det_relation
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
        ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            ∃ a : ℤ, 0 < a ∧ N.pairingDeterminant * a ^ 2 = μ * d ∧
              IsPrimitiveMinimumComplementWithIndex μ L N a := by
  intro L hdet hminimum
  obtain ⟨N, a, hdet_relation, hN⟩ :=
    fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_det_relation_signed_index
      hn d hd μ hμ L hdet hminimum
  refine ⟨N, |a|, hN.abs_index_pos_of_minimum_pos hμ, ?_, hN.abs_index⟩
  rw [sq_abs]
  exact hdet_relation

/-- A chosen primitive-minimum-complement relation supplied by the
Schulze--Pillot primitive-complement step. -/
noncomputable def fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement
    (_hn : 2 ≤ n) (d : ℤ) (_hd : 0 < d) (μ : ℤ) (_hμ : 0 < μ) :
    PositiveDefiniteIntegralLattice n → PositiveDefiniteIntegralLattice (n - 1) → Prop :=
  fun L N => ∃ a : ℤ, 0 < a ∧ N.pairingDeterminant * a ^ 2 = μ * d ∧
    IsPrimitiveMinimumComplementWithIndex μ L N a

/-- The concrete primitive-minimum-complement relation still has the existence
property needed by the downstream fixed-minimum proof. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement_exists
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
      ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
            ∃ N : PositiveDefiniteIntegralLattice (n - 1),
              (∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧ N.pairingDeterminant = e) ∧
                fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement
                  hn d hd μ hμ L N := by
  intro L hdet hminimum
  obtain ⟨N, a, ha_pos, hdet_relation, hN⟩ :=
    fixed_rank_atLeastTwo_positive_pairingDeterminant_primitive_complement_det_relation
      hn d hd μ hμ L hdet hminimum
  refine ⟨N, ?_, a, ha_pos, hdet_relation, hN⟩
  refine ⟨N.pairingDeterminant, N.pairingDeterminant_pos, ?_, rfl⟩
  exact ⟨a ^ 2, hdet_relation.symm⟩

/-- A Lean coordinate representative for a full-rank representation into an
ambient integral lattice.

The second component records the full-rank coordinate image of the represented
lattice inside the ambient coordinate lattice. -/
abbrev FullRankCoordinateRepresentation (n : ℕ) :=
  Σ _L : PositiveDefiniteIntegralLattice n,
    { A : Submodule ℤ (Fin n → ℤ) // Module.finrank ℤ A = n }

/-- Coordinate-form equivalence of representation classes.

This is the Lean analogue of Schulze--Pillot's equivalence of representations:
an ambient isometry carries the representative coordinate image to the target
coordinate image.  The matrix orientation matches `IsGlobalIsometry`, so
forgetting the coordinate-image equality immediately gives an ambient global
isometry. -/
def FullRankCoordinateRepresentation.IsClassEquivalent
    (R : FullRankCoordinateRepresentation n)
    (L : PositiveDefiniteIntegralLattice n) (A : Submodule ℤ (Fin n → ℤ)) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ,
    IsUnit U ∧ Uᵀ * L.pairingMatrix * U = R.1.pairingMatrix ∧
      Submodule.map (Matrix.toLin' U) R.2.1 = A

/-- Representation-class equivalence is reflexive on a full-rank coordinate
representation.

This formalizes the identity representative in Schulze--Pillot's phrase
"classes of representations", so the remaining source theorem only has to
supply a finite class family, not elementary class-relation bookkeeping. -/
lemma FullRankCoordinateRepresentation.IsClassEquivalent.refl
    (R : FullRankCoordinateRepresentation n) :
    R.IsClassEquivalent R.1 R.2.1 := by
  refine ⟨1, isUnit_one, ?_, ?_⟩
  · simp
  · simp


/-- Representation-class equivalence is symmetric between two full-rank
coordinate representations.

The inverse unimodular matrix carries the target coordinate image back to the
representative image and conjugates the ambient form matrix in the opposite
direction. -/
lemma FullRankCoordinateRepresentation.IsClassEquivalent.symm
    {R S : FullRankCoordinateRepresentation n}
    (h : R.IsClassEquivalent S.1 S.2.1) :
    S.IsClassEquivalent R.1 R.2.1 := by
  rcases h with ⟨U, hU_unit, hU_form, hU_image⟩
  have hU_det_unit : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
  have hU_inv_unit : IsUnit U⁻¹ := by
    rwa [Matrix.isUnit_nonsing_inv_iff]
  refine ⟨U⁻¹, hU_inv_unit, ?_, ?_⟩
  · have hleft : (U⁻¹)ᵀ * Uᵀ = (1 : Matrix (Fin n) (Fin n) ℤ) := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv U hU_det_unit,
        Matrix.transpose_one]
    have hright : U * U⁻¹ = (1 : Matrix (Fin n) (Fin n) ℤ) :=
      Matrix.mul_nonsing_inv U hU_det_unit
    calc
      (U⁻¹)ᵀ * R.1.pairingMatrix * U⁻¹
          = (U⁻¹)ᵀ * (Uᵀ * S.1.pairingMatrix * U) * U⁻¹ := by
              rw [hU_form]
      _ = ((U⁻¹)ᵀ * Uᵀ) * S.1.pairingMatrix * (U * U⁻¹) := by
              simp [Matrix.mul_assoc]
      _ = S.1.pairingMatrix := by
              rw [hleft, hright]
              simp
  · let e := intMatrixLinearEquivOfIsUnit U hU_unit
    have hU_image' : Submodule.map e.toLinearMap R.2.1 = S.2.1 := by
      simpa [e] using hU_image
    change Submodule.map e.symm.toLinearMap S.2.1 = R.2.1
    rw [← hU_image']
    rw [← Submodule.map_comp]
    change Submodule.map (e.symm.toLinearMap.comp e.toLinearMap) R.2.1 = R.2.1
    simp [Submodule.map_id]

/-- Representation-class equivalence is transitive between full-rank
coordinate representations.

Composing the two unimodular coordinate changes composes both the form
congruences and the coordinate-image transports. -/
lemma FullRankCoordinateRepresentation.IsClassEquivalent.trans
    {R S T : FullRankCoordinateRepresentation n}
    (hRS : R.IsClassEquivalent S.1 S.2.1)
    (hST : S.IsClassEquivalent T.1 T.2.1) :
    R.IsClassEquivalent T.1 T.2.1 := by
  rcases hRS with ⟨U, hU_unit, hU_form, hU_image⟩
  rcases hST with ⟨V, hV_unit, hV_form, hV_image⟩
  refine ⟨V * U, hV_unit.mul hU_unit, ?_, ?_⟩
  · calc
      (V * U)ᵀ * T.1.pairingMatrix * (V * U)
          = Uᵀ * (Vᵀ * T.1.pairingMatrix * V) * U := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Uᵀ * S.1.pairingMatrix * U := by
              rw [hV_form]
      _ = R.1.pairingMatrix := hU_form
  · rw [Matrix.toLin'_mul]
    rw [Submodule.map_comp, hU_image, hV_image]

/-- The target coordinate image in a representation-class equivalence is
full rank.

Thus the class-equivalence witness itself carries the full-rank coordinate
condition needed for Schulze--Pillot's primitive-closure index bookkeeping;
it is not an extra source-side datum once a representative class has been
chosen. -/
lemma FullRankCoordinateRepresentation.IsClassEquivalent.finrank_eq
    {R : FullRankCoordinateRepresentation n} {L : PositiveDefiniteIntegralLattice n}
    {A : Submodule ℤ (Fin n → ℤ)} (h : R.IsClassEquivalent L A) :
    Module.finrank ℤ A = n := by
  rcases h with ⟨U, hU_unit, _hU_form, hU_image⟩
  let e := intMatrixLinearEquivOfIsUnit U hU_unit
  have hU_image' : Submodule.map e.toLinearMap R.2.1 = A := by
    simpa [e] using hU_image
  rw [← hU_image']
  have hfin :=
    (Submodule.equivMapOfInjective e.toLinearMap e.injective R.2.1).finrank_eq
  rw [← hfin]
  exact R.2.2


/-- **Schulze-Pillot fixed lower-block sandwich finite-overlattice theorem**:
the cover-only fixed-block statement follows from the finite set of
pullback overlattices `P⁻¹ℤ^n`.  The hypothesis also contains the
denominator-controlled upper inclusion, but the finite representative set
only uses the block identity. -/
theorem fixed_primitiveLineComplement_fixed_block_sandwich_representatives
    (_hn : 2 ≤ n) (μ : ℤ) (_hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (a : ℤ) (_ha_pos : 0 < a) (_hden : μ / a ≠ 0) :
      ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
        ∀ L : PositiveDefiniteIntegralLattice n,
          (∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
            (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
                primitiveLineComplementMatrix x C =
              primitiveLineComplementFormMatrix μ N₀ ∧
              embeddedIntegralLatticeSubmodule n ≤
                Submodule.span ℤ
                    ({((μ : ℚ)⁻¹ • intVectorToRatLinear n x)} :
                      Set (Fin n → ℚ)) ⊔
                  scaledComplementOvermodule C (μ / a)) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  classical
  have hn_pos : 0 < n := by omega
  rcases finite_primitiveLineComplementPullbackOverlattice_lattice_representatives_of_fixed_block
      (μ := μ) hn_pos _hμ N₀ with
    ⟨representatives, hrepresentatives_finite, hcover⟩
  refine ⟨representatives, hrepresentatives_finite, ?_⟩
  intro L hpresentation
  rcases hpresentation with ⟨x, C, hblock, _hupper⟩
  exact hcover L x C hblock

/-- **Schulze-Pillot fixed lower-block finite-overlattice theorem**: the
exact primitive-line/complement presentation reduces formally to the
normalized fixed-block step.

The exact data `Q(x)=μ`, `B(x,Λ)=aℤ`, `x⊥=range(C)`, and
`Cᵀ F_Λ C = N₀.pairingMatrix` is used only to prove the fixed block matrix and
the denominator-controlled upper inclusion.  The normalized theorem above
inherits the representative determinant and coordinate-realization facts; this
older interface is its cover-only projection. -/
theorem fixed_primitiveLineComplement_fixed_index_overlattice_representatives
    (_hn : 2 ≤ n) (μ : ℤ) (_hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (a : ℤ) (_ha_pos : 0 < a) :
      ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
        ∀ L : PositiveDefiniteIntegralLattice n,
          (∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
            x ≠ 0 ∧
              L.quadForm x = μ ∧
              L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
              (∀ y : Fin n → ℤ,
                L.bilinearFormValue x y = 0 ↔
                  ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) ∧
              Cᵀ * L.pairingMatrix * C = N₀.pairingMatrix) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  by_cases hden : μ / a ≠ 0
  ·
    rcases fixed_primitiveLineComplement_fixed_block_sandwich_representatives
        _hn μ _hμ N₀ a _ha_pos hden with
      ⟨representatives, hrepresentatives_finite, hcover⟩
    refine ⟨representatives, hrepresentatives_finite, ?_⟩
    intro L hpresentation
    rcases hpresentation with
      ⟨x, C, _hx_ne, hx_value, hindex, hspan, hmatrix⟩
    have hblock :
        (primitiveLineComplementMatrix x C)ᵀ * L.pairingMatrix *
            primitiveLineComplementMatrix x C =
          primitiveLineComplementFormMatrix μ N₀ :=
      primitiveLineComplementMatrix_transpose_mul_pairingMatrix_mul_eq
        hx_value hspan hmatrix
    have hsandwich :
        embeddedSubmodule
            (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤
          embeddedIntegralLatticeSubmodule n ∧
        embeddedIntegralLatticeSubmodule n ≤
          Submodule.span ℤ
              ({((μ : ℚ)⁻¹ • intVectorToRatLinear n x)} :
                Set (Fin n → ℚ)) ⊔
            scaledComplementOvermodule C (μ / a) ∧
        Set.Finite { D : Submodule ℤ (Fin n → ℚ) |
          embeddedSubmodule
              (LinearMap.range (Matrix.toLin' (primitiveLineComplementMatrix x C))) ≤ D ∧
            D ≤ embeddedIntegralLatticeSubmodule n } :=
      primitiveLineComplementMatrix_fixed_index_upper_sandwich_fixed_denominator
        _hμ _ha_pos hx_value hindex hspan
    exact hcover L ⟨x, C, hblock, hsandwich.2.1⟩
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro L hpresentation
    rcases hpresentation with
      ⟨x, _C, _hx_ne, hx_value, hindex, _hspan, _hmatrix⟩
    have hden_ne : μ / a ≠ 0 :=
      L.quotient_index_ediv_ne_zero_of_positive_quadForm x _ha_pos _hμ hx_value
        hindex
    exact False.elim (hden hden_ne)

/-- **Schulze-Pillot fixed-index exact-complement reconstruction**: after
fixing one complement representative `N₀` and one positive compatible
primitive-complement index `a`, Schulze--Pillot's fixed-determinant
class-number proof gives only finitely many rank-`n` lattices whose primitive
minimum complement can be written with pulled-back matrix exactly
`N₀.pairingMatrix`.

This is the cover-only projection of the normalized exact-complement theorem
above.  The determinant is `pairingDeterminant = det(F) = det_B`, not the bilinear
discriminant `polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_exact_complement_matrix_representatives
    (_hn : 2 ≤ n) (d : ℤ) (_hd : 0 < d) (μ : ℤ) (_hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (a : ℤ) (_ha_pos : 0 < a) (_ha_det : N₀.pairingDeterminant * a ^ 2 = μ * d) :
      ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
        ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
          (∃ x : Fin n → ℤ, ∃ C : Matrix (Fin n) (Fin (n - 1)) ℤ,
            IsPrimitiveVector x ∧
              x ≠ 0 ∧
              L.quadForm x = μ ∧
              (∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
              L.bilinearImageIdeal x = Ideal.span ({a} : Set ℤ) ∧
              (∀ y : Fin n → ℤ,
                L.bilinearFormValue x y = 0 ↔
                  ∃ z : Fin (n - 1) → ℤ, y = C.mulVec z) ∧
              Cᵀ * L.pairingMatrix * C = N₀.pairingMatrix) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  rcases fixed_primitiveLineComplement_fixed_index_overlattice_representatives
      _hn μ _hμ N₀ a _ha_pos with
    ⟨representatives, hrepresentatives_finite, hcover⟩
  refine ⟨representatives, hrepresentatives_finite, ?_⟩
  intro L _hdet hpresentation
  rcases hpresentation with
    ⟨x, C, _hx_primitive, hx_ne, hx_value, _hx_minimum, hindex, hspan,
      hmatrix⟩
  exact hcover L ⟨x, C, hx_ne, hx_value, hindex, hspan, hmatrix⟩

/-- **Schulze-Pillot fixed-index complement-class reconstruction theorem**:
the fixed-complement-class statement reduces formally to the normalized exact
fixed-complement matrix theorem above. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_complement_class_representatives
    (_hn : 2 ≤ n) (d : ℤ) (_hd : 0 < d) (μ : ℤ) (_hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (a : ℤ) (_ha_pos : 0 < a) (_ha_det : N₀.pairingDeterminant * a ^ 2 = μ * d) :
      ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
        ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
          (∃ N : PositiveDefiniteIntegralLattice (n - 1),
            IsPrimitiveMinimumComplementWithIndex μ L N a ∧
              N₀.IsGlobalIsometry N) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  rcases fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_exact_complement_matrix_representatives
      _hn d _hd μ _hμ N₀ a _ha_pos _ha_det with
    ⟨representatives, hrepresentatives_finite, hcover⟩
  refine ⟨representatives, hrepresentatives_finite, ?_⟩
  intro L hdet hcomplement
  rcases hcomplement with ⟨N, hprimitive, hN_iso⟩
  exact hcover L hdet
    (hprimitive.exists_fixed_complement_matrix_of_isGlobalIsometry hN_iso)

/-- **Schulze-Pillot single-complement fixed-index step**:
after fixing one complement representative `N₀` and one positive normalized
primitive-complement index `a` satisfying
`N₀.pairingDeterminant * a^2 = μ * d`, only finitely many rank-`n` overlattices can
arise.

This is the fixed-index core of the finite-overlattice reconstruction step.
The theorem below takes the finite union over the possible positive indices
`a ∣ μ`; the divisibility is needed for that finite outer union, not for the
fixed-index step itself.  The theorem below supplies determinant
compatibility from the primitive-complement relation plus global-isometry
invariance of `pairingDeterminant`.  This is proved from the coordinate
reconstruction theorem above and the finite coordinate-submodule candidate
construction. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_overlattices
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ)
    (N₀ : PositiveDefiniteIntegralLattice (n - 1))
    (a : ℤ) (ha_pos : 0 < a) (ha_det : N₀.pairingDeterminant * a ^ 2 = μ * d) :
      ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
        ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
          (∃ N : PositiveDefiniteIntegralLattice (n - 1),
            IsPrimitiveMinimumComplementWithIndex μ L N a ∧
              N₀.IsGlobalIsometry N) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  rcases fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_complement_class_representatives
      hn d hd μ hμ N₀ a ha_pos ha_det with
    ⟨representatives, hrepresentatives_finite, hcover⟩
  exact ⟨representatives, hrepresentatives_finite, hcover⟩

/-- **Schulze-Pillot single-complement finite-overlattice step**:
after fixing one rank `n - 1` complement representative `N₀`, only finitely
many rank `n` overlattices can arise from primitive minimum complements
globally isometric to `N₀`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_overlattices
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ)
    (complementRepresentatives : Set (PositiveDefiniteIntegralLattice (n - 1))) :
      (∀ N₀ : PositiveDefiniteIntegralLattice (n - 1), N₀ ∈ complementRepresentatives →
        ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
          ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
            (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
              ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
                (∃ N : PositiveDefiniteIntegralLattice (n - 1),
                  fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement
                    hn d hd μ hμ L N ∧ N₀.IsGlobalIsometry N) →
                    ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L) := by
  classical
  let indices : Set ℤ := { a : ℤ | 0 < a ∧ a ∣ μ }
  have hindices : indices.Finite :=
    finite_positive_primitive_complement_indices μ hμ
  intro N₀ hN₀
  let representativesOfIndex (a : ℤ) : Set (PositiveDefiniteIntegralLattice n) :=
    if ha : a ∈ indices ∧ N₀.pairingDeterminant * a ^ 2 = μ * d then
      Classical.choose
        (fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_overlattices
          hn d hd μ hμ N₀ a ha.1.1 ha.2)
    else ∅
  refine ⟨⋃ a ∈ indices, representativesOfIndex a, ?_, ?_⟩
  · refine hindices.biUnion ?_
    intro a ha
    dsimp [representativesOfIndex]
    by_cases hdet_index : N₀.pairingDeterminant * a ^ 2 = μ * d
    · rw [dif_pos ⟨ha, hdet_index⟩]
      exact (Classical.choose_spec
        (fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_overlattices
          hn d hd μ hμ N₀ a ha.1 hdet_index)).1
    · rw [dif_neg]
      · exact Set.finite_empty
      · exact fun hsource => hdet_index hsource.2
  · intro L hdet hminimum hcomplement
    obtain ⟨N, hprimitive, hN_iso⟩ := hcomplement
    obtain ⟨a, ha_pos, hdet_relation, ha⟩ := hprimitive
    have hindex : a ∈ indices := ⟨ha_pos, ha.index_dvd_minimum⟩
    have hdet_index : N₀.pairingDeterminant * a ^ 2 = μ * d := by
      rwa [pairingDeterminant_eq_of_isGlobalIsometry hN_iso]
    obtain ⟨L₀, hL₀_mem, hL₀_iso⟩ :=
      (Classical.choose_spec
        (fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_fixed_index_overlattices
          hn d hd μ hμ N₀ a hindex.1 hdet_index)).2
        L hdet ⟨N, ha, hN_iso⟩
    refine ⟨L₀, ?_, hL₀_iso⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    refine Set.mem_iUnion.2 ⟨hindex, ?_⟩
    dsimp [representativesOfIndex]
    rw [dif_pos ⟨hindex, hdet_index⟩]
    exact hL₀_mem

/-- **Schulze-Pillot fixed-minimum finite-complement-representative step**:
after choosing a primitive minimum vector and reducing the orthogonal
complement to a finite list of representatives, only finitely many rank-`n`
lattices can occur.

This is the finite-overlattice reconstruction step from Schulze--Pillot's
proof.  The complement representatives are rank `n - 1` lattices, not just
classes, and their determinants are Schulze--Pillot determinants
`pairingDeterminant = det(F)` dividing `μ * d`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_representatives_finite_of_fixed_minimum_complement_representatives
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ)
    (complementRepresentatives : Set (PositiveDefiniteIntegralLattice (n - 1)))
    (hcomplementRepresentatives_finite : complementRepresentatives.Finite)
    (hcomplementRepresentatives :
      ∀ N : PositiveDefiniteIntegralLattice (n - 1),
        (∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧ N.pairingDeterminant = e) →
          ∃ N₀ ∈ complementRepresentatives, N₀.IsGlobalIsometry N) :
    ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
      ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  classical
  have hcomplement_exists :
      ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
            ∃ N : PositiveDefiniteIntegralLattice (n - 1),
              (∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧ N.pairingDeterminant = e) ∧
                fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement
                  hn d hd μ hμ L N :=
    fixed_rank_atLeastTwo_positive_pairingDeterminant_primitiveMinimumComplement_exists
      hn d hd μ hμ
  have hsingle_complement :=
    fixed_rank_atLeastTwo_positive_pairingDeterminant_single_complement_overlattices
      hn d hd μ hμ complementRepresentatives
  let representativesOfComplement (N₀ : PositiveDefiniteIntegralLattice (n - 1)) :
      Set (PositiveDefiniteIntegralLattice n) :=
    if hN₀ : N₀ ∈ complementRepresentatives then
      Classical.choose (hsingle_complement N₀ hN₀)
    else ∅
  refine ⟨⋃ N₀ ∈ complementRepresentatives, representativesOfComplement N₀,
    ?_, ?_⟩
  · refine hcomplementRepresentatives_finite.biUnion ?_
    intro N₀ hN₀
    dsimp [representativesOfComplement]
    rw [dif_pos hN₀]
    exact (Classical.choose_spec (hsingle_complement N₀ hN₀)).1
  · intro L hdet hminimum
    obtain ⟨N, hN_det, hN_complement⟩ :=
      hcomplement_exists L hdet hminimum
    obtain ⟨N₀, hN₀_mem, hN₀_iso⟩ :=
      hcomplementRepresentatives N hN_det
    obtain ⟨L₀, hL₀_mem, hL₀_iso⟩ :=
      (Classical.choose_spec (hsingle_complement N₀ hN₀_mem)).2
        L hdet hminimum ⟨N, hN_complement, hN₀_iso⟩
    refine ⟨L₀, ?_, hL₀_iso⟩
    refine Set.mem_iUnion.2 ⟨N₀, ?_⟩
    refine Set.mem_iUnion.2 ⟨hN₀_mem, ?_⟩
    dsimp [representativesOfComplement]
    rw [dif_pos hN₀_mem]
    exact hL₀_mem

/-- **Schulze-Pillot fixed-minimum overlattice step**:
after a primitive minimum vector has been chosen, the determinant relation
`det(N) ∣ μ * d` and the lower-rank induction hypothesis give a finite list of
possible orthogonal-complement classes.  This step is
only the passage from those complement classes to actual representatives plus
the finite-overlattice reconstruction step to the original rank-`n` lattice
classes.

The determinant throughout is Schulze--Pillot's `det_B = pairingDeterminant = det(F)`,
not the bilinear discriminant `polarDeterminant = det(2F)`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_representatives_finite_of_fixed_minimum_overlattice
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ)
    (hcomplements :
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice (n - 1)) |
        ∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            N.pairingDeterminant = e ∧ C = N.globalIsometryClass }) :
    ∃ representatives : Set (PositiveDefiniteIntegralLattice n), representatives.Finite ∧
      ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) →
            ∃ L₀ ∈ representatives, L₀.IsGlobalIsometry L := by
  classical
  let complementClasses : Set (Set (PositiveDefiniteIntegralLattice (n - 1))) :=
    { C : Set (PositiveDefiniteIntegralLattice (n - 1)) |
      ∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧
        ∃ N : PositiveDefiniteIntegralLattice (n - 1),
          N.pairingDeterminant = e ∧ C = N.globalIsometryClass }
  have hcomplements' : complementClasses.Finite := by
    simpa [complementClasses] using hcomplements
  haveI : Fintype complementClasses := hcomplements'.fintype
  have hclass_has_rep :
      ∀ C : complementClasses, ∃ N : PositiveDefiniteIntegralLattice (n - 1),
        C.1 = N.globalIsometryClass := by
    intro C
    obtain ⟨e, he_pos, he_dvd, N, hdet, hC⟩ := C.2
    exact ⟨N, hC⟩
  let representativeOfComplementClass : complementClasses → PositiveDefiniteIntegralLattice (n - 1) :=
    fun C => Classical.choose (hclass_has_rep C)
  have hcomplementRepresentatives :
      ∀ N : PositiveDefiniteIntegralLattice (n - 1),
        (∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧ N.pairingDeterminant = e) →
          ∃ N₀ ∈ Set.range representativeOfComplementClass, N₀.IsGlobalIsometry N := by
    intro N hN
    obtain ⟨e, he_pos, he_dvd, hdet⟩ := hN
    let C : complementClasses :=
      ⟨N.globalIsometryClass, ⟨e, he_pos, he_dvd, N, hdet, rfl⟩⟩
    refine ⟨representativeOfComplementClass C, Set.mem_range_self C, ?_⟩
    have hspec := Classical.choose_spec (hclass_has_rep C)
    change N ∈ (representativeOfComplementClass C).globalIsometryClass
    rw [← hspec]
    exact N.mem_globalIsometryClass_self
  rcases fixed_rank_atLeastTwo_positive_pairingDeterminant_representatives_finite_of_fixed_minimum_complement_representatives
      hn d hd μ hμ (Set.range representativeOfComplementClass)
      (Set.finite_range representativeOfComplementClass)
      hcomplementRepresentatives with
    ⟨representatives, hrepresentatives_finite, hcover⟩
  exact ⟨representatives, hrepresentatives_finite, hcover⟩

/-- Fixed-minimum class finiteness follows formally from the finite
representative version of the Schulze--Pillot overlattice reconstruction
source. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_fixed_minimum_representatives
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ)
    (hcomplements :
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice (n - 1)) |
        ∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            N.pairingDeterminant = e ∧ C = N.globalIsometryClass }) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
            C = L.globalIsometryClass } := by
  obtain ⟨representatives, hrepresentatives_finite, hrepresentatives⟩ :=
    fixed_rank_atLeastTwo_positive_pairingDeterminant_representatives_finite_of_fixed_minimum_overlattice
      hn d hd μ hμ hcomplements
  refine global_isometry_classes_finite_of_finite_representatives
    hrepresentatives_finite ?_
  intro C hC
  obtain ⟨L, hdet, hminimum, rfl⟩ := hC
  obtain ⟨L₀, hL₀_mem, hL₀_iso⟩ := hrepresentatives L hdet hminimum
  exact ⟨L₀, hL₀_mem, (globalIsometryClass_eq_of_isGlobalIsometry hL₀_iso).symm⟩

/-- **Schulze-Pillot, fixed-minimum induction step**:
assuming fixed-rank fixed-`det_B` finiteness in every positive lower rank,
there are only finitely many global isometry classes of rank `n ≥ 2` integral
quadratic `ℤ`-lattices with fixed positive Schulze--Pillot determinant
`det_B = pairingDeterminant = det(F)` and fixed positive minimum value `μ`.

This theorem takes the finite divisor union for the orthogonal complement
determinant `det(N) ∣ μ * d` and uses the step above for the primitive-vector
and finite-overlattice reconstruction. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_fixed_minimum
    (hn : 2 ≤ n)
    (hind : ∀ m : ℕ, 0 < m → m < n → ∀ d : ℤ, 0 < d →
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice m) |
        ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = d ∧ C = L.globalIsometryClass })
    (d : ℤ) (hd : 0 < d) (μ : ℤ) (hμ : 0 < μ) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
            C = L.globalIsometryClass } := by
  have hμd : 0 < μ * d := mul_pos hμ hd
  have hcomplements :
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice (n - 1)) |
        ∃ e : ℤ, 0 < e ∧ e ∣ μ * d ∧
          ∃ N : PositiveDefiniteIntegralLattice (n - 1),
            N.pairingDeterminant = e ∧ C = N.globalIsometryClass } :=
    lower_rank_positive_pairingDeterminant_isometry_classes_finite_of_det_divides
      (n := n) hind (by omega) (by omega) (μ * d) hμd
  exact fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_fixed_minimum_representatives
    hn d hd μ hμ hcomplements

/-- **Schulze-Pillot, Theorem [finiteness_classnumber], induction step after
Hermite**:
assuming fixed-rank fixed-`det_B` finiteness in every positive lower rank,
and a fixed-`det_B` Hermite minimum bound in rank `n`, there are only finitely
many global isometry classes of rank `n ≥ 2` integral quadratic `ℤ`-lattices
with fixed positive Schulze--Pillot determinant
`det_B = pairingDeterminant = det(F)`.

This is the reduction-theory step after isolating the
formal rank-one base case, the outer induction, and the Hermite minimum bound.
It corresponds to the orthogonal-complement and finite-overlattice step in
Schulze--Pillot's proof, and uses `pairingDeterminant`, not the bilinear discriminant
`polarDeterminant`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_bounded_minimum
    (hn : 2 ≤ n)
    (hind : ∀ m : ℕ, 0 < m → m < n → ∀ d : ℤ, 0 < d →
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice m) |
        ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = d ∧ C = L.globalIsometryClass })
    (d : ℤ) (hd : 0 < d) (B : ℕ)
    (hB : ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d →
      ∃ μ : ℤ, 0 < μ ∧ μ ≤ (B : ℤ) ∧
        ∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  classical
  let minimumClasses (μ : ℤ) : Set (Set (PositiveDefiniteIntegralLattice n)) :=
    { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧
        (∃ x : Fin n → ℤ, x ≠ 0 ∧ L.quadForm x = μ ∧
          ∀ y : Fin n → ℤ, y ≠ 0 → μ ≤ L.quadForm y) ∧
            C = L.globalIsometryClass }
  let possibleMinima : Set ℤ := { μ : ℤ | 0 < μ ∧ μ ≤ (B : ℤ) }
  have hpossible_finite : possibleMinima.Finite := by
    refine (Set.finite_Icc (1 : ℤ) (B : ℤ)).subset ?_
    intro μ hμ
    change 0 < μ ∧ μ ≤ (B : ℤ) at hμ
    exact ⟨by omega, hμ.2⟩
  have hclasses_finite :
      (⋃ μ ∈ possibleMinima, minimumClasses μ).Finite := by
    refine hpossible_finite.biUnion ?_
    intro μ hμ
    exact fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_fixed_minimum
      hn hind d hd μ hμ.1
  refine hclasses_finite.subset ?_
  intro C hC
  obtain ⟨L, hdet, rfl⟩ := hC
  obtain ⟨μ, hμ_pos, hμ_bound, x, hx, hx_eq, hμ_min⟩ := hB L hdet
  refine Set.mem_iUnion.2 ⟨μ, ?_⟩
  refine Set.mem_iUnion.2 ⟨⟨hμ_pos, hμ_bound⟩, ?_⟩
  exact ⟨L, hdet, ⟨x, hx, hx_eq, hμ_min⟩, rfl⟩

/-- **Schulze-Pillot, Theorem [finiteness_classnumber], induction step**:
assuming fixed-rank fixed-`det_B` finiteness in every positive lower rank,
there are only finitely many global isometry classes of rank `n ≥ 2` integral
quadratic `ℤ`-lattices with fixed positive Schulze--Pillot determinant
`det_B = pairingDeterminant = det(F)`.

The proof separates the fixed-`pairingDeterminant` Hermite minimum bound from
the orthogonal-complement induction step. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_induction_step
    (hn : 2 ≤ n)
    (hind : ∀ m : ℕ, 0 < m → m < n → ∀ d : ℤ, 0 < d →
      Set.Finite { C : Set (PositiveDefiniteIntegralLattice m) |
        ∃ L : PositiveDefiniteIntegralLattice m, L.pairingDeterminant = d ∧ C = L.globalIsometryClass })
    (d : ℤ) (hd : 0 < d) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  obtain ⟨B, hB⟩ :=
    fixed_rank_positive_pairingDeterminant_hermite_minimum_bound_of_matrix_induction
      (by omega : 0 < n) d hd
  exact fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_of_bounded_minimum
    hn hind d hd B hB

/-- Rank-at-least-two fixed-`pairingDeterminant` class-number finiteness, proved by strong
induction on the rank from the formal Hermite minimum bound and the fixed-
minimum overlattice reconstruction. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_by_rank_induction
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  classical
  have h :
      ∀ n : ℕ, 2 ≤ n → ∀ d : ℤ, 0 < d →
        Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
          ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn d hd
        exact
          fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_induction_step
            hn (fun m hm_pos hm_lt d hd => by
              by_cases hm_rank_one : m = 1
              · subst hm_rank_one
                exact fixed_rank_one_pairingDeterminant_isometry_classes_finite d
              · exact ih m hm_lt (by omega) d hd) d hd
  exact h n hn d hd

/-- **Schulze-Pillot, Theorem [finiteness_classnumber], fixed `det_B` form**:
for rank at least two and fixed positive Schulze--Pillot determinant
`det_B = pairingDeterminant = det(F)`, there are only finitely many global isometry
classes of integral quadratic `ℤ`-lattices.

This is the isometry-class projection of the fixed-rank fixed-determinant
representative source theorem.  It is stated in the determinant convention
used by Schulze--Pillot: fixed `pairingDeterminant`, not fixed bilinear discriminant
`polarDeterminant`. -/
theorem fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite
    (hn : 2 ≤ n) (d : ℤ) (hd : 0 < d) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  exact fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite_by_rank_induction
    hn d hd

/-- Fixed-rank fixed-`pairingDeterminant` finiteness in the positive-rank, positive
determinant case.  Rank one is formal; ranks at least two use the
Schulze--Pillot Hermite/reduction-theory step. -/
theorem fixed_positiveRank_positive_pairingDeterminant_isometry_classes_finite
    (hn : 0 < n) (d : ℤ) (hd : 0 < d) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          exact fixed_rank_one_pairingDeterminant_isometry_classes_finite d
      | succ n =>
          exact fixed_rank_atLeastTwo_positive_pairingDeterminant_isometry_classes_finite
            (by omega) d hd

/-- There is at most one rank-zero positive-definite integral lattice. -/
lemma subsingleton_rank_zero : Subsingleton (PositiveDefiniteIntegralLattice 0) := by
  constructor
  intro L L'
  obtain ⟨F, hsym, hpos⟩ := L
  obtain ⟨F', hsym', hpos'⟩ := L'
  have hF : F = F' := Subsingleton.elim F F'
  cases hF
  congr

/-- The fixed-determinant isometry-class set is finite in rank zero.  In this
rank the empty matrix has determinant `1`, so the set is either empty or the
single global isometry class. -/
theorem fixed_rank_zero_pairingDeterminant_isometry_classes_finite (d : ℤ) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice 0) |
      ∃ L : PositiveDefiniteIntegralLattice 0, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  classical
  haveI : Subsingleton (PositiveDefiniteIntegralLattice 0) := subsingleton_rank_zero
  refine Set.Finite.subset
    (Set.finite_singleton (Set.univ : Set (PositiveDefiniteIntegralLattice 0))) ?_
  intro C hC
  obtain ⟨L, hdet, rfl⟩ := hC
  ext L'
  constructor
  · intro h
    trivial
  · intro h
    refine ⟨1, isUnit_one, ?_⟩
    exact Subsingleton.elim _ _

/-- Fixed-rank fixed-`pairingDeterminant` finiteness in the positive determinant case.
Rank zero is formal; positive rank uses the Hermite/minimum and
complement-overlattice induction developed above. -/
theorem fixed_rank_positive_pairingDeterminant_isometry_classes_finite (d : ℤ)
    (hd : 0 < d) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  cases n with
  | zero =>
      exact fixed_rank_zero_pairingDeterminant_isometry_classes_finite d
  | succ n =>
      exact fixed_positiveRank_positive_pairingDeterminant_isometry_classes_finite
        (Nat.succ_pos n) d hd

/-- Fixed-rank fixed-`pairingDeterminant` finiteness, with the nonpositive determinant
case discharged from positive-definiteness. -/
theorem fixed_rank_pairingDeterminant_isometry_classes_finite (d : ℤ) :
    Set.Finite { C : Set (PositiveDefiniteIntegralLattice n) |
      ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } := by
  by_cases hd : 0 < d
  · exact fixed_rank_positive_pairingDeterminant_isometry_classes_finite d hd
  · have h_empty :
        { C : Set (PositiveDefiniteIntegralLattice n) |
          ∃ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = d ∧ C = L.globalIsometryClass } = ∅ := by
      ext C
      constructor
      · rintro ⟨L, hdet, hC⟩
        have hd_pos : 0 < d := by simpa [hdet] using L.pairingDeterminant_pos
        exact (hd hd_pos).elim
      · intro hC
        simp at hC
    simp [h_empty]


/-- **Schulze-Pillot, Corollary to Theorem [finiteness_classnumber]**:
The number of isometry classes in a fixed genus of `ℤ`-lattices is finite.

**Proof**: The genus of `L` is a subset of isometry classes with `det_B` equal
to `L.pairingDeterminant` (by `pairingDeterminant_eq_of_isSameGenus`).  By
`fixed_rank_pairingDeterminant_isometry_classes_finite`, this superset is finite. -/
theorem genus_finite (L : PositiveDefiniteIntegralLattice n) : L.genus.Finite := by
  apply Set.Finite.subset (fixed_rank_pairingDeterminant_isometry_classes_finite L.pairingDeterminant)
  intro C hC
  obtain ⟨L', hL'_genus, hC_eq⟩ := hC
  exact ⟨L', (pairingDeterminant_eq_of_isSameGenus L L' hL'_genus).symm, hC_eq⟩

/-- The genus can be used as a finite index type for the mass sum. -/
noncomputable instance genus_fintype (L : PositiveDefiniteIntegralLattice n) :
    Fintype L.genus := by
  exact L.genus_finite.fintype

end PositiveDefiniteIntegralLattice

end
