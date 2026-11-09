import SMSFormula.QuadraticFormSimilarityToolkit

/-!
# The quaternion lattice of a ternary lattice and the similarity of its complements

For a positive definite ternary lattice `T` with a diagonalization `T ⊗ ℚ ≅ ⟨a, b, c⟩` (`a, b, c > 0`), the
positive diagonal lattice `U` of rank four whose rational form is (up to coordinate scaling) the reduced norm
`⟨1, ab, ac, a²bc⟩` of `ℍ[ℚ, −ab, −ac]` has the property that every anisotropic rational complement `x^⊥ ⊂ U ⊗ ℚ` is
isometric to `k T ⊗ ℚ` for some integer `k > 0` (`exists_quaternionLattice_complement_isometry_smul`): by the
quaternion core, `x^⊥ ≅ N(x) · ⟨ab, ac, a²bc⟩ ≅ N(x) abc · ⟨a, b, c⟩ ≅ N(x) abc · T`, and a positive rational scaling
`p/q` is isometric to the integral scaling `p q`.
The diagonalization is proof-internal; nothing in the statement is chosen.
-/

noncomputable section

open Module QuadraticMap Matrix
open scoped Quaternion

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The positive diagonal lattice with diagonal entries `d`. -/
def ofPosDiagonal (d : Fin n → ℤ) (hd : ∀ i, 0 < d i) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := diagonal d
  form_symm := by simp [Matrix.IsSymm]
  form_posDef := by
    rw [diagonal_map (by simp)]
    exact posDef_diagonal_iff.2 fun i ↦ by simpa using hd i

/-- The integral scaling `k L`. -/
def smulLattice (L : PositiveDefiniteIntegralLattice n) (k : ℕ) (hk : 0 < k) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := (k : ℤ) • L.pairingMatrix
  form_symm := L.form_symm.smul _
  form_posDef := by
    have h : ((k : ℤ) • L.pairingMatrix).map (Int.cast : ℤ → ℝ) =
        (k : ℝ) • L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [h]
    exact L.form_posDef.smul (by exact_mod_cast hk)

theorem rationalQuadraticForm_apply (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℚ) :
    L.rationalQuadraticSpaceMatrix.quadraticForm x =
      x ⬝ᵥ (L.pairingMatrix.map (algebraMap ℤ ℚ)) *ᵥ x := by
  simpa [RationalQuadraticSpaceMatrix.quadraticForm, Matrix.toQuadraticMap',
    rationalQuadraticSpaceMatrix_pairingMatrix, rationalFormMatrix] using
    Matrix.toLinearMap₂'_apply' (L.pairingMatrix.map (algebraMap ℤ ℚ)) x x

theorem ofPosDiagonal_quadraticForm (d : Fin n → ℤ) (hd : ∀ i, 0 < d i) :
    (ofPosDiagonal d hd).rationalQuadraticSpaceMatrix.quadraticForm =
      weightedSumSquares ℚ (fun i ↦ (d i : ℚ)) := by
  ext x
  rw [rationalQuadraticForm_apply, weightedSumSquares_apply]
  simp only [ofPosDiagonal, diagonal_map (map_zero _), mulVec_diagonal, dotProduct, smul_eq_mul,
    algebraMap_int_eq, eq_intCast]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem smulLattice_quadraticForm (L : PositiveDefiniteIntegralLattice n) (k : ℕ) (hk : 0 < k) :
    (L.smulLattice k hk).rationalQuadraticSpaceMatrix.quadraticForm =
      (k : ℚ) • L.rationalQuadraticSpaceMatrix.quadraticForm := by
  ext x
  rw [QuadraticMap.smul_apply, rationalQuadraticForm_apply, rationalQuadraticForm_apply, smul_eq_mul]
  have h : ((L.smulLattice k hk).pairingMatrix).map (algebraMap ℤ ℚ) =
      (k : ℚ) • L.pairingMatrix.map (algebraMap ℤ ℚ) := by
    ext i j
    simp only [smulLattice, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, algebraMap_int_eq,
      eq_intCast]
    push_cast
    ring
  rw [h, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-! ## The quaternion lattice -/

/-- The integral representative `w · den(w)²` of a positive rational weight. -/
theorem num_mul_den_pos {w : ℚ} (hw : 0 < w) : 0 < w.num * (w.den : ℤ) :=
  mul_pos (Rat.num_pos.2 hw) (by exact_mod_cast w.den_pos)

theorem num_mul_den_eq (w : ℚ) : ((w.num * (w.den : ℤ) : ℤ) : ℚ) = w * (w.den : ℚ) ^ 2 := by
  rw [Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num]
  ring

/-- The diagonal lattice with rational form `⟨w₀ den₀², w₁ den₁², …⟩ ≅ ⟨w₀, w₁, …⟩`. -/
def ofPosRatDiagonal (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) : PositiveDefiniteIntegralLattice n :=
  ofPosDiagonal (fun i ↦ (w i).num * ((w i).den : ℤ)) fun i ↦ num_mul_den_pos (hw i)

theorem nonempty_ofPosRatDiagonal_isometryEquiv (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    Nonempty ((ofPosRatDiagonal w hw).rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (weightedSumSquares ℚ w)) := by
  have h : (ofPosRatDiagonal w hw).rationalQuadraticSpaceMatrix.quadraticForm =
      weightedSumSquares ℚ (fun i ↦ w i * ((w i).den : ℚ) ^ 2) := by
    rw [ofPosRatDiagonal, ofPosDiagonal_quadraticForm]
    congr 1
    funext i
    exact num_mul_den_eq (w i)
  rw [h]
  exact ⟨weightedSumSquaresSqScaleIsometry w (fun i ↦ ((w i).den : ℚ)) fun i ↦
    Nat.cast_ne_zero.2 (w i).den_ne_zero⟩

theorem quaternionWeights_pos {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, 0 < (![1, a * b, a * c, a * a * b * c] : Fin 4 → ℚ) i := by
  intro i
  fin_cases i <;> simp <;> positivity

/-- The quaternion lattice of a positive diagonal ternary form `⟨a, b, c⟩`. -/
def quaternionLattice {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : PositiveDefiniteIntegralLattice 4 :=
  ofPosRatDiagonal ![1, a * b, a * c, a * a * b * c] (quaternionWeights_pos ha hb hc)

end PositiveDefiniteIntegralLattice
