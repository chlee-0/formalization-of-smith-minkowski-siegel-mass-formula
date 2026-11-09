import Mathlib.Algebra.Quaternion
import SMSFormula.QuadraticCartanDieudonneOrthogonal
import SMSFormula.RationalQuadraticSpaceAnisotropicDecomposition
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellTonelli

/-!
# Isometry and similarity toolkit for the quaternion bootstrap

* `IsometryEquiv.orthogonalRestrictionMap`: an isometry `Q₁ ≅ Q₂` restricts to `x^⊥ ≅ (e x)^⊥`;
* `IsometryEquiv.smulForm`: an isometry `Q₁ ≅ Q₂` is an isometry `c • Q₁ ≅ c • Q₂`;
* `exists_pos_weightedSumSquares_isometryEquiv`: a positive definite rational form on `ℚ³` is isometric to
  `⟨a, b, c⟩` with `a, b, c > 0`;
* `weightedSumSquaresQuaternionPureIsometry`: `⟨ab, ac, a²bc⟩ ≅ abc · ⟨a, b, c⟩`;
* `weightedSumSquaresSqScaleIsometry`: `⟨wᵢ⟩ ≅ ⟨wᵢ mᵢ²⟩`, and `smulWeightedSumSquaresRatIsometry`:
  `(p/q) • Q ≅ (p q) • Q`.
Nothing is chosen in any statement.
-/

noncomputable section

open Module QuadraticMap

namespace QuadraticMap.IsometryEquiv

variable {K M₁ M₂ : Type*} [Field K] [CharZero K] [AddCommGroup M₁] [Module K M₁]
  [AddCommGroup M₂] [Module K M₂] {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}

theorem apply_symm_apply' (e : Q₁.IsometryEquiv Q₂) (z : M₂) : e (e.symm z) = z :=
  e.toLinearEquiv.apply_symm_apply z

theorem symm_apply_apply' (e : Q₁.IsometryEquiv Q₂) (z : M₁) : e.symm (e z) = z :=
  e.toLinearEquiv.symm_apply_apply z

theorem associated_map (e : Q₁.IsometryEquiv Q₂) (x y : M₁) :
    Q₂.associated (e x) (e y) = Q₁.associated x y := by
  rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply, ← map_add, e.map_app, e.map_app,
    e.map_app]

/-- An isometry restricts to the orthogonal complements `x^⊥ ≅ (e x)^⊥`. -/
def orthogonalRestrictionMap (e : Q₁.IsometryEquiv Q₂) (x : M₁) :
    (Q₁.orthogonalRestriction x).IsometryEquiv (Q₂.orthogonalRestriction (e x)) where
  toFun y := ⟨e (y : M₁), Q₂.mem_anisotropicOrthogonal_iff.2 (by
    change Q₂.associated (e x) (e (y : M₁)) = 0
    rw [e.associated_map]
    exact Q₁.mem_anisotropicOrthogonal_iff.1 y.2)⟩
  invFun y := ⟨e.symm (y : M₂), Q₁.mem_anisotropicOrthogonal_iff.2 (by
    change Q₁.associated x (e.symm (y : M₂)) = 0
    rw [← e.associated_map, e.apply_symm_apply']
    exact Q₂.mem_anisotropicOrthogonal_iff.1 y.2)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply' (y : M₁))
  right_inv y := Subtype.ext (e.apply_symm_apply' (y : M₂))
  map_add' y z := Subtype.ext (map_add e (y : M₁) z)
  map_smul' r y := Subtype.ext (map_smul e r (y : M₁))
  map_app' y := e.map_app (y : M₁)

/-- An isometry `Q₁ ≅ Q₂` is an isometry `c • Q₁ ≅ c • Q₂`. -/
def smulForm (e : Q₁.IsometryEquiv Q₂) (c : K) : (c • Q₁).IsometryEquiv (c • Q₂) where
  toLinearEquiv := e.toLinearEquiv
  map_app' y := by
    change c • Q₂ (e y) = c • Q₁ y
    rw [e.map_app]

end QuadraticMap.IsometryEquiv

namespace QuadraticMap

/-- `⟨wᵢ⟩ ≅ ⟨wᵢ mᵢ²⟩` for nonzero `mᵢ` (coordinate scaling). -/
def weightedSumSquaresSqScaleIsometry {K : Type*} [Field K] {ι : Type*} [Fintype ι] (w m : ι → K)
    (hm : ∀ i, m i ≠ 0) :
    (weightedSumSquares K fun i ↦ w i * m i ^ 2).IsometryEquiv (weightedSumSquares K w) where
  toFun v i := m i * v i
  invFun v i := (m i)⁻¹ * v i
  left_inv v := by funext i; simp [hm i]
  right_inv v := by funext i; simp [hm i]
  map_add' v u := by funext i; simp [mul_add]
  map_smul' r v := by funext i; simp [mul_left_comm]
  map_app' v := by
    simp only [weightedSumSquares_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

/-- `⟨ab, ac, a²bc⟩ ≅ abc · ⟨a, b, c⟩`. -/
def weightedSumSquaresQuaternionPureIsometry {K : Type*} [Field K] (a b c : K) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    (weightedSumSquares K ![a * b, a * c, a * a * b * c]).IsometryEquiv
      ((a * b * c) • weightedSumSquares K ![a, b, c]) where
  toFun y := ![y 2, y 1 / b, y 0 / c]
  invFun z := ![z 2 * c, z 1 * b, z 0]
  left_inv y := by
    funext i
    fin_cases i <;> simp [hb, hc]
  right_inv z := by
    funext i
    fin_cases i <;> simp [hb, hc]
  map_add' y u := by
    funext i
    fin_cases i <;> simp [add_div]
  map_smul' r y := by
    funext i
    fin_cases i <;> simp [mul_div_assoc]
  map_app' y := by
    change (a * b * c) • weightedSumSquares K ![a, b, c] ![y 2, y 1 / b, y 0 / c] =
      weightedSumSquares K ![a * b, a * c, a * a * b * c] y
    simp only [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring

/-- `(p q) • Q ≅ (p/q) • Q` (scale by `q`). -/
def smulRatIsometry {M : Type*} [AddCommGroup M] [Module ℚ M] (Q : QuadraticForm ℚ M) (p : ℤ) (q : ℕ)
    (hq : q ≠ 0) :
    (((p : ℚ) * q) • Q).IsometryEquiv (((p : ℚ) / q) • Q) where
  toFun v := (q : ℚ) • v
  invFun v := (q : ℚ)⁻¹ • v
  left_inv v := by
    simp [smul_smul, (Nat.cast_ne_zero.2 hq : (q : ℚ) ≠ 0)]
  right_inv v := by
    simp [smul_smul, (Nat.cast_ne_zero.2 hq : (q : ℚ) ≠ 0)]
  map_add' v u := smul_add _ v u
  map_smul' r v := smul_comm _ r v
  map_app' v := by
    change ((p : ℚ) / q) • Q ((q : ℚ) • v) = ((p : ℚ) * q) • Q v
    rw [QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq
    field_simp

/-- Reindexing a weighted sum of squares along an equivalence of index types. -/
def weightedSumSquaresReindexIsometry {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → K) :
    (weightedSumSquares K w).IsometryEquiv (weightedSumSquares K (w ∘ e.symm)) where
  toFun v := v ∘ e.symm
  invFun v := v ∘ e
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v u := rfl
  map_smul' r v := rfl
  map_app' v := by
    simp only [weightedSumSquares_apply, Function.comp_apply]
    exact Equiv.sum_comp e.symm (fun i ↦ w i • (v i * v i))

end QuadraticMap

namespace RationalQuadraticSpaceMatrix

open QuadraticMap

/-- A positive definite rational form on `ℚ³` is isometric to a positive diagonal form `⟨a, b, c⟩`. -/
theorem exists_pos_weightedSumSquares_isometryEquiv (Q : QuadraticForm ℚ (Fin 3 → ℚ))
    (hQ : ∀ x, x ≠ 0 → 0 < Q x) :
    ∃ w : Fin 3 → ℚ, (∀ i, 0 < w i) ∧ Nonempty (Q.IsometryEquiv (weightedSumSquares ℚ w)) := by
  classical
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  have hfr : finrank ℚ (Fin 3 → ℚ) = 3 := by simp
  set f : Fin (finrank ℚ (Fin 3 → ℚ)) ≃ Fin 3 := finCongr hfr with hfdef
  refine ⟨w ∘ f.symm, fun i ↦ ?_, ⟨e.trans (weightedSumSquaresReindexIsometry f w)⟩⟩
  have hv : e.symm (Pi.single (f.symm i) 1) ≠ 0 := by
    intro h
    have := congrArg e h
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply', map_zero] at this
    exact one_ne_zero (congrFun this (f.symm i) |>.symm.trans (by simp) |>.symm)
  have hpos := hQ _ hv
  rw [← e.map_app, QuadraticMap.IsometryEquiv.apply_symm_apply', weightedSumSquares_apply] at hpos
  simpa [Pi.single_apply] using hpos

end RationalQuadraticSpaceMatrix
