import SMSFormula.RationalCliffordGeneralSpinAllRationalShellIndex

/-!
# Positive-definite all-rational-shell Tonelli reassembly

For the rational quadratic space attached to an actual positive-definite
integral lattice, the zero quadratic fiber is the singleton zero vector.
Consequently every nonnegative sum over rational vectors splits exactly into
its zero term and the sum over nonisotropic rational vectors.  Combining this
with the section-free represented-norm index gives the literal iterated sum
over represented nonzero rational norms and their rational fibers.

The summand is arbitrary and `ENNReal`-valued, so no convergence hypothesis
or rearrangement subtraction is needed.  This file attaches no complement
presentation, cutoff, shell measure, Spin volume, or Tamagawa coefficient.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The rational extension of a positive-definite integral-lattice form is
positive on every nonzero rational vector. -/
theorem rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos
    (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ} (hx : x ≠ 0) :
    0 < L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x := by
  let xℝ : Fin n → ℝ := fun i ↦ (x i : ℝ)
  have hxℝ : xℝ ≠ 0 := by
    intro h
    apply hx
    ext i
    exact Rat.cast_eq_zero.mp (congr_fun h i)
  have hpos := L.form_posDef.dotProduct_mulVec_pos (x := xℝ) hxℝ
  have hcast :
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x : ℝ) =
        dotProduct xℝ
          ((L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec xℝ) := by
    simp [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm,
      PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix,
      PositiveDefiniteIntegralLattice.rationalFormMatrix, Matrix.toQuadraticMap',
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, xℝ]
  have hpos_cast :
      0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x : ℝ) := by
    rw [hcast]
    simpa [xℝ] using hpos
  exact Rat.cast_pos.mp hpos_cast

/-- The rational quadratic form of a positive-definite integral lattice
vanishes exactly at the zero vector. -/
theorem rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_eq_zero_iff
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℚ) :
    L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = 0 ↔
      x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hpos :=
      L.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos hx
    rw [h] at hpos
    exact (lt_irrefl 0) hpos
  · rintro rfl
    simp

/-- Every nonnegative sum over the lattice's rational coordinate space is
the zero term plus the literal sum over nonisotropic rational vectors. -/
theorem tsum_rationalVector_eq_zero_add_anisotropic
    (L : PositiveDefiniteIntegralLattice n) (F : (Fin n → ℚ) → ℝ≥0∞) :
    (∑' x, F x) = F 0 +
      ∑' x : L.rationalQuadraticSpaceMatrix.AnisotropicRationalVector,
        F x.1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let p : (Fin n → ℚ) → Prop := fun x ↦ V.nativeRationalQuadraticForm x = 0
  let e := Equiv.sumCompl p
  calc
    (∑' x, F x) = ∑' z, F (e z) := by
      exact (e.tsum_eq F).symm
    _ =
        (∑' z : {x // p x}, F (e (Sum.inl z))) +
          ∑' z : {x // ¬ p x}, F (e (Sum.inr z)) := by
      exact Summable.tsum_sum ENNReal.summable ENNReal.summable
    _ = F 0 + ∑' x : V.AnisotropicRationalVector, F x.1 := by
      congr 1
      let z₀ : {x // p x} := ⟨0, by simp [p]⟩
      rw [tsum_eq_single z₀]
      · rfl
      · intro z hz
        exfalso
        apply hz
        apply Subtype.ext
        exact
          (L.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_eq_zero_iff
            z.1).mp z.2

/-- Tonelli-ready zero/nonzero reassembly indexed section-freely by the
represented nonzero rational norms and their literal vector fibers. -/
theorem tsum_rationalVector_eq_zero_add_representedNorm_fibers
    (L : PositiveDefiniteIntegralLattice n) (F : (Fin n → ℚ) → ℝ≥0∞) :
    (∑' x, F x) = F 0 +
      ∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        ∑' x : a.rationalVectorFiber L.rationalQuadraticSpaceMatrix,
          F x.1 := by
  rw [L.tsum_rationalVector_eq_zero_add_anisotropic F]
  rw [L.rationalQuadraticSpaceMatrix
    |>.tsum_anisotropicRationalVector_eq_representedNorm_fibers]
  congr 1

end PositiveDefiniteIntegralLattice
