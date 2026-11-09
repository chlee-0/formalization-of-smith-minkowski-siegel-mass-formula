import SMSFormula.AdelicGaussianSpinTamagawaEisensteinComparison
import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormCoefficient
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellTonelli

/-!
# Every anisotropic complement carries an integral lattice

For a positive definite integral lattice `L` of rank `m + 1` and a rational vector `x` with
`Q(x) ≠ 0`, the orthogonal complement `x^⊥` (rational dimension `m`) is isometric to the rational
quadratic space of an integral lattice of rank `m`.  Take any rational basis of `x^⊥` and clear its
coordinate denominators: the resulting integer coordinate matrix `B` gives the integral Gram matrix
`Bᵀ F B` (`F` the integral form matrix).  Positive definiteness over `ℝ` follows from that of
`F` and injectivity of `B` over `ℝ`, which is deduced from the nonvanishing of the integral
determinant (itself forced by positivity over `ℚ`).

Consequently `OneShellSpinCoefficientLocallyNonempty` (the local complement-lattice input of the
one-shell coefficient and of the core theorem) holds for every positive definite integral
lattice of rank at least four.  The statements are pure existence (`∃`/`Nonempty`): no complement
lattice, basis or presentation is selected in any statement.
-/

noncomputable section

open Matrix PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix QuadraticMap

namespace PositiveDefiniteIntegralLattice

variable {m : ℕ}

/-- Existence of an integral complement lattice: `x^⊥` is isometric to the rational space of an
integral lattice of rank `m`. -/
theorem exists_integralLattice_isometryEquiv_orthogonalRestriction_integral
    (L : PositiveDefiniteIntegralLattice (m + 1))
    (x : Fin (m + 1) → ℚ) (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0) :
    ∃ LW : PositiveDefiniteIntegralLattice m, ∃ e : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x),
      ∀ (k : Fin m) (i : Fin (m + 1)),
        ((e (Pi.single k 1) : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.anisotropicOrthogonal x) :
          Fin (m + 1) → ℚ) i ∈ (algebraMap ℤ ℚ).range := by
  classical
  set Q := L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm with hQdef
  set E := Q.anisotropicOrthogonal x with hEdef
  have hdim : Module.finrank ℚ E = m := by
    have h := Q.finrank_anisotropicOrthogonal_add_one x hx
    rw [Module.finrank_fin_fun, ← hEdef] at h
    omega
  let b : Module.Basis (Fin m) ℚ E := Module.finBasisOfFinrankEq ℚ E hdim
  -- clear the coordinate denominators
  set d : ℕ := ∏ i : Fin (m + 1), ∏ j : Fin m, ((b j : Fin (m + 1) → ℚ) i).den with hddef
  have hd : d ≠ 0 := by
    rw [hddef, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact Rat.den_ne_zero _
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hint : ∀ i j, ∃ z : ℤ, (z : ℚ) = d * (b j : Fin (m + 1) → ℚ) i := by
    intro i j
    have hdvd : ((b j : Fin (m + 1) → ℚ) i).den ∣ d :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j' ↦ ((b j' : Fin (m + 1) → ℚ) i).den)
        (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem (fun i' ↦ ∏ j' : Fin m, ((b j' : Fin (m + 1) → ℚ) i').den)
          (Finset.mem_univ i))
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c * ((b j : Fin (m + 1) → ℚ) i).num, ?_⟩
    rw [hc]
    push_cast
    rw [mul_comm (((b j : Fin (m + 1) → ℚ) i).den : ℚ) (c : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose Bz hBz using hint
  set Bint : Matrix (Fin (m + 1)) (Fin m) ℤ := Matrix.of fun i j ↦ Bz i j with hBintdef
  set FW : Matrix (Fin m) (Fin m) ℤ := Bintᵀ * L.pairingMatrix * Bint with hFWdef
  set Bq : Matrix (Fin (m + 1)) (Fin m) ℚ := Bint.map (algebraMap ℤ ℚ) with hBqdef
  -- the coordinate linear equivalence and its matrix
  let e : (Fin m → ℚ) ≃ₗ[ℚ] E :=
    (LinearEquiv.smulOfNeZero ℚ (Fin m → ℚ) (d : ℚ) hdq).trans b.equivFun.symm
  have hcoe : ∀ y, ((e y : E) : Fin (m + 1) → ℚ) = Bq *ᵥ y := by
    intro y
    funext i
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
      Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hBqdef, hBintdef, Matrix.map_apply,
      Matrix.of_apply, eq_intCast, hBz]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hFq : L.rationalQuadraticSpaceMatrix.pairingMatrix = L.pairingMatrix.map (algebraMap ℤ ℚ) := rfl
  have hGq : FW.map (algebraMap ℤ ℚ) = Bqᵀ * L.rationalQuadraticSpaceMatrix.pairingMatrix * Bq := by
    rw [hFWdef, hFq, hBqdef, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hquad : ∀ y : Fin m → ℚ,
      Q (Bq *ᵥ y) = y ⬝ᵥ (FW.map (algebraMap ℤ ℚ) *ᵥ y) := by
    intro y
    rw [hQdef, L.nativeRationalQuadraticForm_eq_gramQuadraticValue, gramQuadraticValue, hGq]
    have hmv : (Bqᵀ * L.rationalQuadraticSpaceMatrix.pairingMatrix * Bq) *ᵥ y =
        Bqᵀ *ᵥ (L.rationalQuadraticSpaceMatrix.pairingMatrix *ᵥ (Bq *ᵥ y)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hmv, Matrix.dotProduct_mulVec y Bqᵀ, Matrix.vecMul_transpose]
  -- injectivity over ℚ and nonvanishing determinant
  have hBq_inj : ∀ y, Bq *ᵥ y = 0 → y = 0 := by
    intro y hy
    rw [← hcoe] at hy
    have : e y = 0 := Subtype.ext hy
    exact (LinearEquiv.map_eq_zero_iff e).1 this
  have hdet : FW.det ≠ 0 := by
    intro h0
    have hq0 : (FW.map (algebraMap ℤ ℚ)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨y, hy, hGy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hq0
    have hQ0 : Q (Bq *ᵥ y) = 0 := by rw [hquad, hGy, dotProduct_zero]
    by_cases hB : Bq *ᵥ y = 0
    · exact hy (hBq_inj y hB)
    · exact (L.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos hB).ne' hQ0
  -- the integral lattice
  have hsymm : FW.IsSymm := by
    rw [Matrix.IsSymm, hFWdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      L.form_symm.eq, Matrix.mul_assoc]
  have hposdef : (FW.map (Int.cast : ℤ → ℝ)).PosDef := by
    set f : ℤ →+* ℝ := Int.castRingHom ℝ
    set Br : Matrix (Fin (m + 1)) (Fin m) ℝ := Bint.map f with hBrdef
    have hmap : FW.map (Int.cast : ℤ → ℝ) = Brᴴ * L.pairingMatrix.map (Int.cast : ℤ → ℝ) * Br := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hFWdef, hBrdef]
      change (Bintᵀ * L.pairingMatrix * Bint).map f = _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      rfl
    have hinj : Function.Injective Br.mulVec := by
      have hker : ∀ y, Br *ᵥ y = 0 → y = 0 := by
        intro y hy
        by_contra hy0
        have hGy : FW.map (Int.cast : ℤ → ℝ) *ᵥ y = 0 := by
          rw [hmap, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
        have hr0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨y, hy0, hGy⟩
        rw [show FW.map (Int.cast : ℤ → ℝ) = f.mapMatrix FW from rfl, ← RingHom.map_det] at hr0
        exact hdet (Int.cast_eq_zero.1 (by simpa [f] using hr0))
      intro y y' hyy'
      have : Br *ᵥ (y - y') = 0 := by
        rw [Matrix.mulVec_sub, sub_eq_zero]
        exact hyy'
      exact sub_eq_zero.1 (hker _ this)
    rw [hmap]
    exact L.form_posDef.conjTranspose_mul_mul_same hinj
  let LW : PositiveDefiniteIntegralLattice m := ⟨FW, hsymm, hposdef⟩
  refine ⟨LW, { toLinearEquiv := e, map_app' := fun y ↦ ?_ }, fun k i ↦ ?_⟩
  · change Q ((e y : E) : Fin (m + 1) → ℚ) = LW.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm y
    rw [hcoe, hquad, LW.nativeRationalQuadraticForm_eq_gramQuadraticValue, gramQuadraticValue]
    rfl
  · change ((e (Pi.single k 1) : E) : Fin (m + 1) → ℚ) i ∈ (algebraMap ℤ ℚ).range
    rw [hcoe, Matrix.mulVec_single_one]
    exact ⟨Bint i k, rfl⟩

/-- Existence of an integral complement lattice (bare form). -/
theorem exists_integralLattice_isometryEquiv_orthogonalRestriction (L : PositiveDefiniteIntegralLattice (m + 1))
    (x : Fin (m + 1) → ℚ) (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0) :
    ∃ LW : PositiveDefiniteIntegralLattice m, Nonempty
      (LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x)) := by
  obtain ⟨LW, e, -⟩ := L.exists_integralLattice_isometryEquiv_orthogonalRestriction_integral x hx
  exact ⟨LW, ⟨e⟩⟩

/-- The local complement-lattice input holds: every represented nonzero norm of a positive definite
integral lattice of rank at least four has an integral complement-lattice witness. -/
theorem oneShellSpinCoefficientLocallyNonempty (L : PositiveDefiniteIntegralLattice (m + 1)) (hm : 3 ≤ m) :
    L.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty := by
  intro a
  obtain ⟨x, hx⟩ := a.2.2
  have hQx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0 := by
    rw [hx]
    exact a.2.1
  obtain ⟨LW, ⟨eIso⟩⟩ := L.exists_integralLattice_isometryEquiv_orthogonalRestriction x hQx
  exact ⟨⟨m, LW, hm, ⟨x, hx⟩, eIso⟩⟩

end PositiveDefiniteIntegralLattice
