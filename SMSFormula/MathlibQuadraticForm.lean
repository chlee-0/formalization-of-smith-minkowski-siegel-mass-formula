import SMSFormula.IntegralQuadraticFormBridge
import SMSFormula.StandardAxiomsGuard
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Integral quadratic forms in Mathlib's language

The formalization stores a positive-definite integral quadratic form through matrices:
`PositiveDefiniteIntegralQuadraticForm n` stores the integral polar Gram matrix `A` of `Q` (so `Q(x) = xᵀ T x` for the
half-integral matrix `T = A / 2`), and `PositiveDefiniteIntegralLattice n` stores an integral matrix `F` with
`Q(x) = xᵀ F x`, the classically integral case. This file identifies both with Mathlib objects:

* `PositiveDefiniteIntegralQuadraticForm.equivQuadraticForm`:
  `PositiveDefiniteIntegralQuadraticForm n ≃ {Q : QuadraticForm ℤ (Fin n → ℤ) // Q.PosDef}`;
* `PositiveDefiniteIntegralLattice.equivQuadraticForm`: the same for `PositiveDefiniteIntegralLattice n` and the forms whose polar
  form takes even values on the standard basis;
* integral isometries `Uᵀ F U = F` are `QuadraticMap.IsometryEquiv`s, and global integral isometry
  of two lattices is `QuadraticMap.Equivalent`.

The bridge to matrices goes through `Matrix.toQuadraticMap'` and the polar matrix
`polarMatrix Q i j = polar Q eᵢ eⱼ`; Mathlib's `QuadraticForm.toMatrix'` needs `2` to be
invertible and is not available over `ℤ`.
-/

noncomputable section

open Matrix

namespace Matrix

/-- Positivity on integral vectors gives positivity on rational vectors. -/
theorem dotProduct_mulVec_pos_rat_of_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ x : Fin n → ℤ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) (y : Fin n → ℚ) (hy : y ≠ 0) :
    0 < y ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ y := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) y
  choose z hz using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hzy : (fun i => ((z i : ℤ) : ℚ)) = (b : ℤ) • y := by
    ext i; simpa [Algebra.smul_def] using hz i
  have hz0 : z ≠ 0 := by
    intro h; apply hy
    have : (b : ℤ) • y = 0 := by rw [← hzy]; ext i; simp [h]
    ext i
    have := congrFun this i
    simp [hb0] at this
    exact this
  have hcast : ((z ⬝ᵥ A *ᵥ z : ℤ) : ℚ) =
      ((b : ℤ) : ℚ) ^ 2 * (y ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ y) := by
    have h1 : ((z ⬝ᵥ A *ᵥ z : ℤ) : ℚ) =
        (fun i => ((z i : ℤ) : ℚ)) ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ (fun i => ((z i : ℤ) : ℚ)) := by
      simp only [dotProduct, mulVec, Matrix.map_apply]
      push_cast
      rfl
    rw [h1, hzy, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]
    simp [pow_two, zsmul_eq_mul]
  have : (0 : ℚ) < ((b : ℤ) : ℚ) ^ 2 * (y ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ y) := by
    rw [← hcast]; exact_mod_cast hA z hz0
  exact pos_of_mul_pos_right this (sq_nonneg _)

/-- An integral symmetric matrix is positive definite over `ℝ` exactly when `xᵀ A x > 0` for every
nonzero integral vector `x`. Positivity extends from integral to rational vectors by clearing
denominators and to real ones by density; it stays strict because a real kernel vector of `A`
forces `det A = 0`, hence a rational kernel vector. -/
theorem posDef_map_intCast_real_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) :
    (A.map (Int.cast : ℤ → ℝ)).PosDef ↔ ∀ x : Fin n → ℤ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x := by
  constructor
  · intro h x hx
    have hx' : (fun i => ((x i : ℤ) : ℝ)) ≠ 0 := by
      intro h0; apply hx; ext i; simpa using congrFun h0 i
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hx'
    have hc : ((x ⬝ᵥ A *ᵥ x : ℤ) : ℝ) =
        star (fun i => ((x i : ℤ) : ℝ)) ⬝ᵥ (A.map (Int.cast : ℤ → ℝ)) *ᵥ
          (fun i => ((x i : ℤ) : ℝ)) := by
      simp only [dotProduct, mulVec, Matrix.map_apply, star_trivial]
      push_cast
      rfl
    exact_mod_cast hc ▸ this
  · intro hpos
    set B := A.map (Int.cast : ℤ → ℝ) with hB
    have herm : B.IsHermitian := by
      ext i j
      simp [B, Matrix.conjTranspose_apply, star_trivial, hA.apply i j]
    have hq := dotProduct_mulVec_pos_rat_of_int A hpos
    let f : (Fin n → ℝ) → ℝ := fun x => x ⬝ᵥ B *ᵥ x
    have hf : Continuous f :=
      continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    let e : (Fin n → ℚ) → (Fin n → ℝ) := fun y i => (y i : ℝ)
    have he : DenseRange e := by
      have hd : Dense (Set.univ.pi fun _ : Fin n => Set.range (Rat.cast : ℚ → ℝ)) :=
        dense_pi _ fun _ _ => Rat.denseRange_cast
      have : Set.range e = Set.univ.pi fun _ : Fin n => Set.range (Rat.cast : ℚ → ℝ) := by
        ext x
        simp only [Set.mem_range, Set.mem_pi, Set.mem_univ, true_implies, e]
        constructor
        · rintro ⟨y, rfl⟩ i; exact ⟨y i, rfl⟩
        · intro h; choose y hy using h; exact ⟨y, funext hy⟩
      simpa [DenseRange, this] using hd
    have hfe : ∀ y : Fin n → ℚ,
        f (e y) = ((y ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ y : ℚ) : ℝ) := by
      intro y
      simp only [f, e, B, dotProduct, mulVec, Matrix.map_apply]
      push_cast
      rfl
    have hnn : ∀ x, 0 ≤ f x := by
      intro x
      refine he.induction_on (p := fun x => 0 ≤ f x) x (isClosed_le continuous_const hf) ?_
      intro y
      rw [hfe]
      by_cases hy : y = 0
      · subst hy; simp
      · exact_mod_cast (hq y hy).le
    have hpsd : B.PosSemidef :=
      Matrix.posSemidef_iff_dotProduct_mulVec.mpr
        ⟨herm, fun x => by simpa [star_trivial] using hnn x⟩
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨herm, fun x hx => ?_⟩
    rw [star_trivial]
    refine lt_of_le_of_ne (hnn x) (fun h0 => ?_)
    have hker : B *ᵥ x = 0 :=
      (hpsd.dotProduct_mulVec_zero_iff x).mp (by simpa [star_trivial] using h0.symm)
    have hdetB : B.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
    have hdet : A.det = 0 := by
      have : ((A.det : ℤ) : ℝ) = 0 := by
        rw [← hdetB, hB]; simpa using (Int.castRingHom ℝ).map_det A
      exact_mod_cast this
    have hdetQ : (A.map (Int.cast : ℤ → ℚ)).det = 0 := by
      rw [show (A.map (Int.cast : ℤ → ℚ)) = (Int.castRingHom ℚ).mapMatrix A from rfl,
        ← RingHom.map_det, hdet, map_zero]
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
    have := hq v hv
    rw [hAv, dotProduct_zero] at this
    exact lt_irrefl _ this

end Matrix

namespace QuadraticMap

variable {n : ℕ}

/-- The polar matrix of an integral quadratic form: `polarMatrix Q i j = polar Q eᵢ eⱼ`, the Gram
matrix of the polar bilinear form `polar Q x y = Q (x + y) - Q x - Q y`. -/
def polarMatrix (Q : QuadraticForm ℤ (Fin n → ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => polar Q (Pi.single i 1) (Pi.single j 1)

/-- The polar form is the bilinear form of the polar matrix. -/
theorem polar_eq_dotProduct_polarMatrix (Q : QuadraticForm ℤ (Fin n → ℤ)) (x y : Fin n → ℤ) :
    polar Q x y = x ⬝ᵥ Q.polarMatrix *ᵥ y := by
  have h : Q.polarMatrix = LinearMap.BilinForm.toMatrix' Q.polarBilin := by
    ext i j
    simp [polarMatrix, LinearMap.BilinForm.toMatrix'_apply]
  rw [h, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix']
  rfl

theorem polarMatrix_isSymm (Q : QuadraticForm ℤ (Fin n → ℤ)) : Q.polarMatrix.IsSymm := by
  ext i j
  exact polar_comm Q _ _

theorem polarMatrix_apply_self (Q : QuadraticForm ℤ (Fin n → ℤ)) (i : Fin n) :
    Q.polarMatrix i i = 2 * Q (Pi.single i 1) := by
  simp [polarMatrix, polar_self, two_mul]

/-- `xᵀ A x = 2 Q(x)` for the polar matrix `A`. -/
theorem dotProduct_polarMatrix_mulVec_self (Q : QuadraticForm ℤ (Fin n → ℤ)) (x : Fin n → ℤ) :
    x ⬝ᵥ Q.polarMatrix *ᵥ x = 2 * Q x := by
  rw [← polar_eq_dotProduct_polarMatrix, polar_self, two_smul, two_mul]

/-- Two integral quadratic forms with the same polar matrix are equal. -/
theorem eq_of_polarMatrix_eq {Q Q' : QuadraticForm ℤ (Fin n → ℤ)}
    (h : Q.polarMatrix = Q'.polarMatrix) : Q = Q' := by
  ext x
  have h2 : 2 * Q x = 2 * Q' x := by
    rw [← dotProduct_polarMatrix_mulVec_self, ← dotProduct_polarMatrix_mulVec_self, h]
  exact mul_left_cancel₀ two_ne_zero h2

end QuadraticMap

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

/-- The quadratic form of `H` is positive definite in Mathlib's sense. -/
theorem quadraticForm_posDef (H : PositiveDefiniteIntegralQuadraticForm n) : H.quadraticForm.PosDef :=
  fun _ hx => H.quadForm_pos hx

/-- The polar matrix of the quadratic form of `H` is the stored polar Gram matrix. -/
theorem polarMatrix_quadraticForm (H : PositiveDefiniteIntegralQuadraticForm n) :
    H.quadraticForm.polarMatrix = H.polarGramMatrix := by
  ext i j
  simp [QuadraticMap.polarMatrix, H.polar_eq_dotProduct]

/-- The positive-definite integral quadratic form `Q`, stored through its polar matrix. -/
def ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) : PositiveDefiniteIntegralQuadraticForm n where
  polarGramMatrix := Q.polarMatrix
  polarGram_symm := Q.polarMatrix_isSymm
  polarGram_even_diag i := ⟨Q (Pi.single i 1), by rw [Q.polarMatrix_apply_self, two_mul]⟩
  polarGram_posDef := by
    refine (Matrix.posDef_map_intCast_real_iff _ Q.polarMatrix_isSymm).mpr fun x hx => ?_
    rw [Q.dotProduct_polarMatrix_mulVec_self]
    exact mul_pos two_pos (hQ x hx)

@[simp] theorem ofQuadraticForm_polarGramMatrix (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    (ofQuadraticForm Q hQ).polarGramMatrix = Q.polarMatrix := rfl

theorem quadraticForm_ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    (ofQuadraticForm Q hQ).quadraticForm = Q :=
  QuadraticMap.eq_of_polarMatrix_eq (by rw [polarMatrix_quadraticForm]; rfl)

theorem ofQuadraticForm_quadraticForm (H : PositiveDefiniteIntegralQuadraticForm n) :
    ofQuadraticForm H.quadraticForm H.quadraticForm_posDef = H := by
  cases H with
  | mk A hs he hp =>
    simp only [ofQuadraticForm, mk.injEq]
    exact polarMatrix_quadraticForm _

/-- Positive-definite integral quadratic forms on `ℤⁿ` are exactly the stored polar Gram matrices. -/
def equivQuadraticForm :
    PositiveDefiniteIntegralQuadraticForm n ≃ {Q : QuadraticForm ℤ (Fin n → ℤ) // Q.PosDef} where
  toFun H := ⟨H.quadraticForm, H.quadraticForm_posDef⟩
  invFun Q := ofQuadraticForm Q.1 Q.2
  left_inv H := ofQuadraticForm_quadraticForm H
  right_inv Q := Subtype.ext (quadraticForm_ofQuadraticForm Q.1 Q.2)

end PositiveDefiniteIntegralQuadraticForm

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The quadratic form of `L` is positive definite in Mathlib's sense. -/
theorem quadraticForm_posDef (L : PositiveDefiniteIntegralLattice n) : L.quadraticForm.PosDef :=
  fun _ hx => L.quadForm_pos hx

/-- `L` and its integral quadratic form `L.toIntegralQuadraticForm` have the same Mathlib quadratic
form. -/
theorem quadraticForm_toIntegralQuadraticForm (L : PositiveDefiniteIntegralLattice n) :
    L.toIntegralQuadraticForm.quadraticForm = L.quadraticForm := by
  ext x
  exact L.toIntegralQuadraticForm_quadForm x

/-- The polar matrix of `q(x) = xᵀ F x` is `2F`. -/
theorem polarMatrix_quadraticForm (L : PositiveDefiniteIntegralLattice n) :
    L.quadraticForm.polarMatrix = (2 : ℤ) • L.pairingMatrix := by
  rw [← quadraticForm_toIntegralQuadraticForm, PositiveDefiniteIntegralQuadraticForm.polarMatrix_quadraticForm]
  rfl

/-- The polar form of an integral quadratic form is even on the standard basis: the classically
integral case, `Q(x) = xᵀ F x` with `F` integral. -/
def IsClassicallyIntegral (Q : QuadraticForm ℤ (Fin n → ℤ)) : Prop :=
  ∀ i j, Even (QuadraticMap.polar Q (Pi.single i 1) (Pi.single j 1))

theorem isClassicallyIntegral_quadraticForm (L : PositiveDefiniteIntegralLattice n) :
    IsClassicallyIntegral L.quadraticForm := fun i j =>
  ⟨L.pairingMatrix i j, by
    have := congrFun (congrFun L.polarMatrix_quadraticForm i) j
    simp only [QuadraticMap.polarMatrix, Matrix.smul_apply, smul_eq_mul] at this
    rw [this, two_mul]⟩

/-- Half the polar matrix, `F = A / 2`: integral when `Q` is classically integral. -/
def halfPolarMatrix (Q : QuadraticForm ℤ (Fin n → ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => Q.polarMatrix i j / 2

theorem two_smul_halfPolarMatrix {Q : QuadraticForm ℤ (Fin n → ℤ)}
    (hev : IsClassicallyIntegral Q) : (2 : ℤ) • halfPolarMatrix Q = Q.polarMatrix := by
  ext i j
  simp only [halfPolarMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hev i j))

theorem halfPolarMatrix_isSymm (Q : QuadraticForm ℤ (Fin n → ℤ)) : (halfPolarMatrix Q).IsSymm := by
  ext i j
  simp only [halfPolarMatrix, Matrix.transpose_apply, Matrix.of_apply]
  rw [Q.polarMatrix_isSymm.apply i j]

/-- The classically integral positive-definite form `Q`, stored through `F = A / 2` for its polar
matrix `A`. -/
def ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef)
    (hev : IsClassicallyIntegral Q) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := halfPolarMatrix Q
  form_symm := halfPolarMatrix_isSymm Q
  form_posDef := by
    refine (Matrix.posDef_map_intCast_real_iff _ (halfPolarMatrix_isSymm Q)).mpr fun x hx => ?_
    have h2 : 2 * (x ⬝ᵥ halfPolarMatrix Q *ᵥ x) = 2 * Q x := by
      rw [← Q.dotProduct_polarMatrix_mulVec_self, ← two_smul_halfPolarMatrix hev,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have := hQ x hx
    omega

theorem two_smul_pairingMatrix_ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef)
    (hev : IsClassicallyIntegral Q) :
    (2 : ℤ) • (ofQuadraticForm Q hQ hev).pairingMatrix = Q.polarMatrix :=
  two_smul_halfPolarMatrix hev

theorem quadraticForm_ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef)
    (hev : IsClassicallyIntegral Q) : (ofQuadraticForm Q hQ hev).quadraticForm = Q :=
  QuadraticMap.eq_of_polarMatrix_eq (by
    rw [polarMatrix_quadraticForm, two_smul_pairingMatrix_ofQuadraticForm])

theorem ofQuadraticForm_quadraticForm (L : PositiveDefiniteIntegralLattice n) :
    ofQuadraticForm L.quadraticForm L.quadraticForm_posDef L.isClassicallyIntegral_quadraticForm =
      L := by
  cases L with
  | mk F hs hp =>
    simp only [ofQuadraticForm, mk.injEq]
    ext i j
    have := congrFun (congrFun (polarMatrix_quadraticForm ⟨F, hs, hp⟩) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    simp only [halfPolarMatrix, Matrix.of_apply, this]
    omega

/-- Integral lattices in the stored-matrix convention are exactly the positive-definite,
classically integral quadratic forms on `ℤⁿ`. -/
def equivQuadraticForm :
    PositiveDefiniteIntegralLattice n ≃
      {Q : QuadraticForm ℤ (Fin n → ℤ) // Q.PosDef ∧ IsClassicallyIntegral Q} where
  toFun L := ⟨L.quadraticForm, L.quadraticForm_posDef, L.isClassicallyIntegral_quadraticForm⟩
  invFun Q := ofQuadraticForm Q.1 Q.2.1 Q.2.2
  left_inv L := ofQuadraticForm_quadraticForm L
  right_inv Q := Subtype.ext (quadraticForm_ofQuadraticForm Q.1 Q.2.1 Q.2.2)

/-- The two identifications agree: `L` and `L.toIntegralQuadraticForm` give the same Mathlib form. -/
theorem equivQuadraticForm_val_eq (L : PositiveDefiniteIntegralLattice n) :
    (equivQuadraticForm L).1 = (PositiveDefiniteIntegralQuadraticForm.equivQuadraticForm L.toIntegralQuadraticForm).1 :=
  (quadraticForm_toIntegralQuadraticForm L).symm

end PositiveDefiniteIntegralLattice

/-! ## Isometries -/

namespace QuadraticMap

variable {n : ℕ}

/-- The polar matrix of `x ↦ xᵀ M x` is `M + Mᵀ`. -/
theorem polarMatrix_toQuadraticMap' (M : Matrix (Fin n) (Fin n) ℤ) :
    (M.toQuadraticMap').polarMatrix = M + Mᵀ := by
  ext i j
  change QuadraticMap.polar (Matrix.toQuadraticForm' M) _ _ = _
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply']

end QuadraticMap

namespace Matrix

variable {n : ℕ}

/-- A symmetric integral matrix is determined by its quadratic form. -/
theorem eq_of_forall_dotProduct_mulVec_self {M N : Matrix (Fin n) (Fin n) ℤ} (hM : M.IsSymm)
    (hN : N.IsSymm) (h : ∀ x, x ⬝ᵥ M *ᵥ x = x ⬝ᵥ N *ᵥ x) : M = N := by
  have hQ : M.toQuadraticMap' = N.toQuadraticMap' := by
    ext x
    change Matrix.toQuadraticForm' M x = Matrix.toQuadraticForm' N x
    simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using h x
  have h2 := congrArg QuadraticMap.polarMatrix hQ
  rw [QuadraticMap.polarMatrix_toQuadraticMap', QuadraticMap.polarMatrix_toQuadraticMap', hM.eq,
    hN.eq] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.add_apply] at this
  omega

/-- `(U x)ᵀ F (U x) = xᵀ (Uᵀ F U) x`. -/
theorem dotProduct_mulVec_conj (U F : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (U *ᵥ x) ⬝ᵥ F *ᵥ (U *ᵥ x) = x ⬝ᵥ (Uᵀ * F * U) *ᵥ x := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec x Uᵀ (F * U), Matrix.dotProduct_mulVec x Uᵀ,
    Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec x F U]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

theorem quadraticForm_mulVec (L : PositiveDefiniteIntegralLattice n) (U : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    L.quadraticForm (U *ᵥ x) = x ⬝ᵥ (Uᵀ * L.pairingMatrix * U) *ᵥ x := by
  rw [← Matrix.dotProduct_mulVec_conj]
  exact L.quadForm_eq_dotProduct _

theorem transpose_mul_pairingMatrix_mul_isSymm (L : PositiveDefiniteIntegralLattice n)
    (U : Matrix (Fin n) (Fin n) ℤ) : (Uᵀ * L.pairingMatrix * U).IsSymm := by
  simp [Matrix.IsSymm, Matrix.transpose_mul, L.form_symm.eq, Matrix.mul_assoc]

/-- `Uᵀ F' U = F` exactly when `x ↦ U x` carries the form of `L` to the form of `L'`. -/
theorem transpose_mul_pairingMatrix_mul_eq_iff (L L' : PositiveDefiniteIntegralLattice n)
    (U : Matrix (Fin n) (Fin n) ℤ) :
    Uᵀ * L'.pairingMatrix * U = L.pairingMatrix ↔
      ∀ x, L'.quadraticForm (U *ᵥ x) = L.quadraticForm x := by
  constructor
  · intro h x
    rw [quadraticForm_mulVec, h]
    exact (L.quadForm_eq_dotProduct x).symm
  · intro h
    refine Matrix.eq_of_forall_dotProduct_mulVec_self (L'.transpose_mul_pairingMatrix_mul_isSymm U)
      L.form_symm fun x => ?_
    rw [← quadraticForm_mulVec, h x]
    exact L.quadForm_eq_dotProduct x

/-- An invertible integral matrix with `Uᵀ F' U = F` as a Mathlib isometry `Q_L ≃ Q_{L'}`. -/
def isometryEquivOfMatrix (L L' : PositiveDefiniteIntegralLattice n) (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U) (h : Uᵀ * L'.pairingMatrix * U = L.pairingMatrix) :
    L.quadraticForm.IsometryEquiv L'.quadraticForm where
  toLinearEquiv := Matrix.toLinearEquiv' U hU.invertible
  map_app' x := by
    simpa [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply] using
      (transpose_mul_pairingMatrix_mul_eq_iff L L' U).mp h x

theorem isUnit_toMatrix' (e : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :
    IsUnit (LinearMap.toMatrix' e.toLinearMap) := by
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp

theorem toMatrix'_transpose_mul_pairingMatrix_mul (L L' : PositiveDefiniteIntegralLattice n)
    (e : L.quadraticForm.IsometryEquiv L'.quadraticForm) :
    (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap)ᵀ * L'.pairingMatrix *
        LinearMap.toMatrix' e.toLinearEquiv.toLinearMap = L.pairingMatrix :=
  (transpose_mul_pairingMatrix_mul_eq_iff L L' _).mpr fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    exact e.map_app x

/-- Global integral isometry of two lattices is Mathlib's `QuadraticMap.Equivalent`. -/
theorem isGlobalIsometry_iff_equivalent (L L' : PositiveDefiniteIntegralLattice n) :
    L.IsGlobalIsometry L' ↔ L.quadraticForm.Equivalent L'.quadraticForm := by
  constructor
  · rintro ⟨U, hU, h⟩
    exact ⟨isometryEquivOfMatrix L L' U hU h⟩
  · rintro ⟨e⟩
    exact ⟨_, isUnit_toMatrix' e.toLinearEquiv, toMatrix'_transpose_mul_pairingMatrix_mul L L' e⟩

private theorem isometryEquiv_ext_toLinearEquiv {Q₁ Q₂ : QuadraticForm ℤ (Fin n → ℤ)}
    {e f : Q₁.IsometryEquiv Q₂} (h : e.toLinearEquiv = f.toLinearEquiv) : e = f := by
  cases e; cases f; cases h; rfl

/-- The integral isometry group `O(L)` is the group of Mathlib self-isometries of `Q_L`. -/
def isometryGroupEquiv (L : PositiveDefiniteIntegralLattice n) :
    L.IsometryGroup ≃ L.quadraticForm.IsometryEquiv L.quadraticForm where
  toFun U := isometryEquivOfMatrix L L U.1 U.2.1 U.2.2
  invFun e := ⟨LinearMap.toMatrix' e.toLinearEquiv.toLinearMap, isUnit_toMatrix' e.toLinearEquiv,
    toMatrix'_transpose_mul_pairingMatrix_mul L L e⟩
  left_inv U := Subtype.ext (by simp [isometryEquivOfMatrix])
  right_inv e := by
    refine isometryEquiv_ext_toLinearEquiv ?_
    ext x i
    change (Matrix.toLin' (LinearMap.toMatrix' (e.toLinearEquiv : (Fin n → ℤ) →ₗ[ℤ] _))) x i = e x i
    rw [Matrix.toLin'_toMatrix']
    rfl

/-- `|O(L)|` counted through Mathlib's self-isometries of `Q_L`. -/
theorem natCard_isometryGroup (L : PositiveDefiniteIntegralLattice n) :
    Nat.card L.IsometryGroup = Nat.card (L.quadraticForm.IsometryEquiv L.quadraticForm) :=
  Nat.card_congr L.isometryGroupEquiv

end PositiveDefiniteIntegralLattice

#assert_standard_axioms Matrix.posDef_map_intCast_real_iff
#assert_standard_axioms QuadraticMap.polar_eq_dotProduct_polarMatrix
#assert_standard_axioms QuadraticMap.eq_of_polarMatrix_eq
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.quadraticForm_ofQuadraticForm
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.ofQuadraticForm_quadraticForm
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.equivQuadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.quadraticForm_toIntegralQuadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.quadraticForm_ofQuadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.ofQuadraticForm_quadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.equivQuadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.equivQuadraticForm_val_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.transpose_mul_pairingMatrix_mul_eq_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.isGlobalIsometry_iff_equivalent
#assert_standard_axioms PositiveDefiniteIntegralLattice.isometryGroupEquiv
#assert_standard_axioms PositiveDefiniteIntegralLattice.natCard_isometryGroup

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

/-- Isometries of the polar-form lattices are exactly Mathlib isometries of Q.
Both directions keep the same linear equivalence. The factor two cancels over ℤ. -/
def isometryEquivPolarFormLattice (H J : PositiveDefiniteIntegralQuadraticForm n) :
    H.latticeOfPolarForm.quadraticForm.IsometryEquiv J.latticeOfPolarForm.quadraticForm ≃
      H.quadraticForm.IsometryEquiv J.quadraticForm where
  toFun e :=
    { toLinearEquiv := e.toLinearEquiv
      map_app' := fun x => by
        have h := e.map_app x
        change J.latticeOfPolarForm.quadForm (e x) = H.latticeOfPolarForm.quadForm x at h
        rw [J.latticeOfPolarForm_quadForm, H.latticeOfPolarForm_quadForm] at h
        exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)) h }
  invFun e :=
    { toLinearEquiv := e.toLinearEquiv
      map_app' := fun x => by
        change J.latticeOfPolarForm.quadForm (e x) = H.latticeOfPolarForm.quadForm x
        rw [J.latticeOfPolarForm_quadForm, H.latticeOfPolarForm_quadForm]
        change 2 * J.quadraticForm (e x) = 2 * H.quadraticForm x
        rw [e.map_app] }
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The direct full-O automorphism type is Mathlib's self-isometry type of Q. -/
def isometryGroupEquiv (H : PositiveDefiniteIntegralQuadraticForm n) :
    H.IsometryGroup ≃ H.quadraticForm.IsometryEquiv H.quadraticForm :=
  H.isometryGroupEquivLatticeOfPolarForm.trans
    (H.latticeOfPolarForm.isometryGroupEquiv.trans (isometryEquivPolarFormLattice H H))

/-- Cardinalities of the direct full-O and Mathlib automorphism types agree. -/
theorem natCard_isometryGroup (H : PositiveDefiniteIntegralQuadraticForm n) :
    Nat.card H.IsometryGroup = Nat.card (H.quadraticForm.IsometryEquiv H.quadraticForm) :=
  Nat.card_congr H.isometryGroupEquiv

/-- The direct automorphism count for a supplied Mathlib Q uses Q itself. -/
theorem natCard_isometryGroup_ofQuadraticForm
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    Nat.card (ofQuadraticForm Q hQ).IsometryGroup = Nat.card (Q.IsometryEquiv Q) := by
  rw [natCard_isometryGroup, quadraticForm_ofQuadraticForm]

end PositiveDefiniteIntegralQuadraticForm

#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.isometryEquivPolarFormLattice
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.isometryGroupEquiv
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.natCard_isometryGroup
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.natCard_isometryGroup_ofQuadraticForm
