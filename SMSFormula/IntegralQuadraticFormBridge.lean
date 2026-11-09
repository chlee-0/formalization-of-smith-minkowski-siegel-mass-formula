import SMSFormula.IntegralQuadraticForm
import SMSFormula.Genus

/-!
# Norm and polarization constructions for based integral forms

An integral bilinear lattice with pairing matrix G gives its norm `xᵀGx`.
`PositiveDefiniteIntegralLattice.toIntegralQuadraticForm` preserves that norm
and stores its polar matrix 2G.

For an integer-valued quadratic form Q with polar matrix A,
`PositiveDefiniteIntegralQuadraticForm.latticeOfPolarForm` instead constructs
the integral bilinear lattice with pairing `polar(Q)` and matrix A. Its norm
is exactly 2Q, and its polar matrix is 2A.

These are distinct legitimate constructions on the based module `ℤ^n`.
They are not inverse equivalences, and the second is not an implicit coercion.
Local-density comparisons, including the dyadic comparison, are proved in
separate polarization/scaling compatibility modules.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- An old integral quadratic matrix `F` as the same half-integral quadratic
form, with integral polar Gram matrix `2F`. -/
def toIntegralQuadraticForm : PositiveDefiniteIntegralQuadraticForm n where
  polarGramMatrix := (2 : ℤ) • L.pairingMatrix
  polarGram_symm := by
    ext i j
    change 2 * L.pairingMatrix j i = 2 * L.pairingMatrix i j
    rw [(L.form_symm.apply j i).symm]
  polarGram_even_diag := by
    intro i
    refine ⟨L.pairingMatrix i i, ?_⟩
    simp [two_mul]
  polarGram_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply,
        Matrix.smul_apply, star_trivial, smul_eq_mul, Int.cast_mul,
        Int.cast_ofNat]
      change (2 : ℝ) * (L.pairingMatrix j i : ℝ) =
        2 * (L.pairingMatrix i j : ℝ)
      rw [(L.form_symm.apply j i).symm]
    · intro x hx
      have h := L.form_posDef.dotProduct_mulVec_pos hx
      have hmap :
          ((2 : ℤ) • L.pairingMatrix).map (Int.cast : ℤ → ℝ) =
            (2 : ℝ) • L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
          Int.cast_mul, Int.cast_ofNat]
      rw [hmap, Matrix.smul_mulVec, dotProduct_smul]
      exact mul_pos (by norm_num) h

/-- The rational half-integral matrix of `L.toIntegralQuadraticForm` is
the pairing matrix of `L` cast to `ℚ`. -/
theorem toIntegralQuadraticForm_quadraticMatrix :
    L.toIntegralQuadraticForm.quadraticMatrix =
      L.pairingMatrix.map (Int.cast : ℤ → ℚ) := by
  ext i j
  simp only [toIntegralQuadraticForm,
    PositiveDefiniteIntegralQuadraticForm.quadraticMatrix, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]
  norm_num
  ring

/-- Converting an old lattice to the integral-quadratic-form convention preserves the
integral quadratic form exactly. -/
theorem toIntegralQuadraticForm_quadForm (x : Fin n → ℤ) :
    L.toIntegralQuadraticForm.quadForm x = L.quadForm x := by
  have h := L.toIntegralQuadraticForm.two_mul_quadForm_eq_polarGram x
  have hright :
      dotProduct x
          (((2 : ℤ) • L.pairingMatrix).mulVec x) =
        2 * L.quadForm x := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp [L.quadForm_eq_dotProduct]
  rw [show L.toIntegralQuadraticForm.polarGramMatrix =
      (2 : ℤ) • L.pairingMatrix by rfl, hright] at h
  omega

/-- Compatibility of the two matrix presentations after casting to `ℚ`. -/
theorem toIntegralQuadraticForm_quadForm_cast_eq_pairingMatrixQ
    (x : Fin n → ℤ) :
    (L.toIntegralQuadraticForm.quadForm x : ℚ) =
      dotProduct (fun i ↦ (x i : ℚ))
        ((L.pairingMatrix.map (Int.cast : ℤ → ℚ)).mulVec
          (fun i ↦ (x i : ℚ))) := by
  rw [L.toIntegralQuadraticForm_quadForm]
  have h := congrArg (fun z : ℤ ↦ (z : ℚ)) (L.quadForm_eq_dotProduct x)
  simpa [dotProduct, Matrix.mulVec] using h

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## The lattice of the polar form -/

/-- The integral bilinear lattice whose pairing is the polar form of H.
Its pairing matrix is A and its norm is exactly `2Q_H`. -/
def latticeOfPolarForm : PositiveDefiniteIntegralLattice n where
  pairingMatrix := H.polarGramMatrix
  form_symm := H.polarGram_symm
  form_posDef := H.polarGram_posDef

/-- The norm of the lattice of the polar form is exactly twice Q. -/
theorem latticeOfPolarForm_quadForm (x : Fin n → ℤ) :
    H.latticeOfPolarForm.quadForm x = 2 * H.quadForm x := by
  rw [H.latticeOfPolarForm.quadForm_eq_dotProduct]
  exact (H.two_mul_quadForm_eq_polarGram x).symm

/-- The polar Gram matrix of the constructed lattice is `2A`. -/
theorem latticeOfPolarForm_polarGramMatrix :
    H.latticeOfPolarForm.polarGramMatrix =
      (2 : ℤ) • H.polarGramMatrix := by
  exact H.latticeOfPolarForm.polarGramMatrix_eq_two_smul_pairingMatrix

/-- An integral matrix preserves the integral quadratic form when it is a unit and
preserves the stored polar Gram matrix `A`. -/
def IsIsometry (U : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsUnit U ∧ Uᵀ * H.polarGramMatrix * U = H.polarGramMatrix

/-- The direct ordinary integral automorphism type of an integral quadratic form. -/
def IsometryGroup : Type :=
  {U : Matrix (Fin n) (Fin n) ℤ // H.IsIsometry U}

/-- A direct proper isometry additionally has determinant one. -/
def IsProperIsometry (U : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  H.IsIsometry U ∧ U.det = 1

/-- The direct proper integral automorphism type. -/
def ProperIsometryGroup : Type :=
  {U : Matrix (Fin n) (Fin n) ℤ // H.IsProperIsometry U}

/-- The direct isometry equation is definitionally the integral model equation. -/
theorem isIsometry_iff_latticeOfPolarForm_isIsometry
    (U : Matrix (Fin n) (Fin n) ℤ) :
    H.IsIsometry U ↔ H.latticeOfPolarForm.IsIsometry U := by
  rfl

/-- The direct proper-isometry equation is definitionally the integral model
equation. -/
theorem isProperIsometry_iff_latticeOfPolarForm_isProperIsometry
    (U : Matrix (Fin n) (Fin n) ℤ) :
    H.IsProperIsometry U ↔
      H.latticeOfPolarForm.IsProperIsometry U := by
  rfl

/-- Literal carrier equivalence between the direct and integral model ordinary
automorphism types. -/
def isometryGroupEquivLatticeOfPolarForm :
    H.IsometryGroup ≃ H.latticeOfPolarForm.IsometryGroup where
  toFun U := ⟨U.1, H.isIsometry_iff_latticeOfPolarForm_isIsometry U.1 |>.mp U.2⟩
  invFun U := ⟨U.1, H.isIsometry_iff_latticeOfPolarForm_isIsometry U.1 |>.mpr U.2⟩
  left_inv U := by rfl
  right_inv U := by rfl

/-- Literal carrier equivalence between the direct and integral model proper
automorphism types. -/
def properIsometryGroupEquivLatticeOfPolarForm :
    H.ProperIsometryGroup ≃ H.latticeOfPolarForm.ProperIsometryGroup where
  toFun U :=
    ⟨U.1, H.isProperIsometry_iff_latticeOfPolarForm_isProperIsometry U.1 |>.mp U.2⟩
  invFun U :=
    ⟨U.1, H.isProperIsometry_iff_latticeOfPolarForm_isProperIsometry U.1 |>.mpr U.2⟩
  left_inv U := by rfl
  right_inv U := by rfl

/-! ## Direct global isometry and integral model transport -/

/-- Global integral isometry in the integral-quadratic-form convention, expressed with
the polar Gram matrices. -/
def IsGlobalIsometry (H' : PositiveDefiniteIntegralQuadraticForm n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ,
    IsUnit U ∧ Uᵀ * H'.polarGramMatrix * U = H.polarGramMatrix

/-- Direct global isometry is exactly global isometry of the scaled integral models. -/
theorem isGlobalIsometry_iff_latticeOfPolarForm
    (H' : PositiveDefiniteIntegralQuadraticForm n) :
    H.IsGlobalIsometry H' ↔
      H.latticeOfPolarForm.IsGlobalIsometry H'.latticeOfPolarForm := by
  rfl

/-! ## Direct local isometry and genus relation -/

/-- The polar Gram matrix over `ℤ_p`. -/
def polarGramMatrix_padic (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  H.polarGramMatrix.map (Int.cast : ℤ → ℤ_[p])

/-- The polar Gram matrix over `ℝ`. -/
def polarGramMatrix_real : Matrix (Fin n) (Fin n) ℝ :=
  H.polarGramMatrix.map (Int.cast : ℤ → ℝ)

/-- Direct finite-prime local isometry, using the integral polar Gram matrix
`A`, not the integral model's polar matrix `2A`. -/
def IsLocallyIsometricAt (H' : PositiveDefiniteIntegralQuadraticForm n)
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ_[p],
    IsUnit U ∧
      Uᵀ * H'.polarGramMatrix_padic p * U = H.polarGramMatrix_padic p

/-- Direct real local isometry using `A`. -/
def IsLocallyIsometricAtInfinity (H' : PositiveDefiniteIntegralQuadraticForm n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℝ,
    IsUnit U ∧
      Uᵀ * H'.polarGramMatrix_real * U = H.polarGramMatrix_real

/-- The intrinsic same-genus relation for integral quadratic forms. -/
def IsSameGenus (H' : PositiveDefiniteIntegralQuadraticForm n) : Prop :=
  (∀ (p : ℕ) [Fact (Nat.Prime p)], H.IsLocallyIsometricAt H' p) ∧
    H.IsLocallyIsometricAtInfinity H'

/-- Direct finite-prime local isometry is exactly local isometry of the
scaled integral integral models because both use the same stored matrix `A`. -/
theorem isLocallyIsometricAt_iff_latticeOfPolarForm
    (H' : PositiveDefiniteIntegralQuadraticForm n) (p : ℕ) [Fact (Nat.Prime p)] :
    H.IsLocallyIsometricAt H' p ↔
      H.latticeOfPolarForm.IsLocallyIsometricAt
        H'.latticeOfPolarForm p := by
  rfl

/-- Direct real local isometry is exactly real local isometry of the scaled
integral integral models. -/
theorem isLocallyIsometricAtInfinity_iff_latticeOfPolarForm
    (H' : PositiveDefiniteIntegralQuadraticForm n) :
    H.IsLocallyIsometricAtInfinity H' ↔
      H.latticeOfPolarForm.IsLocallyIsometricAtInfinity
        H'.latticeOfPolarForm := by
  rfl

/-- The intrinsic same-genus relation is transported exactly to the integral model
same-genus relation. -/
theorem isSameGenus_iff_latticeOfPolarForm
    (H' : PositiveDefiniteIntegralQuadraticForm n) :
    H.IsSameGenus H' ↔
      H.latticeOfPolarForm.IsSameGenus H'.latticeOfPolarForm := by
  rfl

end PositiveDefiniteIntegralQuadraticForm

end
