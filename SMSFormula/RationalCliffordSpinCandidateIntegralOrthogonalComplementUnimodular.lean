import SMSFormula.RationalCliffordSpinCandidateIntegralOrthogonalComplement

/-!
# Unimodularity of the integral orthogonal complement

Choose the canonical finite basis of the free integral orthogonal complement
of a unit-norm vector.  In the product basis formed from the unit line and
this complement, the ambient Gram matrix is block diagonal.  An invertible
change of basis and the determinant product formula then show that the
restricted Gram determinant is a unit whenever the ambient determinant is a
unit.

This supplies the recursive finite-coordinate form carrier for the integral
Cartan--Dieudonne induction.  The induction itself remains separate.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral Gram bilinear form in the displayed p-adic coordinates. -/
def localPadicIntegralBilinForm
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime] :
    LinearMap.BilinForm ℤ_[p] (Fin n → ℤ_[p]) :=
  Matrix.toBilin' (L.pairingMatrix_padic p)

@[simp]
theorem localPadicIntegralBilinForm_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x y : Fin n → ℤ_[p]) :
    L.localPadicIntegralBilinForm p x y =
      x ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) y := by
  simp [localPadicIntegralBilinForm, Matrix.toBilin'_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The canonical finite basis of the free integral orthogonal complement. -/
def localPadicIntegralOrthogonalBasis
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    Module.Basis
      (Fin (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)))
      ℤ_[p] (L.localPadicIntegralOrthogonal p x) :=
  Module.finBasis ℤ_[p] (L.localPadicIntegralOrthogonal p x)

/-- Gram matrix of the restricted form in the canonical finite complement
basis. -/
def localPadicIntegralOrthogonalGramMatrix
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    Matrix
      (Fin (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)))
      (Fin (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)))
      ℤ_[p] :=
  LinearMap.BilinForm.toMatrix (L.localPadicIntegralOrthogonalBasis p x)
    ((L.localPadicIntegralBilinForm p).restrict
      (L.localPadicIntegralOrthogonal p x))

@[simp]
theorem localPadicIntegralOrthogonalGramMatrix_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (i j : Fin
      (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x))) :
    L.localPadicIntegralOrthogonalGramMatrix p x i j =
      L.localPadicIntegralBilinForm p
        (L.localPadicIntegralOrthogonalBasis p x i)
        (L.localPadicIntegralOrthogonalBasis p x j) := by
  simp [localPadicIntegralOrthogonalGramMatrix,
    LinearMap.BilinForm.toMatrix_apply]

/-- The restricted Gram matrix remains symmetric. -/
theorem localPadicIntegralOrthogonalGramMatrix_isSymm
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    (L.localPadicIntegralOrthogonalGramMatrix p x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply,
    localPadicIntegralOrthogonalGramMatrix_apply,
    localPadicIntegralBilinForm_apply]
  rw [Matrix.dotProduct_mulVec]
  have hvec :
      Matrix.vecMul
          (L.localPadicIntegralOrthogonalBasis p x j : Fin n → ℤ_[p])
          (L.pairingMatrix_padic p) =
        Matrix.mulVec (L.pairingMatrix_padic p)
          (L.localPadicIntegralOrthogonalBasis p x j : Fin n → ℤ_[p]) := by
    funext k
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [show L.pairingMatrix_padic p l k = L.pairingMatrix_padic p k l by
      simpa [pairingMatrix_padic] using
        (L.form_symm.map (Int.castRingHom ℤ_[p])).apply k l]
    ring
  rw [hvec, dotProduct_comm]

/-- The unit-norm vector itself, viewed as a basis of its integral line. -/
def localPadicIntegralUnitLineBasis
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    Module.Basis Unit ℤ_[p]
      (Submodule.span ℤ_[p] ({x} : Set (Fin n → ℤ_[p]))) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx.ne_zero
    simp [hzero, localPadicIntegralFormValue]
  exact (Module.Basis.singleton Unit ℤ_[p]).map
    (LinearEquiv.coord ℤ_[p] (Fin n → ℤ_[p]) x hx0).symm

/-- Product basis obtained by adjoining the unit line to the canonical
orthogonal-complement basis and applying the direct-sum equivalence. -/
def localPadicIntegralUnitNormSplitBasis
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    Module.Basis
      (Unit ⊕ Fin
        (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)))
      ℤ_[p] (Fin n → ℤ_[p]) :=
  ((L.localPadicIntegralUnitLineBasis p x hx).prod
      (L.localPadicIntegralOrthogonalBasis p x)).map
    (L.localPadicIntegralUnitNormDecompositionEquiv p x hx)

@[simp]
theorem localPadicIntegralUnitNormSplitBasis_apply_inl
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (i : Unit) :
    L.localPadicIntegralUnitNormSplitBasis p x hx (Sum.inl i) = x := by
  cases i
  simp [localPadicIntegralUnitNormSplitBasis,
    localPadicIntegralUnitLineBasis]

@[simp]
theorem localPadicIntegralUnitNormSplitBasis_apply_inr
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (i : Fin
      (Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x))) :
    L.localPadicIntegralUnitNormSplitBasis p x hx (Sum.inr i) =
      (L.localPadicIntegralOrthogonalBasis p x i : Fin n → ℤ_[p]) := by
  simp [localPadicIntegralUnitNormSplitBasis]

/-- The one-dimensional Gram block carried by the unit line. -/
def localPadicIntegralUnitLineGramMatrix
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) : Matrix Unit Unit ℤ_[p] :=
  fun _ _ ↦ L.localPadicIntegralFormValue p x

/-- In the split basis, the ambient Gram form is the direct block sum of the
unit line and the restricted orthogonal-complement Gram matrix. -/
theorem localPadicIntegralBilinForm_toMatrix_splitBasis
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    LinearMap.BilinForm.toMatrix
        (L.localPadicIntegralUnitNormSplitBasis p x hx)
        (L.localPadicIntegralBilinForm p) =
      Matrix.fromBlocks (L.localPadicIntegralUnitLineGramMatrix p x) 0 0
        (L.localPadicIntegralOrthogonalGramMatrix p x) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simp [LinearMap.BilinForm.toMatrix_apply,
      localPadicIntegralUnitLineGramMatrix,
      localPadicIntegralFormValue]
  · cases i
    simp only [LinearMap.BilinForm.toMatrix_apply,
      localPadicIntegralUnitNormSplitBasis_apply_inl,
      localPadicIntegralUnitNormSplitBasis_apply_inr]
    simp [Matrix.fromBlocks]
    have hz :=
      (L.localPadicIntegralOrthogonalBasis p x j).property
    rw [L.mem_localPadicIntegralOrthogonal_iff p x] at hz
    rw [Matrix.dotProduct_mulVec]
    have hvec :
        Matrix.vecMul x (L.pairingMatrix_padic p) =
          Matrix.mulVec (L.pairingMatrix_padic p) x := by
      funext k
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [show L.pairingMatrix_padic p l k = L.pairingMatrix_padic p k l by
        simpa [pairingMatrix_padic] using
          (L.form_symm.map (Int.castRingHom ℤ_[p])).apply k l]
      ring
    rw [hvec, dotProduct_comm]
    exact hz
  · cases j
    simp only [LinearMap.BilinForm.toMatrix_apply,
      localPadicIntegralUnitNormSplitBasis_apply_inl,
      localPadicIntegralUnitNormSplitBasis_apply_inr]
    simp [Matrix.fromBlocks]
    have hz :=
      (L.localPadicIntegralOrthogonalBasis p x i).property
    rw [L.mem_localPadicIntegralOrthogonal_iff p x] at hz
    exact hz
  · simp [LinearMap.BilinForm.toMatrix_apply,
      localPadicIntegralOrthogonalGramMatrix]

/-- Unimodularity descends from the ambient integral Gram matrix to the
orthogonal complement of a unit-norm vector. -/
theorem localPadicIntegralOrthogonalGramMatrix_det_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (hdet : IsUnit (L.pairingMatrix_padic p).det) :
    IsUnit (L.localPadicIntegralOrthogonalGramMatrix p x).det := by
  classical
  let m := Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)
  have hmn : m + 1 = n :=
    L.finrank_localPadicIntegralOrthogonal_add_one p x hx
  have hmn' : 1 + m = n := by omega
  let e : Unit ⊕ Fin m ≃ Fin n :=
    ((Equiv.sumCongr (finOneEquiv.symm) (Equiv.refl (Fin m))).trans
      finSumFinEquiv).trans (finCongr hmn')
  let bSplit : Module.Basis (Unit ⊕ Fin m) ℤ_[p] (Fin n → ℤ_[p]) :=
    L.localPadicIntegralUnitNormSplitBasis p x hx
  let bFin : Module.Basis (Fin n) ℤ_[p] (Fin n → ℤ_[p]) :=
    bSplit.reindex e
  let bStd := Pi.basisFun ℤ_[p] (Fin n)
  let P : Matrix (Fin n) (Fin n) ℤ_[p] := bStd.toMatrix bFin
  letI : Invertible P := Module.Basis.invertibleToMatrix bStd bFin
  have hPdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp (isUnit_of_invertible P)
  have hstd :
      (LinearMap.BilinForm.toMatrix bStd)
          (L.localPadicIntegralBilinForm p) = L.pairingMatrix_padic p := by
    dsimp only [bStd, localPadicIntegralBilinForm]
    rw [LinearMap.BilinForm.toMatrix_basisFun]
    exact LinearMap.BilinForm.toMatrix'_toBilin' _
  have hcong :
      (LinearMap.BilinForm.toMatrix bFin)
          (L.localPadicIntegralBilinForm p) =
        Pᵀ * L.pairingMatrix_padic p * P := by
    symm
    rw [← hstd]
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix bStd bFin
      (L.localPadicIntegralBilinForm p)
  have hFinDet :
      IsUnit ((LinearMap.BilinForm.toMatrix bFin)
        (L.localPadicIntegralBilinForm p)).det := by
    rw [hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hPdet.mul hdet).mul hPdet
  have hreindex :
      (LinearMap.BilinForm.toMatrix bFin)
          (L.localPadicIntegralBilinForm p) =
        Matrix.reindex e e
          ((LinearMap.BilinForm.toMatrix bSplit)
            (L.localPadicIntegralBilinForm p)) := by
    ext i j
    simp [bFin, LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply]
  have hSplitDet :
      IsUnit ((LinearMap.BilinForm.toMatrix bSplit)
        (L.localPadicIntegralBilinForm p)).det := by
    rw [hreindex, Matrix.det_reindex_self] at hFinDet
    exact hFinDet
  have hblock :=
    L.localPadicIntegralBilinForm_toMatrix_splitBasis p x hx
  change
    (LinearMap.BilinForm.toMatrix bSplit)
        (L.localPadicIntegralBilinForm p) =
      Matrix.fromBlocks (L.localPadicIntegralUnitLineGramMatrix p x) 0 0
        (L.localPadicIntegralOrthogonalGramMatrix p x) at hblock
  rw [hblock, Matrix.det_fromBlocks_zero₂₁] at hSplitDet
  have hproduct :
      IsUnit (L.localPadicIntegralFormValue p x *
        (L.localPadicIntegralOrthogonalGramMatrix p x).det) := by
    simpa [localPadicIntegralUnitLineGramMatrix] using hSplitDet
  exact (IsUnit.mul_iff.mp hproduct).2

/-- Finite-coordinate carrier for an integral symmetric unimodular form over
`Z_p`.  This is the datum on which the reflection induction recurses. -/
structure LocalPadicIntegralUnimodularForm (p : ℕ) [Fact p.Prime] where
  rank : ℕ
  pairingMatrix : Matrix (Fin rank) (Fin rank) ℤ_[p]
  pairingMatrix_isSymm : pairingMatrix.IsSymm
  pairingMatrix_det_isUnit : IsUnit pairingMatrix.det

/-- The orthogonal complement, expressed in its canonical finite basis, is a
rank-one-smaller integral symmetric unimodular form. -/
def localPadicIntegralOrthogonalUnimodularForm
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (hdet : IsUnit (L.pairingMatrix_padic p).det) :
    LocalPadicIntegralUnimodularForm p where
  rank := Module.finrank ℤ_[p] (L.localPadicIntegralOrthogonal p x)
  pairingMatrix := L.localPadicIntegralOrthogonalGramMatrix p x
  pairingMatrix_isSymm :=
    L.localPadicIntegralOrthogonalGramMatrix_isSymm p x
  pairingMatrix_det_isUnit :=
    L.localPadicIntegralOrthogonalGramMatrix_det_isUnit p x hx hdet

@[simp]
theorem localPadicIntegralOrthogonalUnimodularForm_rank_add_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p])
    (hx : IsUnit (L.localPadicIntegralFormValue p x))
    (hdet : IsUnit (L.pairingMatrix_padic p).det) :
    (L.localPadicIntegralOrthogonalUnimodularForm p x hx hdet).rank + 1 = n :=
  L.finrank_localPadicIntegralOrthogonal_add_one p x hx

end PositiveDefiniteIntegralLattice
