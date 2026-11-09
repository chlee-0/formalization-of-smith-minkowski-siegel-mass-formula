import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionAlignment

/-!
# Orthogonal complements of recursive integral p-adic forms

Split a unit-norm line from a finite-coordinate symmetric unimodular form
over `Z_p`.  The restricted Gram matrix is again symmetric and unimodular,
and therefore supplies the rank-one-smaller carrier used by the integral
unit-reflection induction.

This is the abstract-carrier analogue of the lattice-specific complement
construction.  Restriction and reflection-word lifting are handled
separately.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

/-- The Gram bilinear form of a recursive integral form carrier. -/
def LocalPadicIntegralUnimodularForm.bilinForm
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) :
    LinearMap.BilinForm ℤ_[p] (Fin U.rank → ℤ_[p]) :=
  Matrix.toBilin' U.pairingMatrix

@[simp]
theorem LocalPadicIntegralUnimodularForm.bilinForm_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p]) :
    U.bilinForm x y = x ⬝ᵥ Matrix.mulVec U.pairingMatrix y := by
  simp [LocalPadicIntegralUnimodularForm.bilinForm,
    Matrix.toBilin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_assoc]

/-- Right Gram pairing with a vector of a recursive integral form. -/
def LocalPadicIntegralUnimodularForm.pairingRight
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    (Fin U.rank → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] :=
  (U.bilinForm.flip : LinearMap.BilinForm ℤ_[p]
    (Fin U.rank → ℤ_[p])) x

@[simp]
theorem LocalPadicIntegralUnimodularForm.pairingRight_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p]) :
    U.pairingRight x y = y ⬝ᵥ Matrix.mulVec U.pairingMatrix x := by
  simp [LocalPadicIntegralUnimodularForm.pairingRight,
    LocalPadicIntegralUnimodularForm.bilinForm_apply]

/-- Integral Gram-orthogonal complement of a fixed vector. -/
def LocalPadicIntegralUnimodularForm.orthogonal
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    Submodule ℤ_[p] (Fin U.rank → ℤ_[p]) :=
  LinearMap.ker (U.pairingRight x)

theorem LocalPadicIntegralUnimodularForm.mem_orthogonal_iff
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p]) :
    y ∈ U.orthogonal x ↔
      y ⬝ᵥ Matrix.mulVec U.pairingMatrix x = 0 := by
  simp [LocalPadicIntegralUnimodularForm.orthogonal,
    LocalPadicIntegralUnimodularForm.pairingRight_apply]

/-- Normalize the Gram functional by the inverse of the unit norm. -/
def LocalPadicIntegralUnimodularForm.unitNormFunctional
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    (Fin U.rank → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p] :=
  ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • U.pairingRight x

theorem LocalPadicIntegralUnimodularForm.unitNormFunctional_apply_self
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    U.unitNormFunctional x hx x = 1 := by
  have hu : (hx.unit : ℤ_[p]) = U.quadraticForm x := IsUnit.unit_spec hx
  change ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * U.quadraticForm x = 1
  calc
    ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * U.quadraticForm x =
        ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (hx.unit : ℤ_[p]) := by rw [hu]
    _ = 1 := by simp

theorem LocalPadicIntegralUnimodularForm.ker_unitNormFunctional
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    LinearMap.ker (U.unitNormFunctional x hx) = U.orthogonal x := by
  ext y
  change
    ((hx.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * U.pairingRight x y = 0 ↔
      U.pairingRight x y = 0
  simp

/-- A unit-norm line is complementary to its Gram-orthogonal kernel. -/
theorem LocalPadicIntegralUnimodularForm.isCompl_span_orthogonal
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    IsCompl
      (Submodule.span ℤ_[p] ({x} : Set (Fin U.rank → ℤ_[p])))
      (U.orthogonal x) := by
  rw [← U.ker_unitNormFunctional x hx]
  exact isCompl_span_singleton_ker_of_apply_eq_one x
    (U.unitNormFunctional x hx) (U.unitNormFunctional_apply_self x hx)

/-- Product coordinates supplied by splitting off a unit-norm line. -/
def LocalPadicIntegralUnimodularForm.decompositionEquiv
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    (Submodule.span ℤ_[p] ({x} : Set (Fin U.rank → ℤ_[p])) ×
        U.orthogonal x) ≃ₗ[ℤ_[p]] (Fin U.rank → ℤ_[p]) :=
  Submodule.prodEquivOfIsCompl _ _ (U.isCompl_span_orthogonal x hx)

@[simp]
theorem LocalPadicIntegralUnimodularForm.decompositionEquiv_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x))
    (y : Submodule.span ℤ_[p] ({x} : Set (Fin U.rank → ℤ_[p])))
    (z : U.orthogonal x) :
    U.decompositionEquiv x hx (y, z) = y + z :=
  rfl

theorem LocalPadicIntegralUnimodularForm.orthogonal_moduleFinite
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    Module.Finite ℤ_[p] (U.orthogonal x) := by
  infer_instance

theorem LocalPadicIntegralUnimodularForm.orthogonal_moduleFree
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    Module.Free ℤ_[p] (U.orthogonal x) := by
  infer_instance

/-- Splitting a unit line lowers finite rank by exactly one. -/
theorem LocalPadicIntegralUnimodularForm.finrank_orthogonal_add_one
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    Module.finrank ℤ_[p] (U.orthogonal x) + 1 = U.rank := by
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx.ne_zero
    simp [hzero]
  let line := Submodule.span ℤ_[p]
    ({x} : Set (Fin U.rank → ℤ_[p]))
  have hline : Module.finrank ℤ_[p] line = 1 := by
    have h :=
      (LinearEquiv.coord ℤ_[p] (Fin U.rank → ℤ_[p]) x hx0).finrank_eq
    simpa [line] using h
  have hfin := (U.decompositionEquiv x hx).finrank_eq
  rw [Module.finrank_prod] at hfin
  simpa [line, hline, add_comm] using hfin

/-- Canonical finite basis of the free orthogonal complement. -/
def LocalPadicIntegralUnimodularForm.orthogonalBasis
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    Module.Basis (Fin (Module.finrank ℤ_[p] (U.orthogonal x)))
      ℤ_[p] (U.orthogonal x) :=
  Module.finBasis ℤ_[p] (U.orthogonal x)

/-- Restricted Gram matrix in the canonical complement basis. -/
def LocalPadicIntegralUnimodularForm.orthogonalGramMatrix
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    Matrix (Fin (Module.finrank ℤ_[p] (U.orthogonal x)))
      (Fin (Module.finrank ℤ_[p] (U.orthogonal x))) ℤ_[p] :=
  LinearMap.BilinForm.toMatrix (U.orthogonalBasis x)
    (U.bilinForm.restrict (U.orthogonal x))

@[simp]
theorem LocalPadicIntegralUnimodularForm.orthogonalGramMatrix_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (i j : Fin (Module.finrank ℤ_[p] (U.orthogonal x))) :
    U.orthogonalGramMatrix x i j =
      U.bilinForm (U.orthogonalBasis x i) (U.orthogonalBasis x j) := by
  simp [LocalPadicIntegralUnimodularForm.orthogonalGramMatrix,
    LinearMap.BilinForm.toMatrix_apply]

theorem LocalPadicIntegralUnimodularForm.orthogonalGramMatrix_isSymm
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    (U.orthogonalGramMatrix x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, U.orthogonalGramMatrix_apply,
    U.bilinForm_apply]
  rw [Matrix.dotProduct_mulVec]
  have hvec :
      Matrix.vecMul (U.orthogonalBasis x j : Fin U.rank → ℤ_[p])
          U.pairingMatrix =
        Matrix.mulVec U.pairingMatrix
          (U.orthogonalBasis x j : Fin U.rank → ℤ_[p]) := by
    funext k
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [show U.pairingMatrix l k = U.pairingMatrix k l by
      exact U.pairingMatrix_isSymm.apply k l]
    ring
  rw [hvec, dotProduct_comm]

/-- The unit vector as a basis of its line. -/
def LocalPadicIntegralUnimodularForm.unitLineBasis
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    Module.Basis Unit ℤ_[p]
      (Submodule.span ℤ_[p] ({x} : Set (Fin U.rank → ℤ_[p]))) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx.ne_zero
    simp [hzero]
  exact (Module.Basis.singleton Unit ℤ_[p]).map
    (LinearEquiv.coord ℤ_[p] (Fin U.rank → ℤ_[p]) x hx0).symm

/-- Product basis obtained by adjoining the unit line to the complement. -/
def LocalPadicIntegralUnimodularForm.splitBasis
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    Module.Basis
      (Unit ⊕ Fin (Module.finrank ℤ_[p] (U.orthogonal x)))
      ℤ_[p] (Fin U.rank → ℤ_[p]) :=
  ((U.unitLineBasis x hx).prod (U.orthogonalBasis x)).map
    (U.decompositionEquiv x hx)

@[simp]
theorem LocalPadicIntegralUnimodularForm.splitBasis_apply_inl
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) (i : Unit) :
    U.splitBasis x hx (Sum.inl i) = x := by
  cases i
  simp [LocalPadicIntegralUnimodularForm.splitBasis,
    LocalPadicIntegralUnimodularForm.unitLineBasis]

@[simp]
theorem LocalPadicIntegralUnimodularForm.splitBasis_apply_inr
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x))
    (i : Fin (Module.finrank ℤ_[p] (U.orthogonal x))) :
    U.splitBasis x hx (Sum.inr i) =
      (U.orthogonalBasis x i : Fin U.rank → ℤ_[p]) := by
  simp [LocalPadicIntegralUnimodularForm.splitBasis]

def LocalPadicIntegralUnimodularForm.unitLineGramMatrix
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) : Matrix Unit Unit ℤ_[p] :=
  fun _ _ ↦ U.quadraticForm x

/-- The Gram matrix in the split basis is block diagonal. -/
theorem LocalPadicIntegralUnimodularForm.bilinForm_toMatrix_splitBasis
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    LinearMap.BilinForm.toMatrix (U.splitBasis x hx) U.bilinForm =
      Matrix.fromBlocks (U.unitLineGramMatrix x) 0 0
        (U.orthogonalGramMatrix x) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simp [LinearMap.BilinForm.toMatrix_apply,
      LocalPadicIntegralUnimodularForm.unitLineGramMatrix]
  · cases i
    simp only [LinearMap.BilinForm.toMatrix_apply,
      U.splitBasis_apply_inl, U.splitBasis_apply_inr]
    simp [Matrix.fromBlocks]
    have hz := (U.orthogonalBasis x j).property
    rw [U.mem_orthogonal_iff x] at hz
    rw [Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul x U.pairingMatrix =
        Matrix.mulVec U.pairingMatrix x := by
      funext k
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [show U.pairingMatrix l k = U.pairingMatrix k l by
        exact U.pairingMatrix_isSymm.apply k l]
      ring
    rw [hvec, dotProduct_comm]
    exact hz
  · cases j
    simp only [LinearMap.BilinForm.toMatrix_apply,
      U.splitBasis_apply_inl, U.splitBasis_apply_inr]
    simp [Matrix.fromBlocks]
    have hz := (U.orthogonalBasis x i).property
    rw [U.mem_orthogonal_iff x] at hz
    exact hz
  · simp [LinearMap.BilinForm.toMatrix_apply,
      LocalPadicIntegralUnimodularForm.orthogonalGramMatrix]

/-- Unimodularity descends to the unit-vector orthogonal complement. -/
theorem LocalPadicIntegralUnimodularForm.orthogonalGramMatrix_det_isUnit
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    IsUnit (U.orthogonalGramMatrix x).det := by
  classical
  let m := Module.finrank ℤ_[p] (U.orthogonal x)
  have hmn : m + 1 = U.rank := U.finrank_orthogonal_add_one x hx
  have hmn' : 1 + m = U.rank := by omega
  let e : Unit ⊕ Fin m ≃ Fin U.rank :=
    ((Equiv.sumCongr (finOneEquiv.symm) (Equiv.refl (Fin m))).trans
      finSumFinEquiv).trans (finCongr hmn')
  let bSplit : Module.Basis (Unit ⊕ Fin m) ℤ_[p]
      (Fin U.rank → ℤ_[p]) := U.splitBasis x hx
  let bFin : Module.Basis (Fin U.rank) ℤ_[p]
      (Fin U.rank → ℤ_[p]) := bSplit.reindex e
  let bStd := Pi.basisFun ℤ_[p] (Fin U.rank)
  let P : Matrix (Fin U.rank) (Fin U.rank) ℤ_[p] := bStd.toMatrix bFin
  letI : Invertible P := Module.Basis.invertibleToMatrix bStd bFin
  have hPdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp (isUnit_of_invertible P)
  have hstd :
      (LinearMap.BilinForm.toMatrix bStd) U.bilinForm = U.pairingMatrix := by
    dsimp only [bStd, LocalPadicIntegralUnimodularForm.bilinForm]
    rw [LinearMap.BilinForm.toMatrix_basisFun]
    exact LinearMap.BilinForm.toMatrix'_toBilin' _
  have hcong :
      (LinearMap.BilinForm.toMatrix bFin) U.bilinForm =
        Pᵀ * U.pairingMatrix * P := by
    symm
    rw [← hstd]
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix bStd bFin U.bilinForm
  have hFinDet :
      IsUnit ((LinearMap.BilinForm.toMatrix bFin) U.bilinForm).det := by
    rw [hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hPdet.mul U.pairingMatrix_det_isUnit).mul hPdet
  have hreindex :
      (LinearMap.BilinForm.toMatrix bFin) U.bilinForm =
        Matrix.reindex e e
          ((LinearMap.BilinForm.toMatrix bSplit) U.bilinForm) := by
    ext i j
    simp [bFin, LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply]
  have hSplitDet :
      IsUnit ((LinearMap.BilinForm.toMatrix bSplit) U.bilinForm).det := by
    rw [hreindex, Matrix.det_reindex_self] at hFinDet
    exact hFinDet
  have hblock := U.bilinForm_toMatrix_splitBasis x hx
  change
    (LinearMap.BilinForm.toMatrix bSplit) U.bilinForm =
      Matrix.fromBlocks (U.unitLineGramMatrix x) 0 0
        (U.orthogonalGramMatrix x) at hblock
  rw [hblock, Matrix.det_fromBlocks_zero₂₁] at hSplitDet
  have hproduct :
      IsUnit (U.quadraticForm x * (U.orthogonalGramMatrix x).det) := by
    simpa [LocalPadicIntegralUnimodularForm.unitLineGramMatrix] using hSplitDet
  exact (IsUnit.mul_iff.mp hproduct).2

/-- Rank-one-smaller symmetric unimodular form carried by the complement. -/
def LocalPadicIntegralUnimodularForm.orthogonalUnimodularForm
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    LocalPadicIntegralUnimodularForm p where
  rank := Module.finrank ℤ_[p] (U.orthogonal x)
  pairingMatrix := U.orthogonalGramMatrix x
  pairingMatrix_isSymm := U.orthogonalGramMatrix_isSymm x
  pairingMatrix_det_isUnit := U.orthogonalGramMatrix_det_isUnit x hx

@[simp]
theorem LocalPadicIntegralUnimodularForm.orthogonalUnimodularForm_rank_add_one
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    (U.orthogonalUnimodularForm x hx).rank + 1 = U.rank :=
  U.finrank_orthogonal_add_one x hx

/-- The recursive complement quadratic form is the ambient form restricted
through the canonical complement basis. -/
theorem LocalPadicIntegralUnimodularForm.orthogonalUnimodularForm_quadraticForm_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (z : Fin (U.orthogonalUnimodularForm x hx).rank → ℤ_[p]) :
    (U.orthogonalUnimodularForm x hx).quadraticForm z =
      U.quadraticForm
        ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) := by
  rw [(U.orthogonalUnimodularForm x hx).quadraticForm_apply]
  change z ⬝ᵥ Matrix.mulVec (U.orthogonalGramMatrix x) z =
    U.quadraticForm
      ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x)
  change z ⬝ᵥ Matrix.mulVec
      (LinearMap.BilinForm.toMatrix (U.orthogonalBasis x)
        (U.bilinForm.restrict (U.orthogonal x))) z = _
  calc
    z ⬝ᵥ Matrix.mulVec
        (LinearMap.BilinForm.toMatrix (U.orthogonalBasis x)
          (U.bilinForm.restrict (U.orthogonal x))) z =
      (U.bilinForm.restrict (U.orthogonal x))
        ((U.orthogonalBasis x).equivFun.symm z)
        ((U.orthogonalBasis x).equivFun.symm z) :=
          LinearMap.BilinForm.dotProduct_toMatrix_mulVec
            (U.orthogonalBasis x) (U.bilinForm.restrict (U.orthogonal x)) z z
    _ = U.quadraticForm
        ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) := by
      change U.bilinForm
          ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x)
          ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x) =
        U.quadraticForm
          ((U.orthogonalBasis x).equivFun.symm z : U.orthogonal x)
      rw [U.bilinForm_apply, U.quadraticForm_apply]

/-- Polarization of the displayed quadratic form is twice its symmetric
Gram bilinear form. -/
theorem LocalPadicIntegralUnimodularForm.polar_eq_two_mul_bilinForm
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p]) :
    QuadraticMap.polar U.quadraticForm x y = 2 * U.bilinForm x y := by
  rw [QuadraticMap.polar]
  simp only [U.quadraticForm_apply, U.bilinForm_apply,
    Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  have hsym : x ⬝ᵥ U.pairingMatrix *ᵥ y =
      y ⬝ᵥ U.pairingMatrix *ᵥ x := by
    rw [Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul x U.pairingMatrix =
        Matrix.mulVec U.pairingMatrix x := by
      funext i
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [show U.pairingMatrix j i = U.pairingMatrix i j by
        exact U.pairingMatrix_isSymm.apply i j]
      ring
    rw [hvec, dotProduct_comm]
  rw [hsym]
  ring

/-- Integral quadratic isometries preserve polarization. -/
theorem LocalPadicIntegralUnimodularForm.polar_map_isometry
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (x y : Fin U.rank → ℤ_[p]) :
    QuadraticMap.polar U.quadraticForm (g x) (g y) =
      QuadraticMap.polar U.quadraticForm x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar]
  have hsum : g (x + y) = g x + g y := g.toLinearEquiv.map_add x y
  rw [← hsum]
  simp only [g.map_app]

/-- At an odd prime, an integral quadratic isometry preserves the Gram
bilinear form. -/
theorem LocalPadicIntegralUnimodularForm.bilinForm_map_isometry
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (x y : Fin U.rank → ℤ_[p]) :
    U.bilinForm (g x) (g y) = U.bilinForm x y := by
  have hpolar := U.polar_map_isometry g x y
  rw [U.polar_eq_two_mul_bilinForm,
    U.polar_eq_two_mul_bilinForm] at hpolar
  exact (two_isUnit_padicInt_of_ne_two p hpodd).mul_left_cancel hpolar

/-- A fixed-vector quadratic isometry preserves right pairing with that
vector. -/
theorem LocalPadicIntegralUnimodularForm.pairingRight_map_isometry_fixing
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x) :
    U.pairingRight x (g y) = U.pairingRight x y := by
  change U.bilinForm (g y) x = U.bilinForm y x
  calc
    U.bilinForm (g y) x = U.bilinForm (g y) (g x) := by rw [hfix]
    _ = U.bilinForm y x := U.bilinForm_map_isometry hpodd g y x

/-- A fixed-vector integral quadratic isometry restricts to the orthogonal
complement. -/
def LocalPadicIntegralUnimodularForm.orthogonalRestriction
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p])
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x) :
    U.orthogonal x ≃ₗ[ℤ_[p]] U.orthogonal x where
  toFun y := ⟨g y, by
    change U.pairingRight x (g y) = 0
    rw [U.pairingRight_map_isometry_fixing hpodd x y g hfix]
    exact y.property⟩
  invFun y := ⟨g.symm y, by
    change U.pairingRight x (g.symm y) = 0
    have hpair := U.pairingRight_map_isometry_fixing hpodd x
      (g.symm y) g hfix
    have happly : g (g.symm (y : Fin U.rank → ℤ_[p])) = y :=
      g.apply_symm_apply y
    rw [happly] at hpair
    rw [← hpair]
    exact y.property⟩
  left_inv y := Subtype.ext (g.symm_apply_apply y)
  right_inv y := Subtype.ext (g.apply_symm_apply y)
  map_add' y z := Subtype.ext (g.toLinearEquiv.map_add y z)
  map_smul' a y := Subtype.ext (g.toLinearEquiv.map_smul a y)

@[simp]
theorem LocalPadicIntegralUnimodularForm.coe_orthogonalRestriction
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p])
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x) (y : U.orthogonal x) :
    (U.orthogonalRestriction hpodd x g hfix y : Fin U.rank → ℤ_[p]) =
      g y :=
  rfl

/-- The restricted complement automorphism preserves the ambient quadratic
value. -/
theorem LocalPadicIntegralUnimodularForm.quadraticForm_orthogonalRestriction
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p])
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x) (y : U.orthogonal x) :
    U.quadraticForm (U.orthogonalRestriction hpodd x g hfix y) =
      U.quadraticForm y :=
  g.map_app y

/-- The restricted fixed-vector isometry in the finite coordinates of the
recursive complement carrier. -/
def LocalPadicIntegralUnimodularForm.orthogonalCoordinateRestriction
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x : Fin U.rank → ℤ_[p]) (hx : IsUnit (U.quadraticForm x))
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hfix : g x = x) :
    (U.orthogonalUnimodularForm x hx).quadraticForm.IsometryEquiv
      (U.orthogonalUnimodularForm x hx).quadraticForm where
  toLinearEquiv :=
    (U.orthogonalBasis x).equivFun.symm.trans
      ((U.orthogonalRestriction hpodd x g hfix).trans
        (U.orthogonalBasis x).equivFun)
  map_app' z := by
    have hcoord :
        (U.orthogonalBasis x).equivFun.symm
            (((U.orthogonalBasis x).equivFun.symm.trans
              ((U.orthogonalRestriction hpodd x g hfix).trans
                (U.orthogonalBasis x).equivFun)).toFun z) =
          U.orthogonalRestriction hpodd x g hfix
            ((U.orthogonalBasis x).equivFun.symm z) := by
      simp
    rw [U.orthogonalUnimodularForm_quadraticForm_apply,
      U.orthogonalUnimodularForm_quadraticForm_apply]
    exact (congrArg (fun vector : U.orthogonal x ↦ U.quadraticForm vector.1) hcoord).trans
      (U.quadraticForm_orthogonalRestriction hpodd x g hfix
        ((U.orthogonalBasis x).equivFun.symm z))

end PositiveDefiniteIntegralLattice
