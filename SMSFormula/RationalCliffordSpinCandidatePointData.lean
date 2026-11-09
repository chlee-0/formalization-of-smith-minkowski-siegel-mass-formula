import SMSFormula.RationalCliffordCoordinateBaseChangeOperations

/-!
# Arbitrary-algebra point data for the affine Clifford--Spin candidate

For every commutative rational algebra `A`, this file reconstructs from a
candidate coordinate-ring point the corresponding element of the finite
base-changed Clifford algebra and its special-orthogonal matrix.  The
polynomial relations become exactly evenness, the one-sided Clifford norm,
and the vector-graph equation.  Conversely these data annihilate the relation
ideal and hence define a unique coordinate-ring point.

The resulting equivalence is over arbitrary commutative rational algebras,
not only fields.  The preceding Dedekind-finiteness theorem shows that the
stored one-sided norm makes the Clifford element a genuine unit.  Group
operations on this carrier are a separate following layer.
-/

noncomputable section

open CliffordAlgebra
open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

theorem cliffordCoordinateBaseChange_rat_smul
    (q : ℚ) (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    q • x = algebraMap ℚ A q • x :=
  (IsScalarTower.algebraMap_smul A q x).symm

theorem cliffordCoordinateBaseChangeBasis_repr_mul
    (x y : V.cliffordCoordinateBaseChangeAlgebra A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr (x * y) u =
      ∑ s, ∑ t,
        (V.cliffordCoordinateBaseChangeBasis A).repr x s *
          (V.cliffordCoordinateBaseChangeBasis A).repr y t *
          algebraMap ℚ A (V.cliffordMulStructureConstant s t u) := by
  conv_lhs =>
    rw [← (V.cliffordCoordinateBaseChangeBasis A).sum_repr x]
    rw [← (V.cliffordCoordinateBaseChangeBasis A).sum_repr y]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [smul_mul_smul]
  rw [V.cliffordCoordinateBaseChangeBasis_mul_eq_sum]
  simp_rw [V.cliffordCoordinateBaseChange_rat_smul A]
  rw [map_smul, map_sum]
  simp only [Finsupp.smul_apply]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [map_smul, Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single u]
  · simp [← IsScalarTower.algebraMap_smul A, mul_comm]
  · intro b _ hbu
    simp [hbu]
  · intro hu
    simp at hu

theorem cliffordCoordinateBaseChangeBasis_repr_involute
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeInvolute A x) u =
      ∑ s, (V.cliffordCoordinateBaseChangeBasis A).repr x s *
        algebraMap ℚ A (V.cliffordInvoluteStructureConstant s u) := by
  conv_lhs =>
    rw [← (V.cliffordCoordinateBaseChangeBasis A).sum_repr x]
  rw [map_sum]
  simp_rw [map_smul]
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [V.cliffordCoordinateBaseChangeBasis_involute_eq_sum,
    Finset.smul_sum]
  simp_rw [V.cliffordCoordinateBaseChange_rat_smul A, smul_smul]
  rw [map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [map_smul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hbu
    simp [hbu]
  · intro hu
    simp at hu

theorem cliffordCoordinateBaseChangeBasis_repr_reverse
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeReverse A x) u =
      ∑ s, (V.cliffordCoordinateBaseChangeBasis A).repr x s *
        algebraMap ℚ A (V.cliffordReverseStructureConstant s u) := by
  conv_lhs =>
    rw [← (V.cliffordCoordinateBaseChangeBasis A).sum_repr x]
  rw [map_sum]
  simp_rw [map_smul]
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [V.cliffordCoordinateBaseChangeBasis_reverse_eq_sum,
    Finset.smul_sum]
  simp_rw [V.cliffordCoordinateBaseChange_rat_smul A, smul_smul]
  rw [map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [map_smul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hbu
    simp [hbu]
  · intro hu
    simp at hu

def cliffordSpinCandidateBaseChangeEvaluation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) :
    cliffordSpinCandidatePolynomialRing n →ₐ[ℚ] A :=
  MvPolynomial.aeval fun z =>
    match z with
    | Sum.inl s => (V.cliffordCoordinateBaseChangeBasis A).repr x s
    | Sum.inr (i, j) => M i j

@[simp]
theorem cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (s : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (cliffordSpinVariable (n := n) s) =
      (V.cliffordCoordinateBaseChangeBasis A).repr x s := by
  simp [cliffordSpinCandidateBaseChangeEvaluation, cliffordSpinVariable]

@[simp]
theorem cliffordSpinCandidateBaseChangeEvaluation_matrixVariable
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (cliffordSpinMatrixVariable (n := n) i j) = M i j := by
  simp [cliffordSpinCandidateBaseChangeEvaluation,
    cliffordSpinMatrixVariable]

def cliffordSpinCandidateElementOfCoordinateAlgHom
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  ∑ s, F (V.cliffordSpinCandidateCliffordCoordinate s) •
    V.cliffordCoordinateBaseChangeBasis A s

@[simp]
theorem cliffordSpinCandidateElementOfCoordinateAlgHom_repr
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordSpinCandidateElementOfCoordinateAlgHom A F) u =
      F (V.cliffordSpinCandidateCliffordCoordinate u) := by
  rw [cliffordSpinCandidateElementOfCoordinateAlgHom, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single u]
  · rw [map_smul, Module.Basis.repr_self]
    simp
  · intro s _ hsu
    rw [map_smul, Module.Basis.repr_self]
    simp [hsu]
  · simp

def cliffordSpinCandidateMatrixOfCoordinateAlgHom
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    Matrix (Fin n) (Fin n) A :=
  fun i j => F (V.cliffordSpinCandidateMatrixCoordinate i j)

theorem cliffordSpinCandidateCoordinateAlgHom_comp_mk
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    F.comp (Ideal.Quotient.mkₐ ℚ V.cliffordSpinCandidateRelationIdeal) =
      V.cliffordSpinCandidateBaseChangeEvaluation A
        (V.cliffordSpinCandidateElementOfCoordinateAlgHom A F)
        (V.cliffordSpinCandidateMatrixOfCoordinateAlgHom A F) := by
  apply MvPolynomial.algHom_ext
  intro z
  rcases z with s | ij
  · rw [show MvPolynomial.X (Sum.inl s) =
        cliffordSpinVariable (n := n) s by rfl]
    simp [cliffordSpinCandidateCliffordCoordinate,
      V.cliffordSpinCandidateElementOfCoordinateAlgHom_repr]
  · rcases ij with ⟨i, j⟩
    rw [show MvPolynomial.X (Sum.inr (i, j)) =
        cliffordSpinMatrixVariable (n := n) i j by rfl]
    simp [cliffordSpinCandidateMatrixCoordinate,
      cliffordSpinCandidateMatrixOfCoordinateAlgHom]

def cliffordCoordinateBaseChangeOfRational
    (x : CliffordAlgebra V.quadraticForm) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  Algebra.TensorProduct.includeRight x

@[simp]
theorem cliffordCoordinateBaseChangeOfRational_repr
    (x : CliffordAlgebra V.quadraticForm) (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeOfRational A x) u =
      algebraMap ℚ A (V.cliffordCoordinateBasis.repr x u) := by
  rw [cliffordCoordinateBaseChangeOfRational,
    Algebra.TensorProduct.includeRight_apply]
  simp [cliffordCoordinateBaseChangeBasis,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

def cliffordCoordinateBaseChangeVector (i : Fin n) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  V.cliffordCoordinateBaseChangeOfRational A
    (CliffordAlgebra.ι V.quadraticForm (Pi.single i 1))

@[simp]
theorem cliffordCoordinateBaseChangeVector_repr
    (i : Fin n) (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeVector A i) u =
      algebraMap ℚ A (V.cliffordVectorBasisCoordinate i u) := by
  exact V.cliffordCoordinateBaseChangeOfRational_repr A _ u

theorem cliffordSpinCandidateBaseChangeEvaluation_coordinateMul
    (x y z : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A)
    (a b : Finset (Fin n) → cliffordSpinCandidatePolynomialRing n)
    (ha : ∀ s, V.cliffordSpinCandidateBaseChangeEvaluation A z M (a s) =
      (V.cliffordCoordinateBaseChangeBasis A).repr x s)
    (hb : ∀ s, V.cliffordSpinCandidateBaseChangeEvaluation A z M (b s) =
      (V.cliffordCoordinateBaseChangeBasis A).repr y s)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A z M
        (V.cliffordSpinCoordinateMul a b u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr (x * y) u := by
  rw [cliffordSpinCoordinateMul, map_sum,
    V.cliffordCoordinateBaseChangeBasis_repr_mul A]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [map_mul, ha, hb]
  have hc : V.cliffordSpinCandidateBaseChangeEvaluation A z M
      (MvPolynomial.C (V.cliffordMulStructureConstant s t u)) =
        algebraMap ℚ A (V.cliffordMulStructureConstant s t u) := by
    simp [cliffordSpinCandidateBaseChangeEvaluation]
  rw [hc]
  ring

theorem cliffordSpinCandidateBaseChangeEvaluation_reverseCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinUniversalReverseCoordinate u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeReverse A x) u := by
  rw [cliffordSpinUniversalReverseCoordinate, map_sum,
    V.cliffordCoordinateBaseChangeBasis_repr_reverse A]
  apply Finset.sum_congr rfl
  intro s _
  simp only [map_mul,
    V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable]
  have hc : V.cliffordSpinCandidateBaseChangeEvaluation A x M
      (MvPolynomial.C (V.cliffordReverseStructureConstant s u)) =
        algebraMap ℚ A (V.cliffordReverseStructureConstant s u) := by
    simp [cliffordSpinCandidateBaseChangeEvaluation]
  rw [hc]
  ring

theorem cliffordSpinCandidateBaseChangeEvaluation_involuteCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinUniversalInvoluteCoordinate u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeInvolute A x) u := by
  rw [cliffordSpinUniversalInvoluteCoordinate, map_sum,
    V.cliffordCoordinateBaseChangeBasis_repr_involute A]
  apply Finset.sum_congr rfl
  intro s _
  simp only [map_mul,
    V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable]
  have hc : V.cliffordSpinCandidateBaseChangeEvaluation A x M
      (MvPolynomial.C (V.cliffordInvoluteStructureConstant s u)) =
        algebraMap ℚ A (V.cliffordInvoluteStructureConstant s u) := by
    simp [cliffordSpinCandidateBaseChangeEvaluation]
  rw [hc]
  ring

theorem cliffordSpinCandidateBaseChangeEvaluation_oneCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (MvPolynomial.C (V.cliffordSpinOneCoordinate u)) =
      (V.cliffordCoordinateBaseChangeBasis A).repr 1 u := by
  rw [← map_one (Algebra.TensorProduct.includeRight :
      CliffordAlgebra V.quadraticForm →ₐ[ℚ]
        V.cliffordCoordinateBaseChangeAlgebra A)]
  change _ = (V.cliffordCoordinateBaseChangeBasis A).repr
    (V.cliffordCoordinateBaseChangeOfRational A 1) u
  rw [V.cliffordCoordinateBaseChangeOfRational_repr]
  simp [cliffordSpinCandidateBaseChangeEvaluation,
    cliffordSpinOneCoordinate]

theorem cliffordSpinCandidateBaseChangeEvaluation_normCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinUniversalNormCoordinate u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (x * V.cliffordCoordinateBaseChangeReverse A x) u := by
  apply V.cliffordSpinCandidateBaseChangeEvaluation_coordinateMul A x
    (V.cliffordCoordinateBaseChangeReverse A x) x M
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable A x M s
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_reverseCoordinate A x M s

theorem cliffordSpinCandidateBaseChangeEvaluation_evenRelation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinEvenRelation u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
          (V.cliffordCoordinateBaseChangeInvolute A x) u -
        (V.cliffordCoordinateBaseChangeBasis A).repr x u := by
  rw [cliffordSpinEvenRelation, map_sub,
    V.cliffordSpinCandidateBaseChangeEvaluation_involuteCoordinate,
    V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable]

theorem cliffordSpinCandidateBaseChangeEvaluation_normOneRelation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinNormOneRelation u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
          (x * V.cliffordCoordinateBaseChangeReverse A x) u -
        (V.cliffordCoordinateBaseChangeBasis A).repr 1 u := by
  rw [cliffordSpinNormOneRelation, map_sub,
    V.cliffordSpinCandidateBaseChangeEvaluation_normCoordinate,
    V.cliffordSpinCandidateBaseChangeEvaluation_oneCoordinate]

theorem cliffordSpinCandidateBaseChangeEvaluation_vectorCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i : Fin n)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (MvPolynomial.C (V.cliffordVectorBasisCoordinate i u)) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordCoordinateBaseChangeVector A i) u := by
  rw [V.cliffordCoordinateBaseChangeVector_repr]
  simp [cliffordSpinCandidateBaseChangeEvaluation]

theorem cliffordSpinCandidateBaseChangeEvaluation_leftVectorCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i : Fin n)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinUniversalLeftVectorCoordinate i u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (x * V.cliffordCoordinateBaseChangeVector A i) u := by
  apply V.cliffordSpinCandidateBaseChangeEvaluation_coordinateMul A x
    (V.cliffordCoordinateBaseChangeVector A i) x M
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_cliffordVariable A x M s
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_vectorCoordinate A x M i s

theorem cliffordSpinCandidateBaseChangeEvaluation_conjugationCoordinate
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i : Fin n)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinUniversalConjugationCoordinate i u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (x * V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A x) u := by
  apply V.cliffordSpinCandidateBaseChangeEvaluation_coordinateMul A
    (x * V.cliffordCoordinateBaseChangeVector A i)
    (V.cliffordCoordinateBaseChangeReverse A x) x M
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_leftVectorCoordinate A x M i s
  · intro s
    exact V.cliffordSpinCandidateBaseChangeEvaluation_reverseCoordinate A x M s

theorem cliffordSpinCandidateBaseChangeEvaluation_vectorGraphRelation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i : Fin n)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinVectorGraphRelation i u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr
          (x * V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordCoordinateBaseChangeReverse A x) u -
        ∑ j, M j i * (V.cliffordCoordinateBaseChangeBasis A).repr
          (V.cliffordCoordinateBaseChangeVector A j) u := by
  rw [cliffordSpinVectorGraphRelation, map_sub,
    V.cliffordSpinCandidateBaseChangeEvaluation_conjugationCoordinate]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul,
    V.cliffordSpinCandidateBaseChangeEvaluation_matrixVariable,
    V.cliffordSpinCandidateBaseChangeEvaluation_vectorCoordinate]

theorem cliffordSpinCandidateBaseChangeEvaluation_specialOrthogonalRelation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        (V.cliffordSpinSpecialOrthogonalRelation i j) =
      (M.transpose * V.specialOrthogonalMappedFormMatrix A * M) i j -
        V.specialOrthogonalMappedFormMatrix A i j := by
  simp [cliffordSpinSpecialOrthogonalRelation,
    cliffordSpinCandidateBaseChangeEvaluation,
    cliffordSpinMatrixVariable, specialOrthogonalMappedFormMatrix,
    Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]

theorem cliffordSpinCandidateBaseChangeEvaluation_specialOrthogonalDetRelation
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M : Matrix (Fin n) (Fin n) A) :
    V.cliffordSpinCandidateBaseChangeEvaluation A x M
        V.cliffordSpinSpecialOrthogonalDetRelation = M.det - 1 := by
  simp only [cliffordSpinSpecialOrthogonalDetRelation, map_sub, map_one]
  congr 1
  change (V.cliffordSpinCandidateBaseChangeEvaluation A x M).toRingHom
      (cliffordSpinUniversalMatrix (n := n)).det = M.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [cliffordSpinUniversalMatrix, cliffordSpinMatrixVariable,
    cliffordSpinCandidateBaseChangeEvaluation]

@[ext]
structure CliffordSpinCandidatePointData where
  clifford : V.cliffordCoordinateBaseChangeAlgebra A
  matrixPoint : V.specialOrthogonalMatrixPoint A
  involute_eq : V.cliffordCoordinateBaseChangeInvolute A clifford = clifford
  mul_reverse_eq_one :
    clifford * V.cliffordCoordinateBaseChangeReverse A clifford = 1
  vectorGraph : ∀ i,
    clifford * V.cliffordCoordinateBaseChangeVector A i *
        V.cliffordCoordinateBaseChangeReverse A clifford =
      ∑ j, matrixPoint.1 j i • V.cliffordCoordinateBaseChangeVector A j

def CliffordSpinCandidatePointData.cliffordUnit
    (d : V.CliffordSpinCandidatePointData A) :
    (V.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
  V.cliffordCoordinateBaseChangeUnitOfMulReverseEqOne A
    d.clifford d.mul_reverse_eq_one

@[simp]
theorem CliffordSpinCandidatePointData.coe_cliffordUnit
    (d : V.CliffordSpinCandidatePointData A) :
    (d.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) =
      d.clifford := rfl

def cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfCoordinateAlgHom
    (F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom)

@[simp]
theorem cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom_apply
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A)
    (i j : Fin n) :
    (V.cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom A F).1 i j =
      F (V.cliffordSpinCandidateMatrixCoordinate i j) := by
  change (F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom)
    (V.specialOrthogonalCoordinate i j) = _
  rw [AlgHom.comp_apply,
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom_coordinate]

theorem cliffordSpinCandidateBaseChangeEvaluation_relation_eq_zero
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A)
    {p : cliffordSpinCandidatePolynomialRing n}
    (hp : p ∈ V.cliffordSpinCandidateRelationIdeal) :
    V.cliffordSpinCandidateBaseChangeEvaluation A
        (V.cliffordSpinCandidateElementOfCoordinateAlgHom A F)
        (V.cliffordSpinCandidateMatrixOfCoordinateAlgHom A F) p = 0 := by
  rw [← V.cliffordSpinCandidateCoordinateAlgHom_comp_mk A F]
  change F (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]

def cliffordSpinCandidatePointDataOfCoordinateAlgHom
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.CliffordSpinCandidatePointData A where
  clifford := V.cliffordSpinCandidateElementOfCoordinateAlgHom A F
  matrixPoint :=
    V.cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom A F
  involute_eq := by
    apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
    ext u
    have hmem : V.cliffordSpinEvenRelation u ∈
        V.cliffordSpinCandidateRelationIdeal := by
      apply Ideal.subset_span
      simp [cliffordSpinCandidateRelationSet]
    have hzero :=
      V.cliffordSpinCandidateBaseChangeEvaluation_relation_eq_zero A F hmem
    rw [V.cliffordSpinCandidateBaseChangeEvaluation_evenRelation] at hzero
    exact sub_eq_zero.mp hzero
  mul_reverse_eq_one := by
    apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
    ext u
    have hmem : V.cliffordSpinNormOneRelation u ∈
        V.cliffordSpinCandidateRelationIdeal := by
      apply Ideal.subset_span
      simp [cliffordSpinCandidateRelationSet]
    have hzero :=
      V.cliffordSpinCandidateBaseChangeEvaluation_relation_eq_zero A F hmem
    rw [V.cliffordSpinCandidateBaseChangeEvaluation_normOneRelation] at hzero
    exact sub_eq_zero.mp hzero
  vectorGraph := by
    intro i
    apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
    ext u
    have hmem : V.cliffordSpinVectorGraphRelation i u ∈
        V.cliffordSpinCandidateRelationIdeal := by
      apply Ideal.subset_span
      simp [cliffordSpinCandidateRelationSet]
    have hzero :=
      V.cliffordSpinCandidateBaseChangeEvaluation_relation_eq_zero A F hmem
    rw [V.cliffordSpinCandidateBaseChangeEvaluation_vectorGraphRelation,
      sub_eq_zero] at hzero
    rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul,
      cliffordSpinCandidateMatrixOfCoordinateAlgHom,
      V.cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom_apply]
      using hzero

@[simp]
theorem cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).clifford u =
      F (V.cliffordSpinCandidateCliffordCoordinate u) := by
  exact V.cliffordSpinCandidateElementOfCoordinateAlgHom_repr A F u

@[simp]
theorem cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A)
    (i j : Fin n) :
    (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixPoint.1 i j =
      F (V.cliffordSpinCandidateMatrixCoordinate i j) := by
  exact V.cliffordSpinCandidateSpecialOrthogonalPointOfCoordinateAlgHom_apply A F i j

theorem CliffordSpinCandidatePointData.evaluation_relationSet_eq_zero
    (d : V.CliffordSpinCandidatePointData A)
    {p : cliffordSpinCandidatePolynomialRing n}
    (hp : p ∈ V.cliffordSpinCandidateRelationSet) :
    V.cliffordSpinCandidateBaseChangeEvaluation A
        d.clifford d.matrixPoint.1 p = 0 := by
  simp only [cliffordSpinCandidateRelationSet, Set.mem_union,
    Set.mem_range, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · rcases hp with hp | hp
        · rcases hp with ⟨u, rfl⟩
          rw [V.cliffordSpinCandidateBaseChangeEvaluation_evenRelation,
            d.involute_eq]
          simp
        · rcases hp with ⟨u, rfl⟩
          rw [V.cliffordSpinCandidateBaseChangeEvaluation_normOneRelation,
            d.mul_reverse_eq_one]
          simp
      · rcases hp with ⟨iu, rfl⟩
        rw [V.cliffordSpinCandidateBaseChangeEvaluation_vectorGraphRelation,
          d.vectorGraph iu.1, map_sum, Finsupp.coe_finset_sum,
          Finset.sum_apply]
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, sub_self]
    · rcases hp with ⟨ij, rfl⟩
      rw [V.cliffordSpinCandidateBaseChangeEvaluation_specialOrthogonalRelation,
        d.matrixPoint.2.1]
      simp
  · rw [hp,
      V.cliffordSpinCandidateBaseChangeEvaluation_specialOrthogonalDetRelation,
      d.matrixPoint.2.2]
    simp

theorem CliffordSpinCandidatePointData.relationIdeal_le_evaluation_ker
    (d : V.CliffordSpinCandidatePointData A) :
    V.cliffordSpinCandidateRelationIdeal ≤ RingHom.ker
      (V.cliffordSpinCandidateBaseChangeEvaluation A
        d.clifford d.matrixPoint.1).toRingHom := by
  rw [cliffordSpinCandidateRelationIdeal]
  apply Ideal.span_le.2
  intro p hp
  exact CliffordSpinCandidatePointData.evaluation_relationSet_eq_zero
    (V := V) (A := A) d hp

def cliffordSpinCandidateCoordinateAlgHomOfPointData
    (d : V.CliffordSpinCandidatePointData A) :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A :=
  Ideal.Quotient.liftₐ V.cliffordSpinCandidateRelationIdeal
    (V.cliffordSpinCandidateBaseChangeEvaluation A
      d.clifford d.matrixPoint.1)
    (by
      intro p hp
      exact CliffordSpinCandidatePointData.relationIdeal_le_evaluation_ker
        (V := V) (A := A) d hp)

@[simp]
theorem cliffordSpinCandidateCoordinateAlgHomOfPointData_cliffordCoordinate
    (d : V.CliffordSpinCandidatePointData A)
    (u : Finset (Fin n)) :
    V.cliffordSpinCandidateCoordinateAlgHomOfPointData A d
        (V.cliffordSpinCandidateCliffordCoordinate u) =
      (V.cliffordCoordinateBaseChangeBasis A).repr d.clifford u := by
  simp [cliffordSpinCandidateCoordinateAlgHomOfPointData,
    cliffordSpinCandidateCliffordCoordinate]

@[simp]
theorem cliffordSpinCandidateCoordinateAlgHomOfPointData_matrixCoordinate
    (d : V.CliffordSpinCandidatePointData A) (i j : Fin n) :
    V.cliffordSpinCandidateCoordinateAlgHomOfPointData A d
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      d.matrixPoint.1 i j := by
  simp [cliffordSpinCandidateCoordinateAlgHomOfPointData,
    cliffordSpinCandidateMatrixCoordinate]

def cliffordSpinCandidateCoordinateAlgHomEquivPointData :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) ≃
      V.CliffordSpinCandidatePointData A where
  toFun := V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A
  invFun := V.cliffordSpinCandidateCoordinateAlgHomOfPointData A
  left_inv F := by
    apply Ideal.Quotient.algHom_ext ℚ
    apply MvPolynomial.algHom_ext
    intro z
    rcases z with s | ij
    · change V.cliffordSpinCandidateCoordinateAlgHomOfPointData A
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F)
          (V.cliffordSpinCandidateCliffordCoordinate s) =
        F (V.cliffordSpinCandidateCliffordCoordinate s)
      simp
    · rcases ij with ⟨i, j⟩
      change V.cliffordSpinCandidateCoordinateAlgHomOfPointData A
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F)
          (V.cliffordSpinCandidateMatrixCoordinate i j) =
        F (V.cliffordSpinCandidateMatrixCoordinate i j)
      simp
  right_inv d := by
    apply CliffordSpinCandidatePointData.ext
    · apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
      ext u
      simp
    · apply Subtype.ext
      ext i j
      simp

end RationalQuadraticSpaceMatrix
