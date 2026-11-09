import SMSFormula.RationalCliffordCoordinateBasis
import SMSFormula.RationalSpecialOrthogonalAffineScheme

/-!
# Polynomial vector-preservation equations for the Spin candidate

This file adds matrix coordinates to the finite Clifford coordinates and
writes the graph equations

```text
x * ι(e_i) * reverse(x) = sum_j M_{j,i} ι(e_j).
```

The relation ideal also contains Clifford evenness, norm one, and the defining
special-orthogonal equations for `M`. Every characteristic-zero field-valued
element of mathlib's closure-generated `spinGroup` gives an algebra point of
the quotient coordinate ring, with Clifford and matrix coordinates equal to
the existing fieldwise Spin data. Conversely, every algebra point supplies a
special-orthogonal matrix point and hence, over a field in the scheme API's
universe, an element of the completed scalar-extension `SO` subgroup.

No equivalence between all coordinate solutions and the closure-generated
Spin group is asserted. Bundling the candidate as a group scheme, identifying
its scheme kernel, and proving fppf surjectivity remain separate boundaries.
-/

noncomputable section

open CliffordAlgebra
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [Algebra ℚ K] [Invertible (2 : K)]

abbrev cliffordSpinCandidateIndex (n : ℕ) :=
  (Finset (Fin n)) ⊕ (Fin n × Fin n)

abbrev cliffordSpinCandidatePolynomialRing (n : ℕ) :=
  MvPolynomial (cliffordSpinCandidateIndex n) ℚ

def cliffordSpinVariable (s : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  MvPolynomial.X (Sum.inl s)

def cliffordSpinMatrixVariable (i j : Fin n) : cliffordSpinCandidatePolynomialRing n :=
  MvPolynomial.X (Sum.inr (i, j))

def cliffordSpinCoordinateMul
    (a b : Finset (Fin n) → cliffordSpinCandidatePolynomialRing n)
    (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  ∑ s, ∑ t, MvPolynomial.C (V.cliffordMulStructureConstant s t u) *
    a s * b t

def cliffordVectorBasisCoordinate (i : Fin n) (u : Finset (Fin n)) : ℚ :=
  V.cliffordCoordinateBasis.repr
    (CliffordAlgebra.ι V.quadraticForm (Pi.single i 1)) u

def cliffordSpinUniversalReverseCoordinate (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  ∑ s, MvPolynomial.C (V.cliffordReverseStructureConstant s u) *
    cliffordSpinVariable (n := n) s

def cliffordSpinUniversalInvoluteCoordinate (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  ∑ s, MvPolynomial.C (V.cliffordInvoluteStructureConstant s u) *
    cliffordSpinVariable (n := n) s

def cliffordSpinOneCoordinate (u : Finset (Fin n)) : ℚ :=
  V.cliffordCoordinateBasis.repr 1 u

def cliffordSpinUniversalLeftVectorCoordinate (i : Fin n) (u : Finset (Fin n)) :
    cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinCoordinateMul (cliffordSpinVariable (n := n))
    (fun t => MvPolynomial.C (V.cliffordVectorBasisCoordinate i t)) u

def cliffordSpinUniversalConjugationCoordinate (i : Fin n) (u : Finset (Fin n)) :
    cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinCoordinateMul (V.cliffordSpinUniversalLeftVectorCoordinate i) V.cliffordSpinUniversalReverseCoordinate u

def cliffordSpinUniversalNormCoordinate (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinCoordinateMul (cliffordSpinVariable (n := n)) V.cliffordSpinUniversalReverseCoordinate u

def cliffordSpinEvenRelation (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinUniversalInvoluteCoordinate u - cliffordSpinVariable (n := n) u

def cliffordSpinNormOneRelation (u : Finset (Fin n)) : cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinUniversalNormCoordinate u - MvPolynomial.C (V.cliffordSpinOneCoordinate u)

def cliffordSpinVectorGraphRelation (i : Fin n) (u : Finset (Fin n)) :
    cliffordSpinCandidatePolynomialRing n :=
  V.cliffordSpinUniversalConjugationCoordinate i u -
    ∑ j, cliffordSpinMatrixVariable (n := n) j i *
      MvPolynomial.C (V.cliffordVectorBasisCoordinate j u)

def cliffordSpinSpecialOrthogonalRelation (i j : Fin n) : cliffordSpinCandidatePolynomialRing n :=
  (∑ k, ∑ l,
      cliffordSpinMatrixVariable (n := n) k i *
        MvPolynomial.C (V.pairingMatrix k l) *
        cliffordSpinMatrixVariable (n := n) l j) -
    MvPolynomial.C (V.pairingMatrix i j)

def cliffordSpinUniversalMatrix : Matrix (Fin n) (Fin n) (cliffordSpinCandidatePolynomialRing n) :=
  fun i j => cliffordSpinMatrixVariable (n := n) i j

def cliffordSpinSpecialOrthogonalDetRelation
    (_V : RationalQuadraticSpaceMatrix n) : cliffordSpinCandidatePolynomialRing n :=
  (cliffordSpinUniversalMatrix (n := n)).det - 1

def cliffordSpinCandidateRelationSet : Set (cliffordSpinCandidatePolynomialRing n) :=
  Set.range V.cliffordSpinEvenRelation ∪
    Set.range V.cliffordSpinNormOneRelation ∪
    Set.range (fun iu : Fin n × Finset (Fin n) =>
      V.cliffordSpinVectorGraphRelation iu.1 iu.2) ∪
    Set.range (fun ij : Fin n × Fin n =>
      V.cliffordSpinSpecialOrthogonalRelation ij.1 ij.2) ∪
    {V.cliffordSpinSpecialOrthogonalDetRelation}

def cliffordSpinCandidateRelationIdeal : Ideal (cliffordSpinCandidatePolynomialRing n) :=
  Ideal.span V.cliffordSpinCandidateRelationSet

abbrev cliffordSpinCandidateCoordinateRing :=
  cliffordSpinCandidatePolynomialRing n ⧸ V.cliffordSpinCandidateRelationIdeal

def cliffordSpinCandidateCliffordCoordinate (s : Finset (Fin n)) : V.cliffordSpinCandidateCoordinateRing :=
  Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal (cliffordSpinVariable (n := n) s)

def cliffordSpinCandidateMatrixCoordinate (i j : Fin n) : V.cliffordSpinCandidateCoordinateRing :=
  Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal (cliffordSpinMatrixVariable (n := n) i j)

def scalarExtensionCliffordSpinCandidateEvaluation
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
    (M : Matrix (Fin n) (Fin n) K) : cliffordSpinCandidatePolynomialRing n →ₐ[ℚ] K :=
  MvPolynomial.aeval fun z =>
    match z with
    | Sum.inl s => (V.scalarExtensionCliffordCoordinateBasis K).repr x s
    | Sum.inr (i, j) => M i j

@[simp] theorem scalarExtensionCliffordSpinCandidateEvaluation_cliffordVariable
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
    (M : Matrix (Fin n) (Fin n) K) (s : Finset (Fin n)) :
    V.scalarExtensionCliffordSpinCandidateEvaluation K x M (cliffordSpinVariable (n := n) s) =
      (V.scalarExtensionCliffordCoordinateBasis K).repr x s := by
  simp [scalarExtensionCliffordSpinCandidateEvaluation, cliffordSpinVariable]

@[simp] theorem scalarExtensionCliffordSpinCandidateEvaluation_matrixVariable
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    V.scalarExtensionCliffordSpinCandidateEvaluation K x M (cliffordSpinMatrixVariable (n := n) i j) = M i j := by
  simp [scalarExtensionCliffordSpinCandidateEvaluation, cliffordSpinMatrixVariable]

theorem scalarExtensionCliffordCoordinateBasis_sum_standardVector_repr_eq_mulVec_single_repr
    (M : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (u : Finset (Fin n)) :
    ∑ j, M j i *
        (V.scalarExtensionCliffordCoordinateBasis K).repr
          (CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
            (Pi.single j 1)) u =
      (V.scalarExtensionCliffordCoordinateBasis K).repr
        (CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
          (M *ᵥ Pi.single i 1)) u := by
  have hvec : M *ᵥ (Pi.single i 1 : Fin n → K) =
      ∑ j, M j i • (Pi.single j 1 : Fin n → K) := by
    ext k
    simp [Pi.single_apply]
  rw [hvec, map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul]
  simp [smul_eq_mul]

theorem scalarExtensionSpin_conjugation_reverse
    (x : spinGroup (V.scalarExtensionQuadraticForm K)) (i : Fin n) :
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) *
          CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
            (Pi.single i 1) *
        CliffordAlgebra.reverse
          (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) =
      CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
        ((V.scalarExtensionSpinMatrixRepresentation K x :
          Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1) := by
  rw [V.scalarExtensionSpinMatrixRepresentation_mulVec]
  rw [spinGroup.conjugationRepresentation_apply]
  rw [spinGroup.ι_conjugationLinearEquiv]
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  change (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) *
          CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
            (Pi.single i 1) *
        CliffordAlgebra.reverse
          (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) =
      (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) *
          CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
            (Pi.single i 1) *
        star (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
  rw [CliffordAlgebra.star_def, spinGroup.involute_eq x.property]

theorem scalarExtensionCliffordSpinCandidateEvaluation_specialOrthogonalRelation
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    V.scalarExtensionCliffordSpinCandidateEvaluation K x M (V.cliffordSpinSpecialOrthogonalRelation i j) =
      (M.transpose * V.scalarExtensionFormMatrix K * M) i j -
        V.scalarExtensionFormMatrix K i j := by
  simp [cliffordSpinSpecialOrthogonalRelation, scalarExtensionCliffordSpinCandidateEvaluation,
    cliffordSpinMatrixVariable, scalarExtensionFormMatrix, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]

theorem scalarExtensionCliffordSpinCandidateEvaluation_specialOrthogonalDetRelation
    (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
    (M : Matrix (Fin n) (Fin n) K) :
    V.scalarExtensionCliffordSpinCandidateEvaluation K x M V.cliffordSpinSpecialOrthogonalDetRelation =
      M.det - 1 := by
  simp only [cliffordSpinSpecialOrthogonalDetRelation, map_sub, map_one]
  congr 1
  change (V.scalarExtensionCliffordSpinCandidateEvaluation K x M).toRingHom
      (cliffordSpinUniversalMatrix (n := n)).det = M.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [cliffordSpinUniversalMatrix, cliffordSpinMatrixVariable, scalarExtensionCliffordSpinCandidateEvaluation]

theorem scalarExtensionCliffordSpinCandidateEvaluation_specialOrthogonalRelation_spin
    (x : spinGroup (V.scalarExtensionQuadraticForm K))
    (i j : Fin n) :
    V.scalarExtensionCliffordSpinCandidateEvaluation K
      (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K))
      (V.scalarExtensionSpinMatrixRepresentation K x :
        Matrix (Fin n) (Fin n) K)
      (V.cliffordSpinSpecialOrthogonalRelation i j) = 0 := by
  rw [V.scalarExtensionCliffordSpinCandidateEvaluation_specialOrthogonalRelation]
  have horth := V.scalarExtensionSpinMatrixRepresentation_mem_orthogonal K x
  rw [PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff] at horth
  rw [horth]
  simp

def scalarExtensionCliffordSpinCandidateElement
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] K) :
    CliffordAlgebra (V.scalarExtensionQuadraticForm K) :=
  ∑ s, F (V.cliffordSpinCandidateCliffordCoordinate s) •
    V.scalarExtensionCliffordCoordinateBasis K s

def scalarExtensionCliffordSpinCandidateMatrix
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => F (V.cliffordSpinCandidateMatrixCoordinate i j)

end RationalQuadraticSpaceMatrix
