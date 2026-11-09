import SMSFormula.RationalCliffordSpinScalarExtensionKernel
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Finite rational coordinates for the Clifford algebra

For the quadratic module `Fin n → ℚ`, the homogeneous exterior-power
bases are assembled through the exterior grading and reindexed by
`Finset (Fin n)`. Transport through `CliffordAlgebra.equivExterior` gives an
explicit basis of the rational Clifford algebra with `2^n` elements.

The file records rational structure constants for multiplication, grade
involution, and reverse, and proves that the same constants describe every
characteristic-zero scalar extension. It also defines the universal Clifford
element over the polynomial algebra on the `2^n` coordinates and records the
finite coordinate polynomials for multiplication, involution, reverse,
evenness, and norm one needed by an eventual affine Spin carrier.

The preservation-of-vectors relations and comparison of their solution
functor with mathlib's closure-generated `spinGroup` are separate following
boundaries. No affine Spin scheme, central morphism, or fppf exactness is
asserted here.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct DirectSum
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

def sigmaPowersetCardEquivFinset :
    (Σ k : ℕ, powersetCard (Fin n) k) ≃ Finset (Fin n) where
  toFun s := s.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv := by
    rintro ⟨k, ⟨s, hs⟩⟩
    dsimp at hs ⊢
    subst k
    rfl
  right_inv s := rfl

def exteriorDirectSumBasis :
    Module.Basis (Σ k : ℕ, powersetCard (Fin n) k) ℚ
      (⨁ k : ℕ, ⋀[ℚ]^k (Fin n → ℚ)) :=
  DFinsupp.basis fun k => (Pi.basisFun ℚ (Fin n)).exteriorPower k

def exteriorAlgebraBasisSigma :
    Module.Basis (Σ k : ℕ, powersetCard (Fin n) k) ℚ
      (ExteriorAlgebra ℚ (Fin n → ℚ)) :=
  (exteriorDirectSumBasis (n := n)).map
    (DirectSum.decomposeLinearEquiv
      (fun k : ℕ => ⋀[ℚ]^k (Fin n → ℚ))).symm

def exteriorAlgebraBasis :
    Module.Basis (Finset (Fin n)) ℚ
      (ExteriorAlgebra ℚ (Fin n → ℚ)) :=
  (exteriorAlgebraBasisSigma (n := n)).reindex
    (sigmaPowersetCardEquivFinset (n := n))

def cliffordCoordinateBasis :
    Module.Basis (Finset (Fin n)) ℚ
      (CliffordAlgebra V.quadraticForm) :=
  (exteriorAlgebraBasis (n := n)).map
    (CliffordAlgebra.equivExterior V.quadraticForm).symm

instance : Module.Finite ℚ (CliffordAlgebra V.quadraticForm) :=
  Module.Finite.of_basis (V.cliffordCoordinateBasis)

theorem finrank_cliffordAlgebra_eq_two_pow :
    Module.finrank ℚ (CliffordAlgebra V.quadraticForm) = 2 ^ n := by
  rw [Module.finrank_eq_card_basis V.cliffordCoordinateBasis,
    Fintype.card_finset, Fintype.card_fin]

def cliffordMulStructureConstant
    (s t u : Finset (Fin n)) : ℚ :=
  (V.cliffordCoordinateBasis.repr
    (V.cliffordCoordinateBasis s * V.cliffordCoordinateBasis t)) u

def cliffordInvoluteStructureConstant
    (s u : Finset (Fin n)) : ℚ :=
  (V.cliffordCoordinateBasis.repr
    (CliffordAlgebra.involute (V.cliffordCoordinateBasis s))) u

def cliffordReverseStructureConstant
    (s u : Finset (Fin n)) : ℚ :=
  (V.cliffordCoordinateBasis.repr
    (CliffordAlgebra.reverse (V.cliffordCoordinateBasis s))) u

theorem cliffordCoordinateBasis_mul_eq_sum
    (s t : Finset (Fin n)) :
    V.cliffordCoordinateBasis s * V.cliffordCoordinateBasis t =
      ∑ u, V.cliffordMulStructureConstant s t u •
        V.cliffordCoordinateBasis u := by
  exact (V.cliffordCoordinateBasis.sum_repr
    (V.cliffordCoordinateBasis s * V.cliffordCoordinateBasis t)).symm

theorem cliffordCoordinateBasis_involute_eq_sum
    (s : Finset (Fin n)) :
    CliffordAlgebra.involute (V.cliffordCoordinateBasis s) =
      ∑ u, V.cliffordInvoluteStructureConstant s u •
        V.cliffordCoordinateBasis u := by
  exact (V.cliffordCoordinateBasis.sum_repr
    (CliffordAlgebra.involute (V.cliffordCoordinateBasis s))).symm

theorem cliffordCoordinateBasis_reverse_eq_sum
    (s : Finset (Fin n)) :
    CliffordAlgebra.reverse (V.cliffordCoordinateBasis s) =
      ∑ u, V.cliffordReverseStructureConstant s u •
        V.cliffordCoordinateBasis u := by
  exact (V.cliffordCoordinateBasis.sum_repr
    (CliffordAlgebra.reverse (V.cliffordCoordinateBasis s))).symm

section CoordinateBaseChange

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def cliffordCoordinateBaseChangeBasis :
    Module.Basis (Finset (Fin n)) A
      (A ⊗[ℚ] CliffordAlgebra V.quadraticForm) :=
  V.cliffordCoordinateBasis.baseChange A

@[simp]
theorem cliffordCoordinateBaseChangeBasis_apply
    (s : Finset (Fin n)) :
    V.cliffordCoordinateBaseChangeBasis A s =
      1 ⊗ₜ[ℚ] V.cliffordCoordinateBasis s := by
  simp [cliffordCoordinateBaseChangeBasis]

theorem cliffordCoordinateBaseChangeBasis_mul_eq_sum
    (s t : Finset (Fin n)) :
    V.cliffordCoordinateBaseChangeBasis A s *
      V.cliffordCoordinateBaseChangeBasis A t =
      ∑ u, V.cliffordMulStructureConstant s t u •
        V.cliffordCoordinateBaseChangeBasis A u := by
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    V.cliffordCoordinateBaseChangeBasis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, V.cliffordCoordinateBasis_mul_eq_sum]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    Algebra.smul_def, ← TensorProduct.tmul_smul]
  congr 1

end CoordinateBaseChange

abbrev cliffordCoordinatePolynomialRing :=
  MvPolynomial (Finset (Fin n)) ℚ

def cliffordUniversalElement :
    cliffordCoordinatePolynomialRing (n := n) ⊗[ℚ]
      CliffordAlgebra V.quadraticForm :=
  ∑ s : Finset (Fin n),
    (MvPolynomial.X s : cliffordCoordinatePolynomialRing (n := n)) ⊗ₜ[ℚ]
      V.cliffordCoordinateBasis s

def cliffordUniversalMulCoordinate (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  ∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
    MvPolynomial.C (V.cliffordMulStructureConstant s t u) *
    MvPolynomial.X s * MvPolynomial.X t

def cliffordUniversalInvoluteCoordinate (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  ∑ s : Finset (Fin n),
    MvPolynomial.C (V.cliffordInvoluteStructureConstant s u) *
    MvPolynomial.X s

def cliffordUniversalReverseCoordinate (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  ∑ s : Finset (Fin n),
    MvPolynomial.C (V.cliffordReverseStructureConstant s u) *
    MvPolynomial.X s

def cliffordOneCoordinate (u : Finset (Fin n)) : ℚ :=
  (V.cliffordCoordinateBasis.repr 1) u

def cliffordUniversalNormCoordinate (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  ∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
    MvPolynomial.C (V.cliffordMulStructureConstant s t u) *
      MvPolynomial.X s * V.cliffordUniversalReverseCoordinate t

def cliffordEvenRelation (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  V.cliffordUniversalInvoluteCoordinate u - MvPolynomial.X u

def cliffordNormOneRelation (u : Finset (Fin n)) :
    cliffordCoordinatePolynomialRing (n := n) :=
  V.cliffordUniversalNormCoordinate u -
    MvPolynomial.C (V.cliffordOneCoordinate u)

def cliffordEvenNormRelationSet :
    Set (cliffordCoordinatePolynomialRing (n := n)) :=
  Set.range V.cliffordEvenRelation ∪ Set.range V.cliffordNormOneRelation

def cliffordEvenNormRelationIdeal :
    Ideal (cliffordCoordinatePolynomialRing (n := n)) :=
  Ideal.span V.cliffordEvenNormRelationSet

section ScalarExtension

variable (K : Type*) [Field K] [Algebra ℚ K] [Invertible (2 : K)]

def scalarExtensionCliffordCoordinateBasis :
    Module.Basis (Finset (Fin n)) K
      (CliffordAlgebra (V.scalarExtensionQuadraticForm K)) :=
  (V.cliffordCoordinateBasis.baseChange K).map
    (V.tensorCliffordScalarExtensionEquiv K).toLinearEquiv

end ScalarExtension

end RationalQuadraticSpaceMatrix
