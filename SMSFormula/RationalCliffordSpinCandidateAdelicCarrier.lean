import SMSFormula.RationalCliffordSpinCandidateKernelFiber
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# Placewise and adelic carriers for the rational Clifford--Spin candidate

The Clifford--Spin candidate already represents a group-valued functor on
commutative rational algebras.  This file evaluates that functor on `ℚ`, `ℝ`,
the p-adic fields, the finite rational adeles, and the full rational adeles.
It also records scalar extension and its compatibility with the completed
candidate-to-special-orthogonal morphism.

These are carrier and functoriality statements only.  No topology, restricted
product description, Haar measure, condition (K), or Tamagawa normalization is
installed on the Spin-candidate groups here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The group of Clifford--Spin candidate points over a rational algebra. -/
abbrev CliffordSpinCandidateGroup
    (A : Type*) [CommRing A] [Algebra ℚ A] :=
  V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A

/-- Rational Clifford--Spin candidate points. -/
abbrev RationalCliffordSpinCandidateGroup :=
  V.CliffordSpinCandidateGroup ℚ

/-- Real Clifford--Spin candidate points. -/
abbrev RealCliffordSpinCandidateGroup :=
  V.CliffordSpinCandidateGroup ℝ

/-- Clifford--Spin candidate points over `ℚ_p`. -/
abbrev PadicCliffordSpinCandidateGroup
    (p : ℕ) [Fact (Nat.Prime p)] :=
  V.CliffordSpinCandidateGroup ℚ_[p]

/-- Finite-adelic Clifford--Spin candidate points. -/
abbrev FiniteAdelicCliffordSpinCandidateGroup :=
  V.CliffordSpinCandidateGroup RationalFiniteAdele

/-- Full-adelic Clifford--Spin candidate points. -/
abbrev FullAdelicCliffordSpinCandidateGroup :=
  V.CliffordSpinCandidateGroup RationalAdele

/-- Scalar extension on Clifford--Spin candidate point groups. -/
def cliffordSpinCandidateGroupMap
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    V.CliffordSpinCandidateGroup A →*
      V.CliffordSpinCandidateGroup B :=
  V.cliffordSpinCandidateCoordinateAlgHomMap A f

@[simp]
theorem cliffordSpinCandidateGroupMap_apply
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateGroupMap f x = f.comp x :=
  rfl

/-- Diagonal scalar extension from rational to real candidate points. -/
def rationalCliffordSpinCandidateRealDiagonalHom :
    V.RationalCliffordSpinCandidateGroup →*
      V.RealCliffordSpinCandidateGroup :=
  V.cliffordSpinCandidateGroupMap (Algebra.ofId ℚ ℝ)

/-- Diagonal scalar extension from rational to p-adic candidate points. -/
def rationalCliffordSpinCandidatePadicDiagonalHom
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.RationalCliffordSpinCandidateGroup →*
      V.PadicCliffordSpinCandidateGroup p :=
  V.cliffordSpinCandidateGroupMap (Algebra.ofId ℚ ℚ_[p])

/-- Diagonal scalar extension from rational to finite-adelic candidate points. -/
def rationalCliffordSpinCandidateFiniteAdelicDiagonalHom :
    V.RationalCliffordSpinCandidateGroup →*
      V.FiniteAdelicCliffordSpinCandidateGroup :=
  V.cliffordSpinCandidateGroupMap (Algebra.ofId ℚ RationalFiniteAdele)

/-- Diagonal scalar extension from rational to full-adelic candidate points. -/
def rationalCliffordSpinCandidateFullAdelicDiagonalHom :
    V.RationalCliffordSpinCandidateGroup →*
      V.FullAdelicCliffordSpinCandidateGroup :=
  V.cliffordSpinCandidateGroupMap (Algebra.ofId ℚ RationalAdele)

/-- The diagonal rational subgroup inside the full-adelic candidate group. -/
def rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :
    Subgroup V.FullAdelicCliffordSpinCandidateGroup :=
  V.rationalCliffordSpinCandidateFullAdelicDiagonalHom.range

/-- The abstract rational left quotient of the full-adelic candidate group. -/
abbrev FullAdelicCliffordSpinCandidateLeftQuotient :=
  leftCosetSet V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup

/-- The canonical map to the rational full-adelic candidate left quotient. -/
def fullAdelicCliffordSpinCandidateLeftQuotientMap :
    V.FullAdelicCliffordSpinCandidateGroup →
      V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  leftCosetMap V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup

/-- The candidate-to-`SO` homomorphism on an arbitrary rational algebra. -/
def cliffordSpinCandidateGroupToSpecialOrthogonal
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    V.CliffordSpinCandidateGroup A →*
      V.specialOrthogonalMatrixGroup A :=
  V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A

/-- Scalar extension commutes with the candidate-to-`SO` homomorphism. -/
theorem cliffordSpinCandidateGroupToSpecialOrthogonal_map
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal B
        (V.cliffordSpinCandidateGroupMap f x) =
      V.specialOrthogonalMatrixGroupMap f
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal A x) := by
  exact V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_map f x

/-- The full-adelic candidate map lands in the existing concrete
full-adelic special-orthogonal carrier. -/
def fullAdelicCliffordSpinCandidateToSpecialOrthogonalHom :
    V.FullAdelicCliffordSpinCandidateGroup →*
      V.FullAdelicSpecialOrthogonalGroup :=
  V.cliffordSpinCandidateGroupToSpecialOrthogonal RationalAdele

/-- The finite-adelic candidate map lands in the existing concrete
finite-adelic special-orthogonal carrier. -/
def finiteAdelicCliffordSpinCandidateToSpecialOrthogonalHom :
    V.FiniteAdelicCliffordSpinCandidateGroup →*
      V.FiniteAdelicSpecialOrthogonalGroup :=
  V.cliffordSpinCandidateGroupToSpecialOrthogonal RationalFiniteAdele

/-- The real candidate map lands in the existing concrete real
special-orthogonal carrier. -/
def realCliffordSpinCandidateToSpecialOrthogonalHom :
    V.RealCliffordSpinCandidateGroup →*
      V.RealSpecialOrthogonalGroup :=
  V.cliffordSpinCandidateGroupToSpecialOrthogonal ℝ

/-- Rational-to-full-adelic scalar extension commutes with the completed
candidate-to-special-orthogonal homomorphism. -/
theorem rational_fullAdelic_diagonal_candidateToSpecialOrthogonal
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateToSpecialOrthogonalHom
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom x) =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ RationalAdele)
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ x) := by
  exact V.cliffordSpinCandidateGroupToSpecialOrthogonal_map
    (Algebra.ofId ℚ RationalAdele) x

/-- Rational-to-finite-adelic scalar extension commutes with the completed
candidate-to-special-orthogonal homomorphism. -/
theorem rational_finiteAdelic_diagonal_candidateToSpecialOrthogonal
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.finiteAdelicCliffordSpinCandidateToSpecialOrthogonalHom
        (V.rationalCliffordSpinCandidateFiniteAdelicDiagonalHom x) =
      V.specialOrthogonalMatrixGroupMap
        (Algebra.ofId ℚ RationalFiniteAdele)
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ x) := by
  exact V.cliffordSpinCandidateGroupToSpecialOrthogonal_map
    (Algebra.ofId ℚ RationalFiniteAdele) x

/-- Rational-to-real scalar extension commutes with the completed
candidate-to-special-orthogonal homomorphism. -/
theorem rational_real_diagonal_candidateToSpecialOrthogonal
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
        (V.rationalCliffordSpinCandidateRealDiagonalHom x) =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ ℝ)
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ x) := by
  exact V.cliffordSpinCandidateGroupToSpecialOrthogonal_map
    (Algebra.ofId ℚ ℝ) x

/-- Rational-to-p-adic scalar extension commutes with the completed
candidate-to-special-orthogonal homomorphism. -/
theorem rational_padic_diagonal_candidateToSpecialOrthogonal
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
        (V.rationalCliffordSpinCandidatePadicDiagonalHom p x) =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ ℚ_[p])
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ x) := by
  exact V.cliffordSpinCandidateGroupToSpecialOrthogonal_map
    (Algebra.ofId ℚ ℚ_[p]) x

end RationalQuadraticSpaceMatrix
