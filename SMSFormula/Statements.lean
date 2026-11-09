import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Statements in Lean and Mathlib terms

This file imports only Mathlib. It defines the objects that `Challenge.lean`
uses to state the main examples, so that a reader can check those statements
without reading the rest of the library.

A positive-definite integral lattice on `ℤⁿ` is given by its Gram matrix `G`:
a symmetric integer matrix that is positive definite over `ℝ`. The norm of `x`
is `xᵀ G x`. Two Gram matrices are isometric when `Uᵀ G' U = G` for some
`U ∈ GLₙ(ℤ)`, and they are in the same genus when such a `U` exists over every
`ℤ_p` and over `ℝ`. The mass of a family of lattices is `∑ 1 / |O(L)|` over its
isometry classes.

`Solution.lean` proves the statements of `Challenge.lean` from the library.
-/

namespace SMSFormula.Statements

open Matrix

variable {n : ℕ}

/-- `G` is the Gram matrix of a positive-definite integral lattice on `ℤⁿ`. -/
def IsPosDefGram (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  G.IsSymm ∧ (G.map (Int.cast : ℤ → ℝ)).PosDef

/-- `G` and `G'` are integrally isometric: `Uᵀ G' U = G` for some `U ∈ GLₙ(ℤ)`. -/
def Isometric (G G' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U ∧ Uᵀ * G' * U = G

/-- `G` and `G'` are in the same genus: they are isometric over `ℤ_p` for every
prime `p` and over `ℝ`. -/
def SameGenus (G G' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], ∃ U : Matrix (Fin n) (Fin n) ℤ_[p],
      IsUnit U ∧ Uᵀ * G'.map (Int.cast : ℤ → ℤ_[p]) * U = G.map (Int.cast : ℤ → ℤ_[p])) ∧
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      IsUnit U ∧ Uᵀ * G'.map (Int.cast : ℤ → ℝ) * U = G.map (Int.cast : ℤ → ℝ)

/-- The isometry group `O(G) = {U ∈ GLₙ(ℤ) | Uᵀ G U = G}`. -/
def IsometryGroup (G : Matrix (Fin n) (Fin n) ℤ) : Type :=
  { U : Matrix (Fin n) (Fin n) ℤ // IsUnit U ∧ Uᵀ * G * U = G }

theorem isometric_equivalence : Equivalence (@Isometric n) where
  refl G := ⟨1, isUnit_one, by simp⟩
  symm := by
    rintro G G' ⟨U, hU, h⟩
    have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
    refine ⟨U⁻¹, (Matrix.isUnit_iff_isUnit_det _).mpr (by
      rw [Matrix.det_nonsing_inv]; exact hdet.ringInverse), ?_⟩
    rw [← h, Matrix.transpose_nonsing_inv]
    calc (Uᵀ)⁻¹ * (Uᵀ * G' * U) * U⁻¹ = ((Uᵀ)⁻¹ * Uᵀ) * G' * (U * U⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = G' := by
          rw [Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]),
            Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.mul_one]
  trans := by
    rintro G G' G'' ⟨U, hU, h⟩ ⟨V, hV, h'⟩
    refine ⟨V * U, hV.mul hU, ?_⟩
    rw [← h, ← h', Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-- The isometry classes of the lattices on `ℤⁿ` whose Gram matrix satisfies `P`. -/
def IsometryClasses (P : Matrix (Fin n) (Fin n) ℤ → Prop) : Type :=
  Quotient (Setoid.comap (fun G : { G // IsPosDefGram G ∧ P G } => G.1)
    ⟨Isometric, isometric_equivalence⟩)

/-- The mass `∑ 1 / |O(L)|` over the isometry classes of the lattices whose Gram
matrix satisfies `P`. It is a `finsum`, so the statements that use it also
assert that there are finitely many classes. -/
noncomputable def mass (P : Matrix (Fin n) (Fin n) ℤ → Prop) : ℚ :=
  ∑ᶠ C : IsometryClasses P, ((Nat.card (IsometryGroup C.out.1) : ℚ))⁻¹

/-- The mass of the genus of `G`. -/
noncomputable def genusMass (G : Matrix (Fin n) (Fin n) ℤ) : ℚ :=
  mass (SameGenus G)

/-- Type I (odd) unimodular lattices: `det G = 1` and some vector has odd norm. -/
def IsTypeI (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  G.det = 1 ∧ ∃ x : Fin n → ℤ, Odd (x ⬝ᵥ G *ᵥ x)

/-- Type II (even) unimodular lattices: `det G = 1` and every norm is even. -/
def IsTypeII (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  G.det = 1 ∧ ∀ x : Fin n → ℤ, Even (x ⬝ᵥ G *ᵥ x)

/-! ### The closed constants of the unimodular mass formulas -/

/-- `P_r = ∏_{j=1}^r |B_{2j}| / (4j)`. -/
def bernoulliCore (r : ℕ) : ℚ :=
  ∏ j ∈ Finset.range r,
    |bernoulli (2 * (j + 1))| / (4 * (j + 1) : ℚ)

/-- The Bernoulli polynomial `B_m(x)`, with `B_1 = -1/2`. -/
def bernoulliPolynomial (m : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ Finset.range (m + 1),
    (Nat.choose m a : ℚ) * bernoulli a * x ^ (m - a)

/-- The generalized Bernoulli number `B_{m,χ₋₄} = 4^(m-1) (B_m(1/4) - B_m(3/4))`
for `m ≥ 1`, and `0` for `m = 0`. -/
def chiMinusFourBernoulli (m : ℕ) : ℚ :=
  if m = 0 then 0
  else (4 : ℚ) ^ (m - 1) *
    (bernoulliPolynomial m (1 / 4) - bernoulliPolynomial m (3 / 4))

/-- The sign in the odd-rank Type I formula. -/
def typeIOddRankSign (n : ℕ) : ℚ :=
  if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

/-- The sign in the even-rank Type I formula. -/
def typeIEvenRankSign (n : ℕ) : ℚ :=
  if n % 8 = 0 then 1 else -1

/-- The total mass of the Type I unimodular lattices of rank `n`. -/
def typeIConstant (n : ℕ) : ℚ :=
  if n = 0 then 0
  else if n = 1 then 1 / 2
  else
    let m := n / 2
    if n % 2 = 1 then
      ((2 : ℚ) ^ m + typeIOddRankSign n) / 2 * bernoulliCore m
    else if m % 2 = 1 then
      |chiMinusFourBernoulli m| / (4 * m : ℚ) * bernoulliCore (m - 1)
    else
      ((2 : ℚ) ^ m - 1) * ((2 : ℚ) ^ (m - 1) + typeIEvenRankSign n) /
          (4 * m : ℚ) *
        |bernoulli m| * bernoulliCore (m - 1)

/-- The total mass of the Type II unimodular lattices of rank `n`; it is zero
unless `8 ∣ n`. -/
def typeIIConstant (n : ℕ) : ℚ :=
  if n = 0 then 1
  else if n % 8 = 0 then
    let m := n / 2
    |bernoulli m| / (2 * m : ℚ) * bernoulliCore (m - 1)
  else 0

end SMSFormula.Statements
