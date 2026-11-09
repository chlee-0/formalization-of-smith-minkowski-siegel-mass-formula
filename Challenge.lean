import SMSFormula.Statements
import Mathlib.Data.Matrix.Cartan

/-!
# Challenge

The main examples, stated in Lean and Mathlib terms. The definitions come from
`SMSFormula/Statements.lean`, which imports only Mathlib. Every proof here is
`sorry`. `Solution.lean` proves the same statements from the library, and
`comparator` checks that the two files state the same theorems with the
standard axioms only (see `comparator.json`).

`genusMass G` is `∑ 1 / |O(L)|` over the isometry classes in the genus of the
lattice with Gram matrix `G`. `mass P` is the same sum over the isometry classes
of all lattices whose Gram matrix satisfies `P`.
-/

open SMSFormula.Statements

namespace SMSFormula.Challenge

/-- Rank 1: the root lattice `A₁`. -/
theorem genusMass_A1 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 1))) ∧
      genusMass (CartanMatrix.A 1) = 1 / 2 := sorry

/-- Rank 2: the root lattice `A₂`. -/
theorem genusMass_A2 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 2))) ∧
      genusMass (CartanMatrix.A 2) = 1 / 12 := sorry

/-- Rank 3: the lattice `x² + 2y² + 11z²`. -/
theorem genusMass_ternary :
    Finite (IsometryClasses (SameGenus !![(1 : ℤ), 0, 0; 0, 2, 0; 0, 0, 11])) ∧
      genusMass !![(1 : ℤ), 0, 0; 0, 2, 0; 0, 0, 11] = 3 / 8 := sorry

/-- Rank 4: the root lattice `A₄`. -/
theorem genusMass_A4 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 4))) ∧
      genusMass (CartanMatrix.A 4) = 1 / 240 := sorry

/-- Rank 8: the root lattice `E₈`. -/
theorem genusMass_E8 :
    Finite (IsometryClasses (SameGenus CartanMatrix.E₈)) ∧
      genusMass CartanMatrix.E₈ = 1 / 696729600 := sorry

/-- The total mass of the Type I (odd) unimodular lattices of every rank. -/
theorem mass_typeI (n : ℕ) :
    Finite (IsometryClasses (@IsTypeI n)) ∧ mass (@IsTypeI n) = typeIConstant n := sorry

/-- The total mass of the Type II (even) unimodular lattices of every rank. -/
theorem mass_typeII (n : ℕ) :
    Finite (IsometryClasses (@IsTypeII n)) ∧ mass (@IsTypeII n) = typeIIConstant n := sorry

end SMSFormula.Challenge
