import SMSFormula.StatementsBridge
import SMSFormula.RankOneMass
import SMSFormula.Applications.Unimodular.Seeds
import Mathlib.Data.Matrix.Cartan

/-!
# The example lattices of the statements in Mathlib terms

`Challenge.lean` names its example lattices by Mathlib's Cartan matrices. This
file gives integral isometries from them to the Gram matrices of the library's
example lattices, proves the rank-one example, and matches the Type I and Type II
conditions with the library's predicates.
-/

open SMSFormula.Statements

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem isUnit_of_mul_eq_one {m : ℕ} {U V : Matrix (Fin m) (Fin m) ℤ}
    (h : U * V = 1) : IsUnit U :=
  (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_right_inverse h)

/-! ### Rank one: `A₁` -/

theorem cartanA1_isPosDefGram : IsPosDefGram (CartanMatrix.A 1) := by
  refine ⟨by ext i j; fin_cases i; fin_cases j; rfl, ?_⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i; fin_cases j; norm_num [CartanMatrix.A]
  · intro x hx
    have h0 : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
    have := mul_self_pos.mpr h0
    simp [CartanMatrix.A, Matrix.mulVec, dotProduct]
    nlinarith

theorem genusMass_cartanA1 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 1))) ∧
      genusMass (CartanMatrix.A 1) = 1 / 2 := by
  let L := ofGram (CartanMatrix.A 1) cartanA1_isPosDefGram
  have h := genusMass_pairingMatrix L
  exact ⟨h.1, h.2.trans (ordinaryGenusMass_eq_one_half_rank_one L)⟩

/-! ### Ranks two and four -/

theorem cartanA2_isometric : Isometric (CartanMatrix.A 2) !![2, 1; 1, 2] :=
  ⟨!![1, 0; 0, -1], isUnit_of_mul_eq_one (V := !![1, 0; 0, -1]) (by decide), by decide⟩

theorem cartanA4_isometric :
    Isometric (CartanMatrix.A 4) !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2] :=
  ⟨1, isUnit_one, by decide⟩

/-! ### `E₈` -/

/-- The permutation matrix that relabels the library's `E₈` Cartan matrix as
Mathlib's (Bourbaki's labelling). -/
def e8Relabel : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a b => if a = ![0, 7, 1, 2, 3, 4, 5, 6] b then 1 else 0

theorem cartanE8_isometric : Isometric CartanMatrix.E₈ e8CartanMatrix :=
  ⟨e8Relabel, isUnit_of_mul_eq_one (V := e8Relabel.transpose) (by decide), by decide⟩

theorem genusMass_cartanE8 :
    Finite (IsometryClasses (SameGenus CartanMatrix.E₈)) ∧
      genusMass CartanMatrix.E₈ = e8Lattice.ordinaryGenusMass :=
  genusMass_of_isometric e8Lattice cartanE8_isometric

/-! ### Type I and Type II -/

theorem isTypeI_iff (L : PositiveDefiniteIntegralLattice n) :
    IsTypeI L.pairingMatrix ↔ L.IsUnimodular ∧ L.HasOddNorm := by
  simp only [IsTypeI, IsUnimodular, HasOddNorm, pairingDeterminant, quadForm_eq_dotProduct]

theorem isTypeII_iff (L : PositiveDefiniteIntegralLattice n) :
    IsTypeII L.pairingMatrix ↔ L.IsUnimodular ∧ L.HasEvenNorms := by
  simp only [IsTypeII, IsUnimodular, HasEvenNorms, pairingDeterminant, quadForm_eq_dotProduct]

end PositiveDefiniteIntegralLattice
