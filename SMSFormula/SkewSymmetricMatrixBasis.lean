import SMSFormula.PadicCayleyDenominatorConjugation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Canonical coordinates for skew-symmetric matrices

Over a field of characteristic different from two, a skew-symmetric
`Fin n`-matrix is determined by its entries strictly above the diagonal.
This file constructs the resulting canonical basis indexed by pairs `i < j`,
gives its matrix-unit formula, and computes the dimension as `n.choose 2`.

This file does not compute a congruence determinant or determinant norm, pull
back a determinant form, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix

namespace Matrix

/-- Strictly upper-triangular index pairs for `Fin n`. -/
abbrev StrictUpperPair (n : ℕ) := {q : Fin n × Fin n // q.1 < q.2}

namespace StrictUpperPair

/-- A strict ordered pair determines the corresponding non-diagonal unordered
pair. -/
def toSym2OffDiag (n : ℕ) :
    StrictUpperPair n ≃ {s : Sym2 (Fin n) // ¬s.IsDiag} :=
  let strictToSorted :
      StrictUpperPair n ≃
        {q : {p : Fin n × Fin n // p.1 ≤ p.2} // q.1.1 ≠ q.1.2} :=
    { toFun := fun q => ⟨⟨q.1, q.2.le⟩, ne_of_lt q.2⟩
      invFun := fun q => ⟨q.1.1, lt_of_le_of_ne q.1.2 q.2⟩
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  strictToSorted.trans <|
    (Sym2.sortEquiv (α := Fin n)).symm.subtypeEquiv fun q => by
      change (q.1.1 ≠ q.1.2) ↔ ¬(Sym2.mk q.1.1 q.1.2).IsDiag
      rw [Sym2.mk_isDiag_iff]

theorem card (n : ℕ) : Fintype.card (StrictUpperPair n) = n.choose 2 := by
  rw [Fintype.card_congr (toSym2OffDiag n), Sym2.card_subtype_not_diag,
    Fintype.card_fin]

end StrictUpperPair

section Coordinates

variable {K : Type*} [Field K] (hK : ringChar K ≠ 2)
variable {n : ℕ}

/-- Reconstruct a skew-symmetric matrix from its strictly upper-triangular
coordinates. -/
def skewSymmetricMatrixOfUpperCoordinates
    (c : StrictUpperPair n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if hij : i < j then c ⟨(i, j), hij⟩
    else if hji : j < i then -c ⟨(j, i), hji⟩
    else 0

theorem skewSymmetricMatrixOfUpperCoordinates_mem
    (c : StrictUpperPair n → K) :
    skewSymmetricMatrixOfUpperCoordinates c ∈
      skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) := by
  change (skewSymmetricMatrixOfUpperCoordinates c)ᵀ =
    -skewSymmetricMatrixOfUpperCoordinates c
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewSymmetricMatrixOfUpperCoordinates, hij, not_lt_of_ge hij.le]
  · subst j
    simp [skewSymmetricMatrixOfUpperCoordinates]
  · simp [skewSymmetricMatrixOfUpperCoordinates, hij, not_lt_of_ge hij.le]

/-- The linear equivalence recording the entries strictly above the diagonal
of a skew-symmetric matrix. -/
def skewSymmetricUpperCoordinateEquiv :
    skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) ≃ₗ[K]
      (StrictUpperPair n → K) where
  toFun Y q := (Y : Matrix (Fin n) (Fin n) K) q.1.1 q.1.2
  invFun c :=
    ⟨skewSymmetricMatrixOfUpperCoordinates c,
      skewSymmetricMatrixOfUpperCoordinates_mem c⟩
  map_add' Y Z := rfl
  map_smul' a Y := rfl
  left_inv Y := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [skewSymmetricMatrixOfUpperCoordinates, hij]
    · subst j
      have hdiag := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) Y.2
      have hneg : -(Y : Matrix (Fin n) (Fin n) K) i i =
          (Y : Matrix (Fin n) (Fin n) K) i i := by
        simpa only [transpose_apply, neg_apply] using hdiag.symm
      have hz : (Y : Matrix (Fin n) (Fin n) K) i i = 0 :=
        (Ring.eq_self_iff_eq_zero_of_char_ne_two hK).mp hneg
      simp [skewSymmetricMatrixOfUpperCoordinates, hz]
    · have hentry := congrArg
        (fun M : Matrix (Fin n) (Fin n) K => M j i) Y.2
      simp only [transpose_apply, neg_apply] at hentry
      simp [skewSymmetricMatrixOfUpperCoordinates, hij,
        not_lt_of_ge hij.le, hentry]
  right_inv c := by
    funext q
    simp [skewSymmetricMatrixOfUpperCoordinates, q.2]

/-- The canonical basis of skew-symmetric matrices, indexed by pairs `i < j`. -/
def skewSymmetricBasis :
    Module.Basis (StrictUpperPair n) K
      (skewSymmetricMatricesSubmodule (R := K) (ι := Fin n)) :=
  (Pi.basisFun K (StrictUpperPair n)).map
    (skewSymmetricUpperCoordinateEquiv hK).symm

@[simp]
theorem skewSymmetricBasis_apply_coe (q : StrictUpperPair n) :
    ((skewSymmetricBasis hK q :
        skewSymmetricMatricesSubmodule (R := K) (ι := Fin n)) :
      Matrix (Fin n) (Fin n) K) =
      Matrix.single q.1.1 q.1.2 1 - Matrix.single q.1.2 q.1.1 1 := by
  simp only [skewSymmetricBasis, Module.Basis.map_apply,
    Pi.basisFun_apply]
  change skewSymmetricMatrixOfUpperCoordinates (Pi.single q (1 : K)) =
    Matrix.single q.1.1 q.1.2 1 - Matrix.single q.1.2 q.1.1 1
  ext i j
  have strictPair_eq_iff (a b : Fin n) (hab : a < b) :
      (⟨(a, b), hab⟩ : StrictUpperPair n) = q ↔
        a = q.1.1 ∧ b = q.1.2 := by
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [skewSymmetricMatrixOfUpperCoordinates, Pi.single_apply,
    Matrix.single_apply, sub_apply, strictPair_eq_iff]
  by_cases hfwd : i = q.1.1 ∧ j = q.1.2
  · obtain ⟨rfl, rfl⟩ := hfwd
    simp [q.2, ne_of_lt q.2]
  by_cases hrev : i = q.1.2 ∧ j = q.1.1
  · obtain ⟨rfl, rfl⟩ := hrev
    simp [q.2, q.2.le, ne_of_lt q.2]
  have hfwd' : ¬(q.1.1 = i ∧ q.1.2 = j) := by
    rintro ⟨hi, hj⟩
    exact hfwd ⟨hi.symm, hj.symm⟩
  have hrev' : ¬(q.1.2 = i ∧ q.1.1 = j) := by
    rintro ⟨hi, hj⟩
    exact hrev ⟨hi.symm, hj.symm⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, hfwd, hfwd', hrev']
  · subst j
    simp [hfwd', hrev']
  · have hcoord : ¬(j = q.1.1 ∧ i = q.1.2) := by
      rintro ⟨hj, hi⟩
      exact hrev ⟨hi, hj⟩
    simp [hij, not_lt_of_ge hij.le, hcoord, hfwd', hrev']

theorem finrank_skewSymmetricMatricesSubmodule
    (hK : ringChar K ≠ 2) :
    Module.finrank K
      (skewSymmetricMatricesSubmodule (R := K) (ι := Fin n)) =
      n.choose 2 := by
  rw [Module.finrank_eq_card_basis (skewSymmetricBasis hK),
    StrictUpperPair.card]

end Coordinates

end Matrix
