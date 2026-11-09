import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInitialLiftBoundary

/-!
# Adjacent-depth raw Gram correction

This module works with the complete raw Gram matrix, rather than its
associated-bilinear quotient.  It defines reduction from depth
`k + 1` to depth `k` and isolates the singular linear term in the Gram defect
of an adjacent correction.  No surjectivity of that linear term is asserted.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Raw Gram-congruence solutions at an arbitrary prime-power depth. -/
abbrev localPadicSpecialOrthogonalRawGramSolution
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :=
  {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
    X ∈ gramCongruenceSolutionMatrices L p k}

set_option backward.isDefEq.respectTransparency false in
/-- Coordinatewise reduction from the adjacent raw Gram solution set at
depth `k + 1` to depth `k`. -/
def localPadicSpecialOrthogonalRawGramSolutionSuccReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalRawGramSolution p (k + 1) →
      L.localPadicSpecialOrthogonalRawGramSolution p k := by
  let hpow : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)
  let f : ZMod (p ^ (k + 1)) →+* ZMod (p ^ k) := ZMod.castHom hpow _
  intro X
  refine ⟨X.1.map f, (mem_gramCongruenceSolutionMatrices_iff).2 ?_⟩
  have hX := (mem_gramCongruenceSolutionMatrices_iff).1 X.2
  have h := congrArg (RingHom.mapMatrix f) hX
  rw [(RingHom.mapMatrix f).map_mul
    (X.1ᵀ * matrixMod L.polarGramMatrix (primePowModulus p (k + 1))) X.1,
    (RingHom.mapMatrix f).map_mul X.1ᵀ
      (matrixMod L.polarGramMatrix (primePowModulus p (k + 1)))] at h
  change
    (X.1ᵀ).map f *
        (matrixMod L.polarGramMatrix (primePowModulus p (k + 1))).map f *
        X.1.map f =
      (matrixMod L.polarGramMatrix (primePowModulus p (k + 1))).map f at h
  rw [Matrix.transpose_map] at h
  have hf (z : ℤ) :
      f (z : ZMod (p ^ (k + 1))) = (z : ZMod (p ^ k)) := by
    rw [ZMod.castHom_apply]
    exact ZMod.cast_intCast hpow z
  have hfun :
      (⇑f ∘ (Int.cast : ℤ → ZMod (p ^ (k + 1)))) =
        (Int.cast : ℤ → ZMod (p ^ k)) := by
    funext z
    exact hf z
  simp only [matrixMod, Matrix.map_map] at h
  rw [hfun] at h
  simpa [matrixMod, f, hpow, primePowModulus] using h

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem localPadicSpecialOrthogonalRawGramSolutionSuccReduction_val
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p (k + 1)) :
    (L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p k X).1 =
      X.1.map
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) :=
  by
    unfold localPadicSpecialOrthogonalRawGramSolutionSuccReduction
    with_reducible_and_instances rfl

/-- The canonical entrywise lift of a raw depth-`k` matrix to depth `k+1`,
using the standard natural representative of every residue entry. -/
def localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k) :
    Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1))) :=
  fun i j => (X.1 i j).val

/-- The canonical raw lift reduces to the prescribed complete matrix modulo
`p^k`. -/
theorem localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix_reduces
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k) :
    (L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X).map
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) =
      X.1 := by
  ext i j
  change
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)))
        ((X.1 i j).val : ZMod (p ^ (k + 1))) = X.1 i j
  rw [ZMod.castHom_apply]
  calc
    ZMod.cast ((X.1 i j).val : ZMod (p ^ (k + 1))) =
        ((X.1 i j).val : ZMod (p ^ k)) := by
      exact ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ k)) _
    _ = X.1 i j := ZMod.natCast_zmod_val _

/-- A depth-`k+1` raw matrix retaining `X` and corrected by the literal
multiple `p^k H`. -/
def localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) :
    Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1))) :=
  L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X +
    ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) • H

/-- Every corrected matrix reduces to the prescribed complete initial
matrix. -/
theorem localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix_reduces
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) :
    (L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H).map
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) =
      X.1 := by
  let hpow : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)
  let f : ZMod (p ^ (k + 1)) →+* ZMod (p ^ k) := ZMod.castHom hpow _
  have hraw :=
    L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix_reduces p k X
  have hscalar : f ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hpow]
    exact (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ k)).2 dvd_rfl
  ext i j
  have hrawij := congrFun (congrFun hraw i) j
  have hrawij' :
      f (L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X i j) =
        X.1 i j := by
    simpa [f, hpow] using hrawij
  change
    f ((L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X) i j +
      ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * H i j) = X.1 i j
  rw [map_add, map_mul, hrawij', hscalar, zero_mul, add_zero]

/-- A literal adjacent correction is valid when its corrected matrix is a raw
Gram solution at depth `k+1`. -/
def IsLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) : Prop :=
  L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H ∈
    gramCongruenceSolutionMatrices L p (k + 1)

end PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The linear part of the Gram defect contributed by a correction matrix.
It remains meaningful when the Gram pairing is singular. -/
def rawGramAdjacentCorrectionLinearMap
    (G X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun H := Hᵀ * G * X + Xᵀ * G * H
  map_add' H K := by
    rw [Matrix.transpose_add]
    noncomm_ring
  map_smul' a H := by
    simp only [RingHom.id_apply]
    rw [Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    module

@[simp] theorem rawGramAdjacentCorrectionLinearMap_apply
    (G X H : Matrix (Fin n) (Fin n) R) :
    rawGramAdjacentCorrectionLinearMap G X H =
      Hᵀ * G * X + Xᵀ * G * H :=
  rfl

/-- Exact Gram-defect expansion for an adjacent correction `X + tH`.  The
middle summand is the singular linear correction map; the final quadratic
term is kept in full. -/
theorem rawGram_adjacent_correction_defect_expansion
    (G X H : Matrix (Fin n) (Fin n) R) (t : R) :
    (X + t • H)ᵀ * G * (X + t • H) - G =
      (Xᵀ * G * X - G) +
        t • rawGramAdjacentCorrectionLinearMap G X H +
          t ^ 2 • (Hᵀ * G * H) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul,
    rawGramAdjacentCorrectionLinearMap_apply]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [pow_two]
  module

/-- A corrected raw lift preserves `G` exactly when its old defect plus the
linear and quadratic correction terms vanishes. -/
theorem rawGram_adjacent_correction_preserves_iff
    (G X H : Matrix (Fin n) (Fin n) R) (t : R) :
    (X + t • H)ᵀ * G * (X + t • H) = G ↔
      (Xᵀ * G * X - G) +
        t • rawGramAdjacentCorrectionLinearMap G X H +
          t ^ 2 • (Hᵀ * G * H) = 0 := by
  constructor
  · intro h
    rw [← rawGram_adjacent_correction_defect_expansion]
    exact sub_eq_zero.mpr h
  · intro h
    apply sub_eq_zero.mp
    rw [rawGram_adjacent_correction_defect_expansion]
    exact h

/-- At positive depth, the quadratic part of a correction divisible by `p^k`
vanishes modulo `p^(k+1)`. -/
theorem rawGram_adjacent_correction_quadratic_term_eq_zero_zmod
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 0 < k)
    (G H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) :
    ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) ^ 2 • (Hᵀ * G * H) = 0 := by
  have hscalar :
      ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    rw [← Nat.pow_mul]
    exact pow_dvd_pow p (by omega)
  rw [hscalar]
  exact zero_smul _ _

/-- At positive depth, an adjacent correction by `p^k H` preserves the Gram
matrix exactly when the old defect plus the singular linear correction term
vanishes modulo `p^(k+1)`. -/
theorem rawGram_adjacent_correction_preserves_iff_linearized_zmod
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 0 < k)
    (G X H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) :
    (X + ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) • H)ᵀ * G *
          (X + ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) • H) = G ↔
      (Xᵀ * G * X - G) +
          ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) •
            rawGramAdjacentCorrectionLinearMap G X H = 0 := by
  rw [rawGram_adjacent_correction_preserves_iff]
  rw [rawGram_adjacent_correction_quadratic_term_eq_zero_zmod p k hk G H,
    add_zero]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- At positive depth, validity of a raw correction is exactly the
adjacent singular linear correction equation.  The defect of the initial matrix is kept
over `ZMod (p^(k+1))`; cancelling its known factor `p^k` to obtain a residue-
field equation is a separate arithmetic step. -/
theorem isLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection_iff_linearized
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hk : 0 < k)
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1)))) :
    L.IsLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection p k X H ↔
      let G :=
        L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ (k + 1))))
      let Xlift :=
        L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X
      (Xliftᵀ * G * Xlift - G) +
          ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) •
            Matrix.rawGramAdjacentCorrectionLinearMap G Xlift H = 0 := by
  rw [IsLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection]
  rw [mem_gramCongruenceSolutionMatrices_iff (L := L) (p := p) (k := k + 1)
    (X := L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H)]
  change
    (L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H)ᵀ *
          L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ (k + 1)))) *
        L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H =
        L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ (k + 1)))) ↔ _
  rw [localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix]
  exact
    Matrix.rawGram_adjacent_correction_preserves_iff_linearized_zmod
      p k hk
        (L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ (k + 1)))))
        (L.localPadicSpecialOrthogonalRawGramSolutionSuccRawLiftMatrix p k X) H

/-- Every valid literal correction supplies an actual adjacent raw solution
whose complete reduction is the prescribed matrix. -/
def localPadicSpecialOrthogonalRawGramSolutionSuccOfCorrection
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1))))
    (hH : L.IsLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection p k X H) :
    L.localPadicSpecialOrthogonalRawGramSolution p (k + 1) :=
  ⟨L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix p k X H, hH⟩

@[simp] theorem localPadicSpecialOrthogonalRawGramSolutionSuccOfCorrection_reduces
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (H : Matrix (Fin n) (Fin n) (ZMod (p ^ (k + 1))))
    (hH : L.IsLocalPadicSpecialOrthogonalRawGramSolutionSuccCorrection p k X H) :
    L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p k
        (L.localPadicSpecialOrthogonalRawGramSolutionSuccOfCorrection p k X H hH) = X := by
  apply Subtype.ext
  exact
    L.localPadicSpecialOrthogonalRawGramSolutionSuccCorrectedMatrix_reduces p k X H

end PositiveDefiniteIntegralLattice
