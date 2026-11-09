import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import SMSFormula.StandardAxiomsGuard

/-!
# Finite matrix moves for odd unimodular normal forms

Proof scripts for small universal certificates, not an assertion that a global
lattice classification has been compiled. The authoring environment did not
contain Lean/Lake. All finite decisions below use proof-producing `decide`.
-/

namespace UnimodularGenusClosure

abbrev R8 := ZMod 8
abbrev M2 := Matrix (Fin 2) (Fin 2) R8
abbrev M3 := Matrix (Fin 3) (Fin 3) R8
abbrev M4 := Matrix (Fin 4) (Fin 4) R8

def oddUnit (a : Fin 4) : R8 := 2 * (a.val : R8) + 1

def diagonalPair (a b : R8) : M2 := !![a, 0; 0, b]

def pairMove (a b : R8) : M2 := !![1, -2 * b; 2, a]

def pairMoveInverse (a b : R8) : M2 :=
  (a + 4 * b) • !![a, 2 * b; -2, 1]

/-- Flip the high bits of any two odd coefficients, not only equal residues. -/
theorem pairMove_certificate (a b : Fin 4) :
    let x := oddUnit a
    let y := oddUnit b
    let P := pairMove x y
    let V := pairMoveInverse x y
    P.transpose * diagonalPair x y * P = diagonalPair (x + 4) (y + 4) ∧
      P * V = 1 ∧ V * P = 1 := by
  fin_cases a <;> fin_cases b <;> decide

def quaternionMatrixZ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, -1, -1;
     1,  0, -1,  1;
     1,  1,  0, -1;
     1, -1,  1,  0]

/-- This identity is over the integers, before reduction. -/
theorem quaternionMatrixZ_norm :
    quaternionMatrixZ.transpose * quaternionMatrixZ = (3 : ℤ) • 1 := by
  decide

def quaternionMatrix : M4 :=
  !![0, -1, -1, -1;
     1,  0, -1,  1;
     1,  1,  0, -1;
     1, -1,  1,  0]

def quaternionInverse : M4 := (3 : R8) • quaternionMatrix.transpose

/-- Four coefficients equal to three become four ones modulo eight. -/
theorem quaternion_certificate :
    quaternionMatrix.transpose * ((3 : R8) • (1 : M4)) * quaternionMatrix = 1 ∧
      quaternionMatrix * quaternionInverse = 1 ∧
      quaternionInverse * quaternionMatrix = 1 := by
  decide

def tripleInput (a b c u : Fin 4) : M3 :=
  !![oddUnit a, 0, 0;
     0, 2 * (b.val : R8), oddUnit u;
     0, oddUnit u, 2 * (c.val : R8)]

def tripleStart : M3 := !![1, 1, 1; 1, 0, 0; 0, 1, 0]
def tripleStartInverse : M3 := !![0, 1, 0; 0, 0, 1; 1, -1, -1]

def firstElimination (A : M3) : M3 :=
  !![1, -A 0 0 * A 0 1, -A 0 0 * A 0 2;
     0, 1, 0;
     0, 0, 1]

def firstEliminationInverse (A : M3) : M3 :=
  !![1, A 0 0 * A 0 1, A 0 0 * A 0 2;
     0, 1, 0;
     0, 0, 1]

def secondElimination (A : M3) : M3 :=
  !![1, 0, 0; 0, 1, -A 1 1 * A 1 2; 0, 0, 1]

def secondEliminationInverse (A : M3) : M3 :=
  !![1, 0, 0; 0, 1, A 1 1 * A 1 2; 0, 0, 1]

def tripleMiddle (G : M3) : M3 := tripleStart.transpose * G * tripleStart

def tripleAfterFirst (G : M3) : M3 :=
  let A := tripleMiddle G
  (firstElimination A).transpose * A * firstElimination A

def tripleMove (G : M3) : M3 :=
  tripleStart * firstElimination (tripleMiddle G) *
    secondElimination (tripleAfterFirst G)

def tripleMoveInverse (G : M3) : M3 :=
  secondEliminationInverse (tripleAfterFirst G) *
    firstEliminationInverse (tripleMiddle G) * tripleStartInverse

set_option maxHeartbeats 4000000 in
/-- One odd line absorbs any regular even binary block. The resulting three
coefficients are units; the inverse is supplied, not inferred from a count. -/
theorem tripleMove_certificate (a b c u : Fin 4) :
    let G := tripleInput a b c u
    let P := tripleMove G
    let V := tripleMoveInverse G
    let D := P.transpose * G * P
    (∀ i j : Fin 3, i ≠ j → D i j = 0) ∧
      (∀ i : Fin 3, D i i * D i i = 1) ∧
      P * V = 1 ∧ V * P = 1 := by
  revert a b c u
  decide +kernel

#assert_standard_axioms pairMove_certificate
#assert_standard_axioms quaternionMatrixZ_norm
#assert_standard_axioms quaternion_certificate
#assert_standard_axioms tripleMove_certificate

end UnimodularGenusClosure
