import SMSFormula.Applications.Unimodular.DirectPeeling.SplitStep
import SMSFormula.Applications.Unimodular.DirectPeeling.BinaryEndgame

/-!
# Direct Type II hyperbolic peeling: recursive all-H certificates

This module defines the recursive certificate family for the direct
hyperbolic-peeling route.  It proves that the one-step splitter can be iterated
down to the checked binary endgame, producing a finite Gram-congruence certificate
to some iterated hyperbolic-plane target.  The reindexing to the concrete
`hyperbolicSplitTarget k` used by the mass assembly is a separate step.
-/

noncomputable section

namespace TypeIIDirectPeeling
open TypeIIModEightCertificates

/-- A target matrix built only from hyperbolic planes, allowing arbitrary finite
reindexing at each recursive split. -/
inductive AllHTarget : {ι : Type} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι R → Prop where
  | nil : AllHTarget (1 : Matrix (Fin 0) (Fin 0) R)
  | single : AllHTarget H
  | cons {ι : Type} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι R}
      (hT : AllHTarget T) : AllHTarget (sumBlockMatrix H T)
  | reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (e : ι ≃ κ) {T : Matrix ι ι R} (hT : AllHTarget T) :
      AllHTarget (Matrix.reindex e e T)

/-- A finite certificate from a matrix to an iterated all-hyperbolic target. -/
structure RecursiveAllHCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι R) where
  target : Matrix ι ι R
  targetAllH : AllHTarget target
  certificate : GramCongruenceCertificate G target

/-- The checked binary endgame is the base case of the recursive all-H certificate. -/
def terminalRecursiveAllHCertificateData (G : Matrix (Fin 2) (Fin 2) R)
    (hs : G.IsSymm) (he : ∀ i, Even8 (G i i)) (hdet : G.det = -1) :
    RecursiveAllHCertificateData G where
  target := H
  targetAllH := AllHTarget.single
  certificate := terminalBinaryCertificate G hs he hdet

/-- One selected split step composes a recursively produced residual all-H certificate
back to an all-H certificate for the original matrix. -/
def RecursiveSplitStepData.allHCertificate {n m : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (D : RecursiveSplitStepData (n := n) (m := m) G)
    (Cres : RecursiveAllHCertificateData (splitPairResidualFinMatrix G D.x D.y D.hrj)) :
    RecursiveAllHCertificateData G where
  target := Matrix.reindex (splitPairIndexEquiv D.hrj) (splitPairIndexEquiv D.hrj)
    (sumBlockMatrix H
      (Matrix.reindex (remainingIndexFinEquiv D.hrj).symm
        (remainingIndexFinEquiv D.hrj).symm Cres.target))
  targetAllH := AllHTarget.reindex (splitPairIndexEquiv D.hrj)
    (AllHTarget.cons
      (AllHTarget.reindex (remainingIndexFinEquiv D.hrj).symm Cres.targetAllH))
  certificate := D.certificate Cres.certificate

/-- Recursive direct-H peeling produces a finite certificate to an iterated hyperbolic
plane target in every positive even half-rank satisfying the alternating determinant
sign invariant. -/
theorem exists_recursiveAllHCertificateData :
    ∀ m : ℕ, 1 ≤ m →
      ∀ (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R), G.IsSymm →
        (∀ i, Even8 (G i i)) → G.det = (-1 : R) ^ m →
        Nonempty (RecursiveAllHCertificateData G) := by
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro hm G hsymm hdiag hdet
      cases m with
      | zero =>
          refine ⟨terminalRecursiveAllHCertificateData G hsymm hdiag ?_⟩
          simpa using hdet
      | succ m =>
          have hthree : 3 ≤ 2 * Nat.succ (Nat.succ m) := by omega
          obtain ⟨V, hGV⟩ := exists_right_inverse_of_det_sign G hdet
          let D := recursiveSplitStepDataOfThreeLe
            (n := 2 * Nat.succ (Nat.succ m)) (m := Nat.succ m)
            hthree G V hGV hsymm hdiag hdet
          let Gres := splitPairResidualFinMatrix G D.x D.y D.hrj
          have hsymm_res : (show Matrix (Fin (2 * Nat.succ m)) (Fin (2 * Nat.succ m)) R from Gres).IsSymm := by
            simpa [Gres, Nat.mul_succ] using D.residualSymm
          have hdiag_res : ∀ i : Fin (2 * Nat.succ m),
              Even8 ((show Matrix (Fin (2 * Nat.succ m)) (Fin (2 * Nat.succ m)) R from Gres) i i) := by
            simpa [Gres, Nat.mul_succ] using D.residualDiagEven
          have hdet_res : (show Matrix (Fin (2 * Nat.succ m)) (Fin (2 * Nat.succ m)) R from Gres).det =
              (-1 : R) ^ Nat.succ m := by
            simpa [Gres, Nat.mul_succ] using D.residualDetSign
          obtain ⟨Cres⟩ := ih (by omega)
            (show Matrix (Fin (2 * Nat.succ m)) (Fin (2 * Nat.succ m)) R from Gres)
            hsymm_res hdiag_res hdet_res
          refine ⟨D.allHCertificate ?_⟩
          simpa [Gres, Nat.mul_succ] using Cres

/-- Chosen recursive direct-H peeling certificate data. -/
def recursiveAllHCertificateData (m : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ m) :
    RecursiveAllHCertificateData G :=
  Classical.choice (exists_recursiveAllHCertificateData m hm G hsymm hdiag hdet)

#assert_standard_axioms AllHTarget
#assert_standard_axioms RecursiveAllHCertificateData
#assert_standard_axioms terminalRecursiveAllHCertificateData
#assert_standard_axioms RecursiveSplitStepData.allHCertificate
#assert_standard_axioms exists_recursiveAllHCertificateData
#assert_standard_axioms recursiveAllHCertificateData

end TypeIIDirectPeeling
