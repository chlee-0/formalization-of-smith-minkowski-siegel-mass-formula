import SMSFormula.Applications.Unimodular.DirectPeeling.PeelingCore
import SMSFormula.Applications.Unimodular.ModEightTransport.FiniteCertificates

/-!
The terminal 2-dimensional case uses the already checked binary certificates.
Unlike an H/A-word normalization, no A+A cancellation is used in the induction.
-/

noncomputable section
open Matrix

namespace TypeIIDirectPeeling
open TypeIIModEightCertificates

/-- Parametrize an even residue without dividing in the ring. -/
theorem even8_parameter : ∀ u : R, Even8 u → ∃ a : Fin 4, u = 2 * (a.val : R) := by
  decide

/-- Split binary determinant forces the off-diagonal entry to be odd. -/
theorem split_binary_off_diagonal :
    ∀ u v w : R, Even8 u → Even8 v → u * v - w * w = -1 →
      ∃ b : Fin 4, w = 2 * (b.val : R) + 1 := by
  decide

/-- A 64-case scalar check selects H, not A, at the terminal determinant. -/
theorem split_binary_target :
    ∀ a b c : Fin 4, (binary a b c).det = (-1 : R) → binaryTarget a c = H := by
  decide

/-- Reuse the old checked binary congruence, specialized to determinant -1. -/
def parametrizedBinarySplitCertificate (a b c : Fin 4)
    (hdet : (binary a b c).det = (-1 : R)) :
    GramCongruenceCertificate (binary a b c) H := by
  have ht := split_binary_target a b c hdet
  simpa only [ht] using binaryGramCertificate a b c

/-- The terminal certificate for an arbitrary binary base, without a supplied
classification. -/
def terminalBinaryCertificate (G : Matrix (Fin 2) (Fin 2) R)
    (hs : G.IsSymm) (he : ∀ i, Even8 (G i i)) (hdet : G.det = -1) :
    GramCongruenceCertificate G H := by
  classical
  have h10 : G 1 0 = G 0 1 := (hs.apply 1 0).symm
  have hd : G 0 0 * G 1 1 - G 0 1 * G 0 1 = -1 := by
    simpa only [Matrix.det_fin_two, h10] using hdet
  let a : Fin 4 := Classical.choose (even8_parameter (G 0 0) (he 0))
  have ha : G 0 0 = 2 * (a.val : R) :=
    Classical.choose_spec (even8_parameter (G 0 0) (he 0))
  let c : Fin 4 := Classical.choose (even8_parameter (G 1 1) (he 1))
  have hc : G 1 1 = 2 * (c.val : R) :=
    Classical.choose_spec (even8_parameter (G 1 1) (he 1))
  let b : Fin 4 := Classical.choose (split_binary_off_diagonal (G 0 0) (G 1 1) (G 0 1)
    (he 0) (he 1) hd)
  have hb : G 0 1 = 2 * (b.val : R) + 1 :=
    Classical.choose_spec (split_binary_off_diagonal (G 0 0) (G 1 1) (G 0 1)
      (he 0) (he 1) hd)
  have hG : G = binary a b c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [binary, ha, hb, hc, h10]
  have hdet' : (binary a b c).det = (-1 : R) := by
    simpa [hG] using hdet
  exact hG ▸ parametrizedBinarySplitCertificate a b c hdet'

/-- The correct induction invariant alternates with the half-rank. Never
recurse on the false requirement that the residual determinant stay one. -/
theorem residual_split_discriminant (m : ℕ) (d : R)
    (h : (-1 : R) * d = (-1 : R) ^ (m + 1)) :
    d = (-1 : R) ^ m := by
  calc
    d = (-1 : R) * ((-1 : R) * d) := by ring
    _ = (-1 : R) * (-1 : R) ^ (m + 1) := by rw [h]
    _ = (-1 : R) ^ m := by rw [pow_succ]; ring

#assert_standard_axioms even8_parameter
#assert_standard_axioms split_binary_off_diagonal
#assert_standard_axioms split_binary_target
#assert_standard_axioms parametrizedBinarySplitCertificate
#assert_standard_axioms terminalBinaryCertificate
#assert_standard_axioms residual_split_discriminant

end TypeIIDirectPeeling
