import SMSFormula.Applications.Unimodular.DirectPeeling.RecursiveAllH
import SMSFormula.Applications.Unimodular.ModEightTransport.SplitTarget

/-!
# Direct Type II hyperbolic peeling: target bridge layer

This module starts the final target-identification layer for the direct-H
route.  The recursive peeling theorem produces certificates to arbitrary
`AllHTarget`s.  Here we introduce the canonical flat all-H target on `Fin (2*m)`
and record the first reusable facts needed to reindex/reassociate recursive
outputs toward the concrete `hyperbolicSplitTarget k` used by the mass assembly.
-/

noncomputable section

namespace TypeIIDirectPeeling
open TypeIIModEightCertificates

/-- The canonical flat target made of `m` hyperbolic planes, indexed by `Fin (2*m)`.
It is intentionally defined by the same one-plane-at-a-time recursion as
`AllHTarget.cons`; later bridge lemmas regroup four consecutive planes into the
`H4` blocks used by `hyperbolicSplitTarget`. -/
def flatAllHTarget : (m : ℕ) → Matrix (Fin (2 * m)) (Fin (2 * m)) R
  | 0 => 1
  | m + 1 =>
      Matrix.reindex
        ((finSumFinEquiv : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 + 2 * m)).trans
          (finCongr (by omega : 2 + 2 * m = 2 * (m + 1))))
        ((finSumFinEquiv : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 + 2 * m)).trans
          (finCongr (by omega : 2 + 2 * m = 2 * (m + 1))))
        (sumBlockMatrix H (flatAllHTarget m))

/-- The canonical flat target is itself an `AllHTarget`. -/
theorem flatAllHTarget_allH (m : ℕ) : AllHTarget (flatAllHTarget m) := by
  induction m with
  | zero =>
      simpa [flatAllHTarget] using AllHTarget.nil
  | succ m ih =>
      simpa [flatAllHTarget] using
        (AllHTarget.reindex
          ((finSumFinEquiv : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 + 2 * m)).trans
            (finCongr (by omega : 2 + 2 * m = 2 * (m + 1))))
          (AllHTarget.cons ih))

/-- The one-plane flat target is literally the checked binary hyperbolic plane. -/
theorem flatAllHTarget_one_eq_H : flatAllHTarget 1 = H := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Four consecutive flat hyperbolic planes agree with the generated `H4` block. -/
theorem flatAllHTarget_four_eq_H4 : flatAllHTarget 4 = H4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- In rank eight, the canonical flat all-H target is the concrete split target. -/
theorem flatAllHTarget_four_eq_hyperbolicSplitTarget_one :
    flatAllHTarget 4 = TypeIIModEightCertificates.hyperbolicSplitTarget 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide



/-- The block-coordinate equivalence used by the recursive definition of
`flatAllHTarget`. -/
def flatAllHTargetStepEquiv (m : ℕ) : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 * (m + 1)) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 + 2 * m)).trans
    (finCongr (by omega : 2 + 2 * m = 2 * (m + 1)))

/-- The entrywise adjacent-pair hyperbolic target on `Fin n`: coordinates `2*r`
and `2*r+1` pair with coefficient one, and all other entries vanish.  This is
the arithmetic normal form used to compare flat all-H targets with the concrete
`hyperbolicSplitTarget`. -/
def adjacentHyperbolicTarget (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i.val / 2 = j.val / 2 ∧ i.val ≠ j.val then 1 else 0

/-- The basic hyperbolic plane is the adjacent-pair target in two coordinates. -/
theorem H_eq_adjacentHyperbolicTarget_two : H = adjacentHyperbolicTarget 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The recursively defined flat target is exactly the adjacent-pair target. -/
theorem flatAllHTarget_eq_adjacentHyperbolicTarget (m : ℕ) :
    flatAllHTarget m = adjacentHyperbolicTarget (2 * m) := by
  induction m with
  | zero =>
      ext i j
      fin_cases i
  | succ m ih =>
      ext i j
      obtain ⟨i', rfl⟩ := (flatAllHTargetStepEquiv m).surjective i
      obtain ⟨j', rfl⟩ := (flatAllHTargetStepEquiv m).surjective j
      cases i' with
      | inl a =>
          cases j' with
          | inl b =>
              simp [flatAllHTarget, flatAllHTargetStepEquiv, adjacentHyperbolicTarget]
              simpa [adjacentHyperbolicTarget] using
                congrFun (congrFun H_eq_adjacentHyperbolicTarget_two a) b
          | inr b =>
              simp [flatAllHTarget, flatAllHTargetStepEquiv, adjacentHyperbolicTarget]
              omega
      | inr a =>
          cases j' with
          | inl b =>
              simp [flatAllHTarget, flatAllHTargetStepEquiv, adjacentHyperbolicTarget]
              omega
          | inr b =>
              simp [flatAllHTarget, flatAllHTargetStepEquiv, adjacentHyperbolicTarget, ih]

/-- The generated four-plane block is the adjacent-pair target in eight coordinates. -/
theorem H4_eq_adjacentHyperbolicTarget_eight : H4 = adjacentHyperbolicTarget 8 := by
  rw [← flatAllHTarget_four_eq_H4, flatAllHTarget_eq_adjacentHyperbolicTarget]

/-- In rank `8*k`, the flat all-H target is the adjacent-pair target after the
canonical arithmetic reindexing. -/
theorem flatAllHTarget_four_mul_reindex_eq_adjacentHyperbolicTarget (k : ℕ) :
    Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
      (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)) =
    adjacentHyperbolicTarget (8 * k) := by
  rw [flatAllHTarget_eq_adjacentHyperbolicTarget]
  ext i j
  simp [adjacentHyperbolicTarget]


/-- The block-coordinate equivalence used by the recursive definition of
`hyperbolicSplitTarget`. -/
def hyperbolicSplitTargetStepEquiv (k : ℕ) :
    Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * (k + 1)) :=
  (finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)).trans
    (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))

@[simp] theorem hyperbolicSplitTargetStepEquiv_inl_val (k : ℕ) (a : Fin (8 * k)) :
    ((hyperbolicSplitTargetStepEquiv k) (Sum.inl a)).val = a.val := by
  rfl

@[simp] theorem hyperbolicSplitTargetStepEquiv_inr_val (k : ℕ) (a : Fin 8) :
    ((hyperbolicSplitTargetStepEquiv k) (Sum.inr a)).val = 8 * k + a.val := by
  rfl

/-- In the grouped split target, the upper-left block evaluates to the previous
split target after the step equivalence. -/
theorem reindexed_blockSumMatrix_step_inl_inl (k : ℕ)
    (A : Matrix (Fin (8 * k)) (Fin (8 * k)) R) (B : Matrix (Fin 8) (Fin 8) R)
    (a b : Fin (8 * k)) :
    (Matrix.reindex (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (PositiveDefiniteIntegralLattice.blockSumMatrix A B))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl b)) = A a b := by
  simp [hyperbolicSplitTargetStepEquiv, PositiveDefiniteIntegralLattice.blockSumMatrix]
  calc
    Matrix.fromBlocks A 0 0 B
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inl a))))
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inl b)))) =
      Matrix.fromBlocks A 0 0 B (Sum.inl a) (Sum.inl b) := by congr <;> simp
    _ = A a b := Matrix.fromBlocks_apply₁₁ A 0 0 B a b

/-- In the grouped split target, the upper-right block is zero after the step equivalence. -/
theorem reindexed_blockSumMatrix_step_inl_inr (k : ℕ)
    (A : Matrix (Fin (8 * k)) (Fin (8 * k)) R) (B : Matrix (Fin 8) (Fin 8) R)
    (a : Fin (8 * k)) (b : Fin 8) :
    (Matrix.reindex (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (PositiveDefiniteIntegralLattice.blockSumMatrix A B))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr b)) = 0 := by
  simp [hyperbolicSplitTargetStepEquiv, PositiveDefiniteIntegralLattice.blockSumMatrix]
  calc
    Matrix.fromBlocks A 0 0 B
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inl a))))
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inr b)))) =
      Matrix.fromBlocks A 0 0 B (Sum.inl a) (Sum.inr b) := by congr <;> simp
    _ = 0 := Matrix.fromBlocks_apply₁₂ A 0 0 B a b

/-- In the grouped split target, the lower-left block is zero after the step equivalence. -/
theorem reindexed_blockSumMatrix_step_inr_inl (k : ℕ)
    (A : Matrix (Fin (8 * k)) (Fin (8 * k)) R) (B : Matrix (Fin 8) (Fin 8) R)
    (a : Fin 8) (b : Fin (8 * k)) :
    (Matrix.reindex (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (PositiveDefiniteIntegralLattice.blockSumMatrix A B))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl b)) = 0 := by
  simp [hyperbolicSplitTargetStepEquiv, PositiveDefiniteIntegralLattice.blockSumMatrix]
  calc
    Matrix.fromBlocks A 0 0 B
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inr a))))
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inl b)))) =
      Matrix.fromBlocks A 0 0 B (Sum.inr a) (Sum.inl b) := by congr <;> simp
    _ = 0 := Matrix.fromBlocks_apply₂₁ A 0 0 B a b

/-- In the grouped split target, the lower-right block evaluates to the new `H4`
block after the step equivalence. -/
theorem reindexed_blockSumMatrix_step_inr_inr (k : ℕ)
    (A : Matrix (Fin (8 * k)) (Fin (8 * k)) R) (B : Matrix (Fin 8) (Fin 8) R)
    (a b : Fin 8) :
    (Matrix.reindex (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
      (PositiveDefiniteIntegralLattice.blockSumMatrix A B))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr b)) = B a b := by
  simp [hyperbolicSplitTargetStepEquiv, PositiveDefiniteIntegralLattice.blockSumMatrix]
  calc
    Matrix.fromBlocks A 0 0 B
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inr a))))
        (finSumFinEquiv.symm ((Equiv.refl (Fin (8 * k + 8)))
          ((finSumFinEquiv : Fin (8 * k) ⊕ Fin 8 ≃ Fin (8 * k + 8)) (Sum.inr b)))) =
      Matrix.fromBlocks A 0 0 B (Sum.inr a) (Sum.inr b) := by congr <;> simp
    _ = B a b := Matrix.fromBlocks_apply₂₂ A 0 0 B a b

/-- Adjacent-pair target entries do not cross the old/new rank-eight boundary. -/
theorem adjacentHyperbolicTarget_cross_left_zero (k : ℕ) (a : Fin (8 * k)) (b : Fin 8) :
    adjacentHyperbolicTarget (8 * (k + 1))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr b)) = 0 := by
  simp [adjacentHyperbolicTarget]
  omega

/-- Adjacent-pair target entries do not cross the new/old rank-eight boundary. -/
theorem adjacentHyperbolicTarget_cross_right_zero (k : ℕ) (a : Fin 8) (b : Fin (8 * k)) :
    adjacentHyperbolicTarget (8 * (k + 1))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl b)) = 0 := by
  simp [adjacentHyperbolicTarget]
  omega

/-- The old block of the adjacent-pair target is stable under the split-target
step equivalence. -/
theorem adjacentHyperbolicTarget_step_inl_inl (k : ℕ) (a b : Fin (8 * k)) :
    adjacentHyperbolicTarget (8 * (k + 1))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inl b)) =
    adjacentHyperbolicTarget (8 * k) a b := by
  simp [adjacentHyperbolicTarget]

/-- The new `H4` block of the adjacent-pair target is the adjacent target in eight
coordinates. -/
theorem adjacentHyperbolicTarget_step_inr_inr (k : ℕ) (a b : Fin 8) :
    adjacentHyperbolicTarget (8 * (k + 1))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr a))
      ((hyperbolicSplitTargetStepEquiv k) (Sum.inr b)) =
    adjacentHyperbolicTarget 8 a b := by
  simp [adjacentHyperbolicTarget]
  by_cases h : (8 * k + a.val) / 2 = (8 * k + b.val) / 2 ∧ ¬a.val = b.val
  · have h' : a.val / 2 = b.val / 2 ∧ ¬a.val = b.val := by omega
    simp [h, h']
  · have h' : ¬(a.val / 2 = b.val / 2 ∧ ¬a.val = b.val) := by
      intro h'
      exact h (by omega)
    simp [h, h']

/-- The grouped split target is also the adjacent-pair normal form. -/
theorem hyperbolicSplitTarget_eq_adjacentHyperbolicTarget (k : ℕ) :
    TypeIIModEightCertificates.hyperbolicSplitTarget k = adjacentHyperbolicTarget (8 * k) := by
  induction k with
  | zero =>
      ext i j
      fin_cases i
  | succ k ih =>
      ext i j
      obtain ⟨i', rfl⟩ := (hyperbolicSplitTargetStepEquiv k).surjective i
      obtain ⟨j', rfl⟩ := (hyperbolicSplitTargetStepEquiv k).surjective j
      cases i' with
      | inl a =>
          cases j' with
          | inl b =>
              rw [adjacentHyperbolicTarget_step_inl_inl, ← ih]
              exact reindexed_blockSumMatrix_step_inl_inl k
                (TypeIIModEightCertificates.hyperbolicSplitTarget k) H4 a b
          | inr b =>
              rw [adjacentHyperbolicTarget_cross_left_zero]
              exact reindexed_blockSumMatrix_step_inl_inr k
                (TypeIIModEightCertificates.hyperbolicSplitTarget k) H4 a b
      | inr a =>
          cases j' with
          | inl b =>
              rw [adjacentHyperbolicTarget_cross_right_zero]
              exact reindexed_blockSumMatrix_step_inr_inl k
                (TypeIIModEightCertificates.hyperbolicSplitTarget k) H4 a b
          | inr b =>
              rw [adjacentHyperbolicTarget_step_inr_inr, ← H4_eq_adjacentHyperbolicTarget_eight]
              exact reindexed_blockSumMatrix_step_inr_inr k
                (TypeIIModEightCertificates.hyperbolicSplitTarget k) H4 a b

/-- In rank `8*k`, the flat target reindexed to `Fin (8*k)` is exactly the
concrete split target. -/
theorem flatAllHTarget_four_mul_reindex_eq_hyperbolicSplitTarget (k : ℕ) :
    Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
      (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)) =
    TypeIIModEightCertificates.hyperbolicSplitTarget k := by
  rw [flatAllHTarget_four_mul_reindex_eq_adjacentHyperbolicTarget,
    hyperbolicSplitTarget_eq_adjacentHyperbolicTarget]

/-- The final finite certificate from the reindexed flat all-H target to the
concrete split target. -/
def flatAllHTargetSplitCertificate (k : ℕ) :
    GramCongruenceCertificate
      (Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
        (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k) := by
  rw [flatAllHTarget_four_mul_reindex_eq_hyperbolicSplitTarget]
  exact TypeIIModEightCertificates.reflCertificate
    (TypeIIModEightCertificates.hyperbolicSplitTarget k)

/-- Compose a certificate to the canonical reindexed flat target with the final
flat-to-split target bridge. -/
def splitCertificate_of_flatAllHTarget_certificate (k : ℕ)
    {G : Matrix (Fin (8 * k)) (Fin (8 * k)) R}
    (C : GramCongruenceCertificate G
      (Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
        (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)))) :
    GramCongruenceCertificate G (TypeIIModEightCertificates.hyperbolicSplitTarget k) :=
  C.trans (flatAllHTargetSplitCertificate k)

/-- A certificate to the canonical reindexed flat target is enough for the dyadic
local-factor comparison with the checked Type II seed. -/
theorem localFactor_eq_typeIISeed_of_flatAllHTarget_certificate (k : ℕ)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : GramCongruenceCertificate (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
        (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)))) :
    L.massLocalFactor 2 =
      (PositiveDefiniteIntegralLattice.typeIISeed k).massLocalFactor 2 :=
  TypeIIModEightNativeTransport.localFactor_eq_typeIISeed_of_split_certificate k L hL
    (splitCertificate_of_flatAllHTarget_certificate k C)

/-- A positive-rank certificate to the canonical reindexed flat target gives the
Type II Bernoulli ordinary genus mass formula via the split-target bridge. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_flatAllHTarget_certificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : GramCongruenceCertificate (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (Matrix.reindex (finCongr (by omega : 2 * (4 * k) = 8 * k))
        (finCongr (by omega : 2 * (4 * k) = 8 * k)) (flatAllHTarget (4 * k)))) :
    L.ordinaryGenusMass = UnimodularMass.typeIIConstant (8 * k) :=
  TypeIIModEightNativeTransport.ordinaryGenusMass_eq_typeIIConstant_of_split_certificate
    k hk L hL (splitCertificate_of_flatAllHTarget_certificate k C)

/-- Reindexing a direct sum by a direct sum of equivalences reindexes the two blocks. -/
theorem reindex_sumBlockMatrix_sumCongr {α β γ δ : Type*}
    (eα : α ≃ γ) (eβ : β ≃ δ)
    (A : Matrix α α R) (B : Matrix β β R) :
    Matrix.reindex (Equiv.sumCongr eα eβ) (Equiv.sumCongr eα eβ) (sumBlockMatrix A B) =
      sumBlockMatrix (Matrix.reindex eα eα A) (Matrix.reindex eβ eβ B) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Flattening data for an `AllHTarget`: after choosing finite coordinates, it is
certified congruent to the canonical flat target with the same number of
hyperbolic planes. -/
structure AllHTargetFlatCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι R) where
  m : ℕ
  e : ι ≃ Fin (2 * m)
  certificate : GramCongruenceCertificate (Matrix.reindex e e T) (flatAllHTarget m)

/-- The empty all-H target flattens to the empty flat target. -/
def allHTargetFlatCertificateData_nil :
    AllHTargetFlatCertificateData (1 : Matrix (Fin 0) (Fin 0) R) where
  m := 0
  e := Equiv.refl _
  certificate := by
    simpa [flatAllHTarget] using
      (reflGramCongruenceCertificate (1 : Matrix (Fin 0) (Fin 0) R))

/-- A single hyperbolic plane flattens to the one-plane flat target. -/
def allHTargetFlatCertificateData_single : AllHTargetFlatCertificateData H where
  m := 1
  e := Equiv.refl _
  certificate := by
    rw [flatAllHTarget_one_eq_H]
    exact reflGramCongruenceCertificate H

/-- Flattening data is invariant under an outer reindexing of the target. -/
def AllHTargetFlatCertificateData.reindex {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {T : Matrix ι ι R} (D : AllHTargetFlatCertificateData T)
    (r : ι ≃ κ) : AllHTargetFlatCertificateData (Matrix.reindex r r T) where
  m := D.m
  e := r.symm.trans D.e
  certificate := by
    convert D.certificate using 1
    ext i j
    simp [Matrix.reindex_apply]

/-- Add one hyperbolic plane to flattened target data. -/
def AllHTargetFlatCertificateData.cons {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι R} (D : AllHTargetFlatCertificateData T) :
    AllHTargetFlatCertificateData (sumBlockMatrix H T) where
  m := D.m + 1
  e := (Equiv.sumCongr (Equiv.refl (Fin 2)) D.e).trans (flatAllHTargetStepEquiv D.m)
  certificate := by
    let C : GramCongruenceCertificate
        (Matrix.reindex (flatAllHTargetStepEquiv D.m) (flatAllHTargetStepEquiv D.m)
          (sumBlockMatrix H (Matrix.reindex D.e D.e T)))
        (Matrix.reindex (flatAllHTargetStepEquiv D.m) (flatAllHTargetStepEquiv D.m)
          (sumBlockMatrix H (flatAllHTarget D.m))) :=
      reindexCertificate (flatAllHTargetStepEquiv D.m)
        (sumBlockCertificate (reflGramCongruenceCertificate H) D.certificate)
    convert C using 1
    ext i j
    obtain ⟨i, rfl⟩ := (flatAllHTargetStepEquiv D.m).surjective i
    obtain ⟨j, rfl⟩ := (flatAllHTargetStepEquiv D.m).surjective j
    cases i <;> cases j <;> simp [Matrix.reindex_apply]

/-- Every iterated all-H target can be flattened to the canonical flat target after
choosing finite coordinates. -/
theorem AllHTarget.exists_flatCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι R} (hT : AllHTarget T) :
    Nonempty (AllHTargetFlatCertificateData T) := by
  induction hT with
  | nil => exact ⟨allHTargetFlatCertificateData_nil⟩
  | single => exact ⟨allHTargetFlatCertificateData_single⟩
  | cons hT ih =>
      rcases ih with ⟨D⟩
      exact ⟨D.cons⟩
  | reindex r hT ih =>
      rcases ih with ⟨D⟩
      exact ⟨D.reindex r⟩

/-- Chosen flattening certificate data for an all-H target. -/
def AllHTarget.flatCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι R} (hT : AllHTarget T) : AllHTargetFlatCertificateData T :=
  Classical.choice hT.exists_flatCertificateData


/-- A recursive all-H certificate with its target flattened to the canonical flat target. -/
structure RecursiveAllHFlatCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι R) where
  m : ℕ
  e : ι ≃ Fin (2 * m)
  certificate : GramCongruenceCertificate (Matrix.reindex e e G) (flatAllHTarget m)

/-- Flatten the target of a recursive all-H certificate and compose the certificates. -/
def RecursiveAllHCertificateData.flatCertificateData {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι R} (D : RecursiveAllHCertificateData G) :
    RecursiveAllHFlatCertificateData G :=
  let F := D.targetAllH.flatCertificateData
  { m := F.m
    e := F.e
    certificate := (reindexCertificate F.e D.certificate).trans F.certificate }

/-- Recursive direct-H peeling produces a certificate to a canonical flat all-H target. -/
theorem exists_recursiveAllHFlatCertificateData (m : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ m) :
    Nonempty (RecursiveAllHFlatCertificateData G) := by
  obtain ⟨D⟩ := exists_recursiveAllHCertificateData m hm G hsymm hdiag hdet
  exact ⟨D.flatCertificateData⟩

/-- Chosen recursive direct-H certificate data with canonical flat target. -/
def recursiveAllHFlatCertificateData (m : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ m) :
    RecursiveAllHFlatCertificateData G :=
  Classical.choice (exists_recursiveAllHFlatCertificateData m hm G hsymm hdiag hdet)


/-- The number of planes in flattened data for a `Fin (2*m)` target is forced by
cardinality. -/
theorem RecursiveAllHFlatCertificateData.rank_eq {m : ℕ}
    {G : Matrix (Fin (2 * m)) (Fin (2 * m)) R}
    (D : RecursiveAllHFlatCertificateData G) : D.m = m := by
  have hcard := Fintype.card_congr D.e
  simp only [Fintype.card_fin] at hcard
  omega

/-- A flattened recursive certificate on `Fin (2*m)` can be converted into a
same-index certificate from the original matrix to the canonical flat target. -/
def RecursiveAllHFlatCertificateData.sameIndexCertificate {m : ℕ}
    {G : Matrix (Fin (2 * m)) (Fin (2 * m)) R}
    (D : RecursiveAllHFlatCertificateData G) :
    GramCongruenceCertificate G (flatAllHTarget m) := by
  cases D with
  | mk mD e C =>
      have hm : mD = m := by
        have hcard := Fintype.card_congr e
        simp only [Fintype.card_fin] at hcard
        omega
      subst mD
      exact (reindexSelfCertificate e G).trans C

/-- A recursive all-H certificate on `Fin (2*m)` flattens to a same-index canonical
flat target certificate. -/
def RecursiveAllHCertificateData.sameIndexFlatCertificate {m : ℕ}
    {G : Matrix (Fin (2 * m)) (Fin (2 * m)) R}
    (D : RecursiveAllHCertificateData G) :
    GramCongruenceCertificate G (flatAllHTarget m) :=
  D.flatCertificateData.sameIndexCertificate

/-- Recursive direct-H peeling produces a same-index certificate to the canonical
flat all-H target. -/
theorem exists_recursiveAllHFlatCertificate (m : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ m) :
    Nonempty (GramCongruenceCertificate G (flatAllHTarget m)) := by
  obtain ⟨D⟩ := exists_recursiveAllHFlatCertificateData m hm G hsymm hdiag hdet
  exact ⟨D.sameIndexCertificate⟩

/-- Chosen same-index direct-H certificate to the canonical flat target. -/
def recursiveAllHFlatCertificate (m : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ m) :
    GramCongruenceCertificate G (flatAllHTarget m) :=
  Classical.choice (exists_recursiveAllHFlatCertificate m hm G hsymm hdiag hdet)

/-- Recursive direct-H peeling plus the final target bridge gives a concrete split-target
certificate for any rank `8*k` matrix satisfying the checked symmetry, even-diagonal,
and determinant-sign hypotheses. -/
def recursiveAllHSplitCertificate (k : ℕ) (hk : 0 < k)
    (G : Matrix (Fin (8 * k)) (Fin (8 * k)) R) (hsymm : G.IsSymm)
    (hdiag : ∀ i, Even8 (G i i)) (hdet : G.det = (-1 : R) ^ (4 * k)) :
    GramCongruenceCertificate G (TypeIIModEightCertificates.hyperbolicSplitTarget k) := by
  let e : Fin (2 * (4 * k)) ≃ Fin (8 * k) := finCongr (by omega : 2 * (4 * k) = 8 * k)
  let G' : Matrix (Fin (2 * (4 * k))) (Fin (2 * (4 * k))) R := Matrix.reindex e.symm e.symm G
  have hm : 1 ≤ 4 * k := by omega
  have hsymm' : G'.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [G', Matrix.reindex_apply, Matrix.IsSymm.ext_iff.mp hsymm]
  have hdiag' : ∀ i, Even8 (G' i i) := by
    intro i
    simpa [G', Matrix.reindex_apply, e] using hdiag (e i)
  have hdet' : G'.det = (-1 : R) ^ (4 * k) := by
    simp [G', hdet]
  let Cflat := recursiveAllHFlatCertificate (4 * k) hm G' hsymm' hdiag' hdet'
  let CflatReindexed := reindexCertificate e Cflat
  exact CflatReindexed.trans (flatAllHTargetSplitCertificate k)

/-- The reduced stored Gram matrix is symmetric over `ZMod 8`. -/
theorem zmod8_pairingMatrix_isSymm {n : ℕ} (L : PositiveDefiniteIntegralLattice n) :
    (L.pairingMatrix.map (Int.cast : ℤ → R)).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [L.form_symm.apply]

/-- Type II parity gives an even diagonal after reduction modulo eight. -/
theorem zmod8_pairingMatrix_diag_even8_of_isTypeII {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hII : L.HasEvenNorms) :
    ∀ i, Even8 ((L.pairingMatrix.map (Int.cast : ℤ → R)) i i) := by
  intro i
  have hdiagZ : Even (L.pairingMatrix i i) :=
    (L.hasEvenNorms_iff_forall_diag_even.mp hII) i
  rcases hdiagZ with ⟨a, ha⟩
  refine ⟨(a : R), ?_⟩
  simp [ha]
  ring

/-- Classical determinant-one unimodularity gives determinant one after reduction modulo eight. -/
theorem zmod8_pairingMatrix_det_eq_one_of_isUnimodular {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) :
    (L.pairingMatrix.map (Int.cast : ℤ → R)).det = 1 := by
  have hdetZ : L.pairingMatrix.det = 1 := by
    simpa [PositiveDefiniteIntegralLattice.IsUnimodular, PositiveDefiniteIntegralLattice.pairingDeterminant] using hL
  rw [← Int.cast_det]
  simp [hdetZ]

/-- In rank `8*k`, determinant one is the alternating determinant sign expected by
the direct-H recursion. -/
theorem zmod8_pairingMatrix_det_eq_neg_one_pow_four_mul_of_isUnimodular (k : ℕ)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular) :
    (L.pairingMatrix.map (Int.cast : ℤ → R)).det = (-1 : R) ^ (4 * k) := by
  have hone := zmod8_pairingMatrix_det_eq_one_of_isUnimodular L hL
  have hpow : (-1 : R) ^ (4 * k) = 1 := by
    rw [show 4 * k = 2 * (2 * k) by omega]
    simp [pow_mul]
  rw [hone, hpow]

/-- The production lattice-to-finite adapter: an arbitrary Type II classically
unimodular lattice in rank `8*k` has a direct-H certificate to the checked split target. -/
def typeIIUnimodularRecursiveSplitCertificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → R))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k) :=
  recursiveAllHSplitCertificate k hk (L.pairingMatrix.map (Int.cast : ℤ → R))
    (zmod8_pairingMatrix_isSymm L)
    (zmod8_pairingMatrix_diag_even8_of_isTypeII L hII)
    (zmod8_pairingMatrix_det_eq_neg_one_pow_four_mul_of_isUnimodular k L hL)

/-- The direct-H finite normal form compares the dyadic local factor of every
Type II classically unimodular lattice in rank `8*k` with the checked seed. -/
theorem localFactor_eq_typeIISeed_of_typeIIUnimodular_directH (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.massLocalFactor 2 =
      (PositiveDefiniteIntegralLattice.typeIISeed k).massLocalFactor 2 :=
  TypeIIModEightNativeTransport.localFactor_eq_typeIISeed_of_split_certificate k L hL
    (typeIIUnimodularRecursiveSplitCertificate k hk L hL hII)

/-- The direct-H finite normal form gives the Type II Bernoulli ordinary-mass
endpoint for every Type II classically unimodular lattice in positive rank `8*k`. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH
    (k : ℕ) (hk : 0 < k) (L : PositiveDefiniteIntegralLattice (8 * k))
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = UnimodularMass.typeIIConstant (8 * k) :=
  TypeIIModEightNativeTransport.ordinaryGenusMass_eq_typeIIConstant_of_split_certificate k hk L hL
    (typeIIUnimodularRecursiveSplitCertificate k hk L hL hII)

/-- The recursive direct-H split certificate feeds directly into the dyadic local-factor
comparison with the checked Type II seed. -/
theorem localFactor_eq_typeIISeed_of_recursiveAllHSplitCertificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (hsymm : (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)).IsSymm)
    (hdiag : ∀ i, Even8 ((L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) i i))
    (hdet : (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)).det = (-1 : R) ^ (4 * k)) :
    L.massLocalFactor 2 =
      (PositiveDefiniteIntegralLattice.typeIISeed k).massLocalFactor 2 :=
  TypeIIModEightNativeTransport.localFactor_eq_typeIISeed_of_split_certificate k L hL
    (recursiveAllHSplitCertificate k hk (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) hsymm hdiag hdet)

/-- The recursive direct-H split certificate gives the Type II Bernoulli ordinary
mass endpoint whenever the finite matrix hypotheses have been supplied. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_recursiveAllHSplitCertificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (hsymm : (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)).IsSymm)
    (hdiag : ∀ i, Even8 ((L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) i i))
    (hdet : (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)).det = (-1 : R) ^ (4 * k)) :
    L.ordinaryGenusMass = UnimodularMass.typeIIConstant (8 * k) :=
  TypeIIModEightNativeTransport.ordinaryGenusMass_eq_typeIIConstant_of_split_certificate k hk L hL
    (recursiveAllHSplitCertificate k hk (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) hsymm hdiag hdet)


#assert_standard_axioms zmod8_pairingMatrix_isSymm
#assert_standard_axioms zmod8_pairingMatrix_diag_even8_of_isTypeII
#assert_standard_axioms zmod8_pairingMatrix_det_eq_one_of_isUnimodular
#assert_standard_axioms zmod8_pairingMatrix_det_eq_neg_one_pow_four_mul_of_isUnimodular
#assert_standard_axioms typeIIUnimodularRecursiveSplitCertificate
#assert_standard_axioms localFactor_eq_typeIISeed_of_typeIIUnimodular_directH
#assert_standard_axioms ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH
#assert_standard_axioms recursiveAllHSplitCertificate
#assert_standard_axioms localFactor_eq_typeIISeed_of_recursiveAllHSplitCertificate
#assert_standard_axioms ordinaryGenusMass_eq_typeIIConstant_of_recursiveAllHSplitCertificate
#assert_standard_axioms flatAllHTargetStepEquiv
#assert_standard_axioms adjacentHyperbolicTarget
#assert_standard_axioms H_eq_adjacentHyperbolicTarget_two
#assert_standard_axioms flatAllHTarget_eq_adjacentHyperbolicTarget
#assert_standard_axioms H4_eq_adjacentHyperbolicTarget_eight
#assert_standard_axioms flatAllHTarget_four_mul_reindex_eq_adjacentHyperbolicTarget
#assert_standard_axioms hyperbolicSplitTargetStepEquiv
#assert_standard_axioms hyperbolicSplitTargetStepEquiv_inl_val
#assert_standard_axioms hyperbolicSplitTargetStepEquiv_inr_val
#assert_standard_axioms reindexed_blockSumMatrix_step_inl_inl
#assert_standard_axioms reindexed_blockSumMatrix_step_inl_inr
#assert_standard_axioms reindexed_blockSumMatrix_step_inr_inl
#assert_standard_axioms reindexed_blockSumMatrix_step_inr_inr
#assert_standard_axioms adjacentHyperbolicTarget_cross_left_zero
#assert_standard_axioms adjacentHyperbolicTarget_cross_right_zero
#assert_standard_axioms adjacentHyperbolicTarget_step_inl_inl
#assert_standard_axioms adjacentHyperbolicTarget_step_inr_inr
#assert_standard_axioms hyperbolicSplitTarget_eq_adjacentHyperbolicTarget
#assert_standard_axioms flatAllHTarget_four_mul_reindex_eq_hyperbolicSplitTarget
#assert_standard_axioms flatAllHTargetSplitCertificate
#assert_standard_axioms splitCertificate_of_flatAllHTarget_certificate
#assert_standard_axioms localFactor_eq_typeIISeed_of_flatAllHTarget_certificate
#assert_standard_axioms ordinaryGenusMass_eq_typeIIConstant_of_flatAllHTarget_certificate
#assert_standard_axioms reindex_sumBlockMatrix_sumCongr
#assert_standard_axioms AllHTargetFlatCertificateData
#assert_standard_axioms allHTargetFlatCertificateData_nil
#assert_standard_axioms allHTargetFlatCertificateData_single
#assert_standard_axioms AllHTargetFlatCertificateData.reindex
#assert_standard_axioms AllHTargetFlatCertificateData.cons
#assert_standard_axioms AllHTarget.exists_flatCertificateData
#assert_standard_axioms AllHTarget.flatCertificateData
#assert_standard_axioms RecursiveAllHFlatCertificateData
#assert_standard_axioms RecursiveAllHCertificateData.flatCertificateData
#assert_standard_axioms exists_recursiveAllHFlatCertificateData
#assert_standard_axioms recursiveAllHFlatCertificateData
#assert_standard_axioms RecursiveAllHFlatCertificateData.rank_eq
#assert_standard_axioms RecursiveAllHFlatCertificateData.sameIndexCertificate
#assert_standard_axioms RecursiveAllHCertificateData.sameIndexFlatCertificate
#assert_standard_axioms exists_recursiveAllHFlatCertificate
#assert_standard_axioms recursiveAllHFlatCertificate
#assert_standard_axioms flatAllHTarget
#assert_standard_axioms flatAllHTarget_allH
#assert_standard_axioms flatAllHTarget_one_eq_H
#assert_standard_axioms flatAllHTarget_four_eq_H4
#assert_standard_axioms flatAllHTarget_four_eq_hyperbolicSplitTarget_one

end TypeIIDirectPeeling
