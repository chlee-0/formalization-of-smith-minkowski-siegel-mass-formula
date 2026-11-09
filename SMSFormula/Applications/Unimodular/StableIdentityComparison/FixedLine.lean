import SMSFormula.Applications.Unimodular.DyadicTypeI
import SMSFormula.StandardAxiomsGuard

/-!
Finite conjugation and the norm-one-line stabilizer.
The tail norm is arbitrary. Its specialization to the actual E8 seed norm is
an adapter, not a new group classification or cardinality formula.
-/
noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice
namespace StableIdentityFixedLine
abbrev R := ZMod 4
abbrev Vec (n : ℕ) := Fin n → R
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) R
abbrev Iso {n : ℕ} (q : Vec n → ZMod 8) := {A : Mat n // ∀ x, q (A.mulVec x) = q x}
abbrev Fix {n : ℕ} (q : Vec n → ZMod 8) (v : Vec n) :=
  {A : Iso q // A.1.mulVec v = v}

def lineNorm {n : ℕ} (q : Vec n → ZMod 8) (x : Vec (n+1)) : ZMod 8 :=
  zmodFourLiftToZModEight (x 0)^2 + q (fun i => x i.succ)

def e (n : ℕ) : Vec (n+1) := Pi.single 0 1

def tail {n : ℕ} (A : Mat (n+1)) : Mat n := fun i j => A i.succ j.succ

def extend {n : ℕ} (A : Mat n) : Mat (n+1) := fun i j =>
  Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => A i j) j) i

lemma extend_mulVec {n : ℕ} (A : Mat n) (x : Vec (n+1)) :
    (extend A).mulVec x = Fin.cons (x 0) (A.mulVec (fun i => x i.succ)) := by
  funext i
  cases i using Fin.cases <;>
    simp [extend, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma tail_mulVec {n : ℕ} (A : Mat (n+1)) (v : Vec n) :
    (fun i => A.mulVec (Fin.cons 0 v) i.succ) = (tail A).mulVec v := by
  funext i
  simp [tail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

set_option maxHeartbeats 800000 in
lemma two_lift_injective :
    Function.Injective (fun a : R => (2 : ZMod 8) * zmodFourLiftToZModEight a) := by
  intro a b h
  have h' : (((2 * a.val : ℕ) : ZMod 8) = ((2 * b.val : ℕ) : ZMod 8)) := by
    simpa [zmodFourLiftToZModEight, Nat.cast_mul] using h
  have hmod : (2 * a.val) % 8 = (2 * b.val) % 8 := by
    exact (ZMod.natCast_eq_natCast_iff' (2 * a.val) (2 * b.val) 8).mp h'
  have ha : 2 * a.val < 8 := by
    have := ZMod.val_lt a
    omega
  have hb : 2 * b.val < 8 := by
    have := ZMod.val_lt b
    omega
  have h2 : 2 * a.val = 2 * b.val := by
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod
  apply ZMod.val_injective
  omega

lemma square_one_add (a : R) :
    zmodFourLiftToZModEight (1+a)^2 =
      1 + zmodFourLiftToZModEight a^2 + 2*zmodFourLiftToZModEight a := by
  fin_cases a <;> decide

/-- Fixing the norm-one line forces the complementary top row to vanish.
The two norm tests (0,v) and (1,v) retain the full mod-four information. -/
lemma top_zero {n : ℕ} {q : Vec n → ZMod 8}
    (A : Fix (lineNorm q) (e n)) (v : Vec n) :
    A.1.1.mulVec (Fin.cons 0 v) 0 = 0 := by
  let z := A.1.1.mulVec (Fin.cons 0 v)
  have hc : Fin.cons (1 : R) v = e n + Fin.cons 0 v := by
    funext i
    cases i using Fin.cases <;> simp [e]
  have hz : A.1.1.mulVec (Fin.cons 1 v) = e n + z := by
    rw [hc, Matrix.mulVec_add, A.2]
  have h0 : zmodFourLiftToZModEight (z 0)^2 + q (fun i => z i.succ) = q v := by
    simpa [z, lineNorm, zmodFourLiftToZModEight] using A.1.2 (Fin.cons 0 v)
  have h1 : zmodFourLiftToZModEight (1 + z 0)^2 + q (fun i => z i.succ) =
      1 + q v := by
    have h := A.1.2 (Fin.cons 1 v)
    rw [hz] at h
    simpa [lineNorm, e, Pi.single_apply, zmodFourLiftToZModEight] using h
  rw [square_one_add] at h1
  have htwo : (2 : ZMod 8) * zmodFourLiftToZModEight (z 0) = 0 := by
    linear_combination h1 - h0
  apply two_lift_injective
  simpa [zmodFourLiftToZModEight] using htwo

lemma tail_preserves {n : ℕ} {q : Vec n → ZMod 8}
    (A : Fix (lineNorm q) (e n)) : ∀ v, q ((tail A.1.1).mulVec v) = q v := by
  intro v
  have h := A.1.2 (Fin.cons 0 v)
  change zmodFourLiftToZModEight (A.1.1.mulVec (Fin.cons 0 v) 0)^2 +
    q (fun i => A.1.1.mulVec (Fin.cons 0 v) i.succ) =
    zmodFourLiftToZModEight (0 : R)^2 + q v at h
  rw [top_zero A v, tail_mulVec] at h
  exact add_left_cancel h

def extendIso {n : ℕ} {q : Vec n → ZMod 8} (A : Iso q) :
    Fix (lineNorm q) (e n) :=
  ⟨⟨extend A.1, by
      intro x
      rw [extend_mulVec]
      simp only [lineNorm, Fin.cons_zero, Fin.cons_succ, A.2]⟩, by
    rw [extend_mulVec]
    funext i
    cases i using Fin.cases <;> simp [e, Matrix.mulVec, dotProduct]⟩

/-- The stabilizer of a norm-one direct summand is the actual tail isometry set. -/
def fixedLineEquivTail {n : ℕ} (q : Vec n → ZMod 8) :
    Fix (lineNorm q) (e n) ≃ Iso q where
  toFun A := ⟨tail A.1.1, tail_preserves A⟩
  invFun := extendIso
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        have h := congrFun A.2 0
        simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply, extendIso, extend] using h.symm
      | succ j =>
        have h := top_zero A (Pi.single j 1)
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          Pi.single_apply, extendIso, extend] using h.symm
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have h := congrFun A.2 i.succ
        simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply, extendIso, extend] using h.symm
      | succ j => rfl
  right_inv A := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the fixed-line/tail equivalence. -/
theorem fixedLine_natCard_eq_tail {n : ℕ} (q : Vec n → ZMod 8) :
    Nat.card (Fix (lineNorm q) (e n)) = Nat.card (Iso q) :=
  Nat.card_congr (fixedLineEquivTail q)


/-- Conjugation by a supplied finite quadratic coordinate equivalence. -/
def isometryCongr {n : ℕ} (q r : Vec n → ZMod 8) (U V : Mat n)
    (hUV : U*V=1) (hVU : V*U=1) (hQ : ∀ x, r (U.mulVec x) = q x) :
    Iso q ≃ Iso r := by
  have hR : ∀ x, q (V.mulVec x) = r x := by
    intro x
    rw [← hQ, Matrix.mulVec_mulVec, hUV]
    simp
  refine
    { toFun := fun A => ⟨U*A.1*V, ?_⟩
      invFun := fun A => ⟨V*A.1*U, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ, A.2, hR]
  · intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hR, A.2, hQ]
  · intro A
    apply Subtype.ext
    calc
      V*(U*A.1*V)*U = (V*U)*A.1*(V*U) := by simp only [mul_assoc]
      _ = A.1 := by rw [hVU]; simp
  · intro A
    apply Subtype.ext
    calc
      U*(V*A.1*U)*V = (U*V)*A.1*(U*V) := by simp only [mul_assoc]
      _ = A.1 := by rw [hUV]; simp

/-- The pointed form of conjugation, used with U(e0)=the all-ones vector. -/
def fixedIsometryCongr {n : ℕ} (q r : Vec n → ZMod 8) (U V : Mat n)
    (hUV : U*V=1) (hVU : V*U=1) (hQ : ∀ x, r (U.mulVec x) = q x)
    (v w : Vec n) (hw : U.mulVec v = w) : Fix q v ≃ Fix r w := by
  let E := isometryCongr q r U V hUV hVU hQ
  have hv : V.mulVec w = v := by
    rw [← hw, Matrix.mulVec_mulVec, hVU]
    simp
  refine
    { toFun := fun A => ⟨E A.1, ?_⟩
      invFun := fun A => ⟨E.symm A.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (U*A.1.1*V).mulVec w = w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, A.2, hw]
  · change (V*A.1.1*U).mulVec v = v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, A.2, hv]
  · intro A
    apply Subtype.ext
    exact E.symm_apply_apply A.1
  · intro A
    apply Subtype.ext
    exact E.apply_symm_apply A.1

/-- A pointed quadratic coordinate equivalence from a norm-one line plus `q` to
a target norm `r` identifies the target fixed-point set with the tail isometry
set.  This is the generic fixed-line part of the Voskresenskii count bridge. -/
def fixedTargetEquivTail {n : ℕ} (q r : Vec (n + 1) → ZMod 8)
    (tailq : Vec n → ZMod 8)
    (U V : Mat (n + 1)) (hUV : U * V = 1) (hVU : V * U = 1)
    (hline : q = lineNorm tailq)
    (hQ : ∀ x, r (U.mulVec x) = q x)
    (w : Vec (n + 1)) (hw : U.mulVec (e n) = w) :
    Fix r w ≃ Iso tailq := by
  subst hline
  exact ((fixedIsometryCongr (lineNorm tailq) r U V hUV hVU hQ (e n) w hw).symm).trans
    (fixedLineEquivTail tailq)

/-- Cardinality form of `fixedTargetEquivTail`. -/
theorem fixedTarget_natCard_eq_tail {n : ℕ} (q r : Vec (n + 1) → ZMod 8)
    (tailq : Vec n → ZMod 8)
    (U V : Mat (n + 1)) (hUV : U * V = 1) (hVU : V * U = 1)
    (hline : q = lineNorm tailq)
    (hQ : ∀ x, r (U.mulVec x) = q x)
    (w : Vec (n + 1)) (hw : U.mulVec (e n) = w) :
    Nat.card (Fix r w) = Nat.card (Iso tailq) :=
  Nat.card_congr (fixedTargetEquivTail q r tailq U V hUV hVU hline hQ w hw)

end StableIdentityFixedLine
#assert_standard_axioms StableIdentityFixedLine.top_zero
#assert_standard_axioms StableIdentityFixedLine.fixedLineEquivTail
#assert_standard_axioms StableIdentityFixedLine.fixedLine_natCard_eq_tail
#assert_standard_axioms StableIdentityFixedLine.fixedTargetEquivTail
#assert_standard_axioms StableIdentityFixedLine.fixedTarget_natCard_eq_tail
#assert_standard_axioms StableIdentityFixedLine.isometryCongr
#assert_standard_axioms StableIdentityFixedLine.fixedIsometryCongr
