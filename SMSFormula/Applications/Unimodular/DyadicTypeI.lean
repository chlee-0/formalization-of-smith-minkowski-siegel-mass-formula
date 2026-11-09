import SMSFormula.Applications.Unimodular.Constants
import SMSFormula.Applications.Unimodular.Dyadic
import SMSFormula.Applications.Unimodular.Seeds

/-!
# Type I dyadic finite target

This file sets up the Type I dyadic local density as the same finite
count used by `Dyadic.lean`.  For the diagonal identity lattice
`Iₙ`, the depth-three dyadic coordinate target is rephrased as matrices over
`ZMod 4` preserving the diagonal quadratic form modulo `8`.
-/

noncomputable section

open BigOperators UnimodularMass

namespace PositiveDefiniteIntegralLattice

/-- The canonical lift from `ZMod 4` to residues modulo `8`, used only for
quadratic expressions where changing an integral representative by `4` does not
change the square modulo `8`. -/
def zmodFourLiftToZModEight (a : ZMod 4) : ZMod 8 :=
  (a.val : ZMod 8)

/-- Squaring makes the canonical `ZMod 4`-to-`ZMod 8` lift independent of the
choice of integral representative. -/
theorem zmodFourLiftToZModEight_sq_intCast (a : ℤ) :
    zmodFourLiftToZModEight (a : ZMod 4) ^ 2 = (a : ZMod 8) ^ 2 := by
  rw [show ((zmodFourLiftToZModEight (a : ZMod 4) : ZMod 8) ^ 2 : ZMod 8) =
      ((((a : ZMod 4).val : ℤ) ^ 2 : ℤ) : ZMod 8) by
        norm_num [zmodFourLiftToZModEight]]
  rw [show ((a : ZMod 8) ^ 2 : ZMod 8) = ((a ^ 2 : ℤ) : ZMod 8) by norm_num]
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  have h4z : (4 : ℤ) ∣ (a - (((a : ZMod 4).val : ℤ))) := by
    have h : (((a : ZMod 4).val : ℤ) : ZMod 4) = (a : ZMod 4) := by
      exact_mod_cast ZMod.natCast_zmod_val (a : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff] at h
    rw [Int.modEq_iff_dvd] at h
    exact h
  rcases h4z with ⟨c, hc⟩
  have hdiff : (a ^ 2 - ((a : ZMod 4).val : ℤ) ^ 2) =
      (a - ((a : ZMod 4).val : ℤ)) * (a + ((a : ZMod 4).val : ℤ)) := by ring
  rw [hdiff, hc]
  have heven : Even (a + (((a : ZMod 4).val : ℤ))) := by
    use ((a : ZMod 4).val : ℤ) + 2 * c
    nlinarith
  rcases heven with ⟨b, hb⟩
  use c * b
  rw [hb]
  ring

/-- Multiplying by `2` makes the canonical `ZMod 4`-to-`ZMod 8` lift behave
as expected on integral representatives. -/
theorem two_mul_zmodFourLiftToZModEight_intCast (a : ℤ) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (a : ZMod 4) = ((2 * a : ℤ) : ZMod 8) := by
  rw [show ((2 : ZMod 8) * zmodFourLiftToZModEight (a : ZMod 4) : ZMod 8) =
      (((2 * ((a : ZMod 4).val : ℤ) : ℤ)) : ZMod 8) by
        norm_num [zmodFourLiftToZModEight]]
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  have h4z : (4 : ℤ) ∣ (a - (((a : ZMod 4).val : ℤ))) := by
    have h : (((a : ZMod 4).val : ℤ) : ZMod 4) = (a : ZMod 4) := by
      exact_mod_cast ZMod.natCast_zmod_val (a : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff] at h
    rw [Int.modEq_iff_dvd] at h
    exact h
  rcases h4z with ⟨c, hc⟩
  use c
  rw [show (2 * (a : ℤ) - 2 * ↑(a : ZMod 4).val) =
      2 * (a - ↑(a : ZMod 4).val) by ring]
  rw [hc]
  ring

/-- The diagonal bilinear expression modulo `4` attached to the Type I identity
quadratic form modulo `8`. -/
def identityBilinearModFour {n : ℕ} (v w : Fin n → ZMod 4) : ZMod 4 :=
  ∑ i, v i * w i

/-- Integral representatives compute the diagonal modulo-`4` bilinear form. -/
theorem identityBilinearModFour_intCast {n : ℕ} (x y : Fin n → ℤ) :
    identityBilinearModFour (fun i : Fin n => (x i : ZMod 4)) (fun i => (y i : ZMod 4)) =
      ((∑ i, x i * y i : ℤ) : ZMod 4) := by
  simp [identityBilinearModFour]

/-- The diagonal Type I quadratic form on `Iₙ` modulo `8`, expressed on
coordinates modulo `4`. -/
def identityQuadraticModEight {n : ℕ} (v : Fin n → ZMod 4) : ZMod 8 :=
  ∑ i, zmodFourLiftToZModEight (v i) ^ 2

/-- Integral representatives compute the diagonal modulo-`8` quadratic form. -/
theorem identityQuadraticModEight_intCast {n : ℕ} (x : Fin n → ℤ) :
    identityQuadraticModEight (fun i : Fin n => (x i : ZMod 4)) =
      ((∑ i, x i ^ 2 : ℤ) : ZMod 8) := by
  simp [identityQuadraticModEight, zmodFourLiftToZModEight_sq_intCast]

/-- The diagonal modulo-`8` quadratic form of a coordinate vector is the square
of that coordinate. -/
theorem identityQuadraticModEight_single {n : ℕ} (j : Fin n) (a : ZMod 4) :
    identityQuadraticModEight (Pi.single j a) = zmodFourLiftToZModEight a ^ 2 := by
  rw [identityQuadraticModEight, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb, zmodFourLiftToZModEight]
  · intro hj
    simp at hj

/-- The diagonal Type I form satisfies the expected first-order addition
formula modulo `8`, with the cross term recorded modulo `4` and multiplied by
`2`. -/
theorem identityQuadraticModEight_add {n : ℕ} (v w : Fin n → ZMod 4) :
    identityQuadraticModEight (v + w) =
      identityQuadraticModEight v + identityQuadraticModEight w +
        (2 : ZMod 8) * zmodFourLiftToZModEight (identityBilinearModFour v w) := by
  let x : Fin n → ℤ := fun i => (v i).val
  let y : Fin n → ℤ := fun i => (w i).val
  have hx : (fun i : Fin n => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hy : (fun i : Fin n => (y i : ZMod 4)) = w := by
    funext i
    dsimp [y]
    exact ZMod.natCast_zmod_val (w i)
  have hxy : (fun i : Fin n => ((x i + y i : ℤ) : ZMod 4)) = v + w := by
    funext i
    rw [Pi.add_apply, Int.cast_add, congrFun hx i, congrFun hy i]
  have hsum : (∑ i, (x i + y i) ^ 2) =
      (∑ i, x i ^ 2) + (∑ i, y i ^ 2) + 2 * (∑ i, x i * y i) := by
    calc
      (∑ i, (x i + y i) ^ 2) = ∑ i, (x i ^ 2 + y i ^ 2 + 2 * (x i * y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, x i ^ 2) + (∑ i, y i ^ 2) + 2 * (∑ i, x i * y i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← hxy, ← hx, ← hy, identityQuadraticModEight_intCast (fun i => x i + y i),
    identityQuadraticModEight_intCast x, identityQuadraticModEight_intCast y,
    identityBilinearModFour_intCast, two_mul_zmodFourLiftToZModEight_intCast, hsum]
  norm_num

/-- The diagonal Type I form satisfies the expected subtraction formula modulo
`8`, with the cross term recorded modulo `4` and multiplied by `2`. -/
theorem identityQuadraticModEight_sub {n : ℕ} (v w : Fin n → ZMod 4) :
    identityQuadraticModEight (v - w) =
      identityQuadraticModEight v + identityQuadraticModEight w -
        (2 : ZMod 8) * zmodFourLiftToZModEight (identityBilinearModFour v w) := by
  let x : Fin n → ℤ := fun i => (v i).val
  let y : Fin n → ℤ := fun i => (w i).val
  have hx : (fun i : Fin n => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hy : (fun i : Fin n => (y i : ZMod 4)) = w := by
    funext i
    dsimp [y]
    exact ZMod.natCast_zmod_val (w i)
  have hxy : (fun i : Fin n => ((x i - y i : ℤ) : ZMod 4)) = v - w := by
    funext i
    rw [Pi.sub_apply, Int.cast_sub, congrFun hx i, congrFun hy i]
  have hsum : (∑ i, (x i - y i) ^ 2) =
      (∑ i, x i ^ 2) + (∑ i, y i ^ 2) - 2 * (∑ i, x i * y i) := by
    calc
      (∑ i, (x i - y i) ^ 2) = ∑ i, (x i ^ 2 + y i ^ 2 - 2 * (x i * y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, x i ^ 2) + (∑ i, y i ^ 2) - 2 * (∑ i, x i * y i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← hxy, ← hx, ← hy, identityQuadraticModEight_intCast (fun i => x i - y i),
    identityQuadraticModEight_intCast x, identityQuadraticModEight_intCast y,
    identityBilinearModFour_intCast, two_mul_zmodFourLiftToZModEight_intCast, hsum]
  norm_num

/-- The canonical lift respects products after squaring. -/
theorem zmodFourLiftToZModEight_mul_sq (a b : ZMod 4) :
    zmodFourLiftToZModEight (a * b) ^ 2 =
      zmodFourLiftToZModEight a ^ 2 * zmodFourLiftToZModEight b ^ 2 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Scalar multiplication by a `ZMod 4` residue scales the diagonal Type I
quadratic form by the square of its canonical lift. -/
theorem identityQuadraticModEight_const_mul {n : ℕ} (a : ZMod 4) (v : Fin n → ZMod 4) :
    identityQuadraticModEight (fun i : Fin n => a * v i) =
      zmodFourLiftToZModEight a ^ 2 * identityQuadraticModEight v := by
  rw [identityQuadraticModEight, identityQuadraticModEight]
  calc
    (∑ i, zmodFourLiftToZModEight (a * v i) ^ 2) =
        ∑ i, zmodFourLiftToZModEight a ^ 2 * zmodFourLiftToZModEight (v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [zmodFourLiftToZModEight_mul_sq]
    _ = zmodFourLiftToZModEight a ^ 2 * ∑ i, zmodFourLiftToZModEight (v i) ^ 2 := by
      rw [Finset.mul_sum]

/-- Distinct coordinate unit vectors are orthogonal for the Type I bilinear form. -/
theorem identityBilinearModFour_single_single_ne {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    identityBilinearModFour (Pi.single j (1 : ZMod 4)) (Pi.single k (1 : ZMod 4)) = 0 := by
  rw [identityBilinearModFour, Finset.sum_eq_zero]
  intro i _
  by_cases hij : i = j
  · subst hij
    simp [Pi.single_eq_of_ne hjk]
  · simp [Pi.single_eq_of_ne hij]

/-- The sum of two distinct coordinate unit vectors has diagonal modulo-`8`
quadratic value `2`. -/
theorem identityQuadraticModEight_single_add_single_one_ne {n : ℕ} {j k : Fin n}
    (hjk : j ≠ k) :
    identityQuadraticModEight (Pi.single j (1 : ZMod 4) + Pi.single k (1 : ZMod 4)) = 2 := by
  rw [identityQuadraticModEight_add, identityQuadraticModEight_single,
    identityQuadraticModEight_single, identityBilinearModFour_single_single_ne hjk]
  change ((1 : ZMod 8) ^ 2 + (1 : ZMod 8) ^ 2 : ZMod 8) = 2
  norm_num

/-- The stored quadratic form of the identity lattice is the sum of squares. -/
theorem identityLattice_quadForm_eq_sum_sq {n : ℕ} (x : Fin n → ℤ) :
    (identityLattice n).quadForm x = ∑ i, x i ^ 2 := by
  rw [(identityLattice n).quadForm_eq_dotProduct]
  have hmul : (1 : Matrix (Fin n) (Fin n) ℤ).mulVec x = x := by
    simp
  change dotProduct x ((1 : Matrix (Fin n) (Fin n) ℤ).mulVec x) = ∑ i, x i ^ 2
  rw [hmul]
  simp [dotProduct, pow_two]

/-- Matrices modulo `4` preserving the diagonal Type I quadratic form modulo
`8`.  This is the finite target expected in the Type I dyadic-density count. -/
abbrev identityQuadraticIsometryModFour (n : ℕ) : Type :=
  {X : Matrix (Fin n) (Fin n) (ZMod 4) //
    ∀ v : Fin n → ZMod 4,
      identityQuadraticModEight (X.mulVec v) = identityQuadraticModEight v}

noncomputable instance (n : ℕ) : Fintype (identityQuadraticIsometryModFour n) := by
  classical
  unfold identityQuadraticIsometryModFour
  infer_instance

/-- The zero-dimensional Type I diagonal quadratic-isometry target has one element. -/
theorem identityQuadraticIsometryModFour_natCard_zero :
    Nat.card (identityQuadraticIsometryModFour 0) = 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_eq_one_iff]
  let X0 : identityQuadraticIsometryModFour 0 :=
    ⟨![], by intro v; simp [identityQuadraticModEight]⟩
  use X0
  intro X
  apply Subtype.ext
  ext i j
  fin_cases i

/-- The one-dimensional Type I diagonal quadratic-isometry target consists of
the two odd residue classes. -/
theorem identityQuadraticIsometryModFour_natCard_one :
    Nat.card (identityQuadraticIsometryModFour 1) = 2 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {X : Matrix (Fin 1) (Fin 1) (ZMod 4) //
    ∀ v : Fin 1 → ZMod 4, identityQuadraticModEight (X.mulVec v) =
      identityQuadraticModEight v} = 2
  decide

/-- The two-dimensional Type I diagonal quadratic-isometry target has eight
elements, matching the signed-permutation count at this finite level. -/
theorem identityQuadraticIsometryModFour_natCard_two :
    Nat.card (identityQuadraticIsometryModFour 2) = 8 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {X : Matrix (Fin 2) (Fin 2) (ZMod 4) //
    ∀ v : Fin 2 → ZMod 4, identityQuadraticModEight (X.mulVec v) =
      identityQuadraticModEight v} = 8
  decide

/-- Every column of a diagonal Type I mod-`4` quadratic isometry has diagonal
quadratic value `1` modulo `8`. -/
theorem identityQuadraticIsometryModFour_column_norm {n : ℕ}
    (X : identityQuadraticIsometryModFour n) (j : Fin n) :
    identityQuadraticModEight (fun i : Fin n => X.1 i j) = 1 := by
  have h := X.2 (Pi.single j (1 : ZMod 4))
  have hvec : X.1.mulVec (Pi.single j (1 : ZMod 4)) = fun i : Fin n => X.1 i j := by
    ext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      simp at hj
  rw [hvec] at h
  simpa [identityQuadraticModEight_single] using h

/-- Distinct columns of a diagonal Type I mod-`4` quadratic isometry have
cross term killed after multiplying by `2` modulo `8`.  This is the off-diagonal
condition used by the Type I finite-count problem. -/
theorem identityQuadraticIsometryModFour_column_bilinear_ne {n : ℕ}
    (X : identityQuadraticIsometryModFour n) {j k : Fin n} (hjk : j ≠ k) :
    (2 : ZMod 8) * zmodFourLiftToZModEight
        (identityBilinearModFour (fun i : Fin n => X.1 i j) (fun i => X.1 i k)) = 0 := by
  let cj : Fin n → ZMod 4 := fun i => X.1 i j
  let ck : Fin n → ZMod 4 := fun i => X.1 i k
  let ej : Fin n → ZMod 4 := Pi.single j (1 : ZMod 4)
  let ek : Fin n → ZMod 4 := Pi.single k (1 : ZMod 4)
  have h := X.2 (ej + ek)
  have hvec : X.1.mulVec (ej + ek) = cj + ck := by
    ext i
    rw [Matrix.mulVec, dotProduct]
    have hj : (∑ x, X.1 i x * ej x) = X.1 i j := by
      rw [Finset.sum_eq_single j]
      · simp [ej]
      · intro b _ hb
        simp [ej, Pi.single_eq_of_ne hb]
      · intro hjmem
        simp at hjmem
    have hk : (∑ x, X.1 i x * ek x) = X.1 i k := by
      rw [Finset.sum_eq_single k]
      · simp [ek]
      · intro b _ hb
        simp [ek, Pi.single_eq_of_ne hb]
      · intro hkmem
        simp at hkmem
    calc
      (∑ x, X.1 i x * (ej + ek) x) = ∑ x, (X.1 i x * ej x + X.1 i x * ek x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Pi.add_apply, mul_add]
      _ = (∑ x, X.1 i x * ej x) + (∑ x, X.1 i x * ek x) := by
        rw [Finset.sum_add_distrib]
      _ = X.1 i j + X.1 i k := by
        rw [hj, hk]
      _ = (cj + ck) i := by
        rfl
  have hpair : identityQuadraticModEight (cj + ck) = 2 := by
    rw [← hvec]
    have hbase : identityQuadraticModEight (ej + ek) = 2 := by
      simpa [ej, ek] using identityQuadraticModEight_single_add_single_one_ne hjk
    exact h.trans hbase
  have hadd := identityQuadraticModEight_add cj ck
  have hterm₀ :
      identityQuadraticModEight cj + identityQuadraticModEight ck +
        (2 : ZMod 8) * zmodFourLiftToZModEight (identityBilinearModFour cj ck) = 2 := by
    rw [← hadd]
    exact hpair
  have hnormj : identityQuadraticModEight cj = 1 := by
    simpa [cj] using identityQuadraticIsometryModFour_column_norm X j
  have hnormk : identityQuadraticModEight ck = 1 := by
    simpa [ck] using identityQuadraticIsometryModFour_column_norm X k
  have hterm : (1 : ZMod 8) + 1 +
      (2 : ZMod 8) * zmodFourLiftToZModEight (identityBilinearModFour cj ck) = 2 := by
    simpa [hnormj, hnormk] using hterm₀
  have hcancel :
      (2 : ZMod 8) +
          ((2 : ZMod 8) * zmodFourLiftToZModEight (identityBilinearModFour cj ck)) =
        (2 : ZMod 8) + 0 := by
    simpa [show ((1 : ZMod 8) + 1) = 2 by norm_num, add_assoc] using hterm
  have hzero := add_left_cancel hcancel
  simpa [cj, ck] using hzero


/-- Vectors whose diagonal Type I quadratic value is a fixed residue modulo `8`. -/
abbrev identityQuadraticShellModEight (n : ℕ) (r : ZMod 8) : Type :=
  {v : Fin n → ZMod 4 // identityQuadraticModEight v = r}

noncomputable instance (n : ℕ) (r : ZMod 8) :
    Fintype (identityQuadraticShellModEight n r) := by
  unfold identityQuadraticShellModEight
  infer_instance

/-- Splitting off the first coordinate in the diagonal Type I modulo-`8` shell. -/
def identityQuadraticShellConsEquiv (n : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEight (n + 1) r ≃
      Σ a : ZMod 4,
        identityQuadraticShellModEight n (r - zmodFourLiftToZModEight a ^ 2) := by
  refine (Equiv.subtypeEquiv (Fin.consEquiv fun _ : Fin (n + 1) => ZMod 4).symm ?_).trans
    ((Equiv.subtypeProdEquivSigmaSubtype
      (fun (a : ZMod 4) (w : Fin n → ZMod 4) =>
        zmodFourLiftToZModEight a ^ 2 + identityQuadraticModEight w = r)).trans
      (Equiv.sigmaCongrRight fun a => Equiv.subtypeEquivRight fun w => ?_))
  · intro v
    simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
    rw [identityQuadraticModEight, Fin.sum_univ_succ]
    rfl
  · constructor
    · intro h
      rw [← h]
      abel
    · intro h
      rw [h]
      abel

/-- First-coordinate recurrence for Type I diagonal modulo-`8` shell counts. -/
theorem identityQuadraticShellModEight_natCard_succ (n : ℕ) (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight (n + 1) r) =
      ∑ a : ZMod 4,
        Nat.card (identityQuadraticShellModEight n (r - zmodFourLiftToZModEight a ^ 2)) := by
  rw [Nat.card_congr (identityQuadraticShellConsEquiv n r), Nat.card_sigma]


/-- Vectors of diagonal Type I norm `1` modulo `8` over `(ZMod 4)^n`.
These are the possible first columns in the Type I identity finite-count target. -/
abbrev identityQuadraticUnitVectorsModFour (n : ℕ) : Type :=
  {v : Fin n → ZMod 4 // identityQuadraticModEight v = 1}

noncomputable instance (n : ℕ) : Fintype (identityQuadraticUnitVectorsModFour n) := by
  unfold identityQuadraticUnitVectorsModFour
  infer_instance

/-- Norm-one vectors are the `1`-shell modulo `8`. -/
def identityQuadraticUnitVectorsModFourEquivShell (n : ℕ) :
    identityQuadraticUnitVectorsModFour n ≃ identityQuadraticShellModEight n 1 :=
  Equiv.refl _

/-- First-coordinate recurrence for the Type I norm-one vector count. -/
theorem identityQuadraticUnitVectorsModFour_natCard_succ (n : ℕ) :
    Nat.card (identityQuadraticUnitVectorsModFour (n + 1)) =
      ∑ a : ZMod 4,
        Nat.card (identityQuadraticShellModEight n (1 - zmodFourLiftToZModEight a ^ 2)) := by
  simpa [identityQuadraticUnitVectorsModFour] using
    identityQuadraticShellModEight_natCard_succ n (1 : ZMod 8)

/-- Explicit four-residue form of the first-coordinate recurrence for Type I
diagonal modulo-`8` shell counts.  The square residues of `ZMod 4` are
`0, 1, 4, 1` after the canonical lift to `ZMod 8`. -/
theorem identityQuadraticShellModEight_natCard_succ_explicit (n : ℕ) (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight (n + 1) r) =
      Nat.card (identityQuadraticShellModEight n r) +
        2 * Nat.card (identityQuadraticShellModEight n (r - 1)) +
        Nat.card (identityQuadraticShellModEight n (r - 4)) := by
  rw [identityQuadraticShellModEight_natCard_succ]
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp
    (fun a : ZMod 4 =>
      Nat.card (identityQuadraticShellModEight n (r - zmodFourLiftToZModEight a ^ 2)))]
  rw [Fin.sum_univ_four]
  change Nat.card (identityQuadraticShellModEight n (r - (0 : ZMod 8)^2)) +
          Nat.card (identityQuadraticShellModEight n (r - (1 : ZMod 8)^2)) +
        Nat.card (identityQuadraticShellModEight n (r - (2 : ZMod 8)^2)) +
      Nat.card (identityQuadraticShellModEight n (r - (3 : ZMod 8)^2)) = _
  norm_num
  rw [show (9 : ZMod 8) = 1 by decide]
  omega

/-- Explicit norm-one specialization of the Type I shell recurrence.  This is
the first input to the direct first-column count for the identity-lattice
dyadic density. -/
theorem identityQuadraticUnitVectorsModFour_natCard_succ_explicit (n : ℕ) :
    Nat.card (identityQuadraticUnitVectorsModFour (n + 1)) =
      Nat.card (identityQuadraticShellModEight n 1) +
        2 * Nat.card (identityQuadraticShellModEight n 0) +
        Nat.card (identityQuadraticShellModEight n 5) := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ]
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp
    (fun a : ZMod 4 =>
      Nat.card (identityQuadraticShellModEight n (1 - zmodFourLiftToZModEight a ^ 2)))]
  rw [Fin.sum_univ_four]
  change Nat.card (identityQuadraticShellModEight n ((1 : ZMod 8) - (0 : ZMod 8)^2)) +
          Nat.card (identityQuadraticShellModEight n ((1 : ZMod 8) - (1 : ZMod 8)^2)) +
        Nat.card (identityQuadraticShellModEight n ((1 : ZMod 8) - (2 : ZMod 8)^2)) +
      Nat.card (identityQuadraticShellModEight n ((1 : ZMod 8) - (3 : ZMod 8)^2)) = _
  norm_num
  rw [show (-3 : ZMod 8) = 5 by decide, show (-8 : ZMod 8) = 0 by decide]
  omega

/-- Recursive finite formula for the diagonal Type I shell counts.  It is the
same first-coordinate recurrence as `identityQuadraticShellModEight_natCard_succ_explicit`,
started from the zero-dimensional shell. -/
def identityQuadraticShellModEightCount : ℕ → ZMod 8 → ℕ
  | 0, r => if r = 0 then 1 else 0
  | n + 1, r =>
      identityQuadraticShellModEightCount n r +
        2 * identityQuadraticShellModEightCount n (r - 1) +
        identityQuadraticShellModEightCount n (r - 4)

/-- Base value for the Type I diagonal modulo-`8` shell counts. -/
theorem identityQuadraticShellModEight_natCard_zero (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 0 r) = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst hr
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {v : Fin 0 → ZMod 4 //
      identityQuadraticModEight v = (0 : ZMod 8)} = 1
    simp [identityQuadraticModEight]
  · rw [if_neg hr]
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {v : Fin 0 → ZMod 4 // identityQuadraticModEight v = r} = 0
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hr (by rw [← x.2]; simp [identityQuadraticModEight])⟩

/-- The recursive finite formula computes the actual diagonal Type I shell
cardinality in every rank and every residue class. -/
theorem identityQuadraticShellModEight_natCard_eq_count (n : ℕ) (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight n r) =
      identityQuadraticShellModEightCount n r := by
  induction n generalizing r with
  | zero =>
      rw [identityQuadraticShellModEight_natCard_zero]
      rfl
  | succ n ih =>
      rw [identityQuadraticShellModEight_natCard_succ_explicit]
      rw [ih r, ih (r - 1), ih (r - 4)]
      rfl

/-- Integer-valued shell vectors indexed by residues modulo `8`. -/
abbrev identityQuadraticShellVector := ZMod 8 → ℤ

/-- One coordinate of `(ZMod 4)^n` contributes square residue `0`, `1`, or `4`
with multiplicities `1`, `2`, and `1`. -/
def identityQuadraticShellStep (f : identityQuadraticShellVector) :
    identityQuadraticShellVector :=
  fun r => f r + 2 * f (r - 1) + f (r - 4)

/-- Period-four part of the integer closed shell model.  This table form avoids
large propositional case splits in downstream finite checks. -/
def identityQuadraticShellPhase (a b : ℤ) (r : ZMod 8) : ℤ :=
  match r.val % 4 with
  | 0 => a
  | 1 => b
  | 2 => -a
  | _ => -b

/-- Antiperiodic delta part of the integer closed shell model. -/
def identityQuadraticShellDelta (t r : ZMod 8) : ℤ :=
  if r = t then 1 else if r = t - 4 then -1 else 0

/-- Integer numerator model for eight times the Type I shell count. -/
def identityQuadraticShellModel (u a b v : ℤ) (t r : ZMod 8) : ℤ :=
  u + 2 * identityQuadraticShellPhase a b r + v * identityQuadraticShellDelta t r

/-- The recursive natural shell count, viewed as an integer shell vector. -/
def identityQuadraticShellModEightCountInt (n : ℕ) : identityQuadraticShellVector :=
  fun r => (identityQuadraticShellModEightCount n r : ℤ)

/-- The recursive shell count satisfies the integer shell-step recurrence. -/
theorem identityQuadraticShellModEightCountInt_succ (n : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (n + 1) r =
      identityQuadraticShellStep (identityQuadraticShellModEightCountInt n) r := by
  simp [identityQuadraticShellModEightCountInt, identityQuadraticShellStep,
    identityQuadraticShellModEightCount, Nat.cast_add, Nat.cast_mul]

/-- The rank-one shell count is the first vector of the integer closed model. -/
theorem identityQuadraticShellModEightCountInt_one_model (r : ZMod 8) :
    8 * identityQuadraticShellModEightCountInt 1 r =
      identityQuadraticShellModel 4 2 2 8 1 r := by
  fin_cases r <;> decide

/-- The phase table at residue `0`. -/
theorem identityQuadraticShellPhase_zero (a b : ℤ) :
    identityQuadraticShellPhase a b (0 : ZMod 8) = a := by
  simp [identityQuadraticShellPhase]

/-- The phase table at residue `1`. -/
theorem identityQuadraticShellPhase_one (a b : ℤ) :
    identityQuadraticShellPhase a b (1 : ZMod 8) = b := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (1 : ZMod 8) = 1 by rfl]

/-- The phase table at residue `2`. -/
theorem identityQuadraticShellPhase_two (a b : ℤ) :
    identityQuadraticShellPhase a b (2 : ZMod 8) = -a := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (2 : ZMod 8) = 2 by rfl]

/-- The phase table at residue `3`. -/
theorem identityQuadraticShellPhase_three (a b : ℤ) :
    identityQuadraticShellPhase a b (3 : ZMod 8) = -b := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (3 : ZMod 8) = 3 by rfl]

/-- The phase table at residue `4`. -/
theorem identityQuadraticShellPhase_four (a b : ℤ) :
    identityQuadraticShellPhase a b (4 : ZMod 8) = a := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (4 : ZMod 8) = 4 by rfl]

/-- The phase table at residue `5`. -/
theorem identityQuadraticShellPhase_five (a b : ℤ) :
    identityQuadraticShellPhase a b (5 : ZMod 8) = b := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (5 : ZMod 8) = 5 by rfl]

/-- The phase table at residue `6`. -/
theorem identityQuadraticShellPhase_six (a b : ℤ) :
    identityQuadraticShellPhase a b (6 : ZMod 8) = -a := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (6 : ZMod 8) = 6 by rfl]

/-- The phase table at residue `7`. -/
theorem identityQuadraticShellPhase_seven (a b : ℤ) :
    identityQuadraticShellPhase a b (7 : ZMod 8) = -b := by
  rw [identityQuadraticShellPhase]
  rw [show ZMod.val (7 : ZMod 8) = 7 by rfl]

/-- The phase table at residue `-1`. -/
theorem identityQuadraticShellPhase_neg_one (a b : ℤ) :
    identityQuadraticShellPhase a b (-1 : ZMod 8) = -b := by
  rw [show (-1 : ZMod 8) = 7 by decide]
  exact identityQuadraticShellPhase_seven a b

/-- The phase table at residue `-2`. -/
theorem identityQuadraticShellPhase_neg_two (a b : ℤ) :
    identityQuadraticShellPhase a b (-2 : ZMod 8) = -a := by
  rw [show (-2 : ZMod 8) = 6 by decide]
  exact identityQuadraticShellPhase_six a b

/-- The phase table at residue `-3`. -/
theorem identityQuadraticShellPhase_neg_three (a b : ℤ) :
    identityQuadraticShellPhase a b (-3 : ZMod 8) = b := by
  rw [show (-3 : ZMod 8) = 5 by decide]
  exact identityQuadraticShellPhase_five a b

/-- The phase table at residue `-4`. -/
theorem identityQuadraticShellPhase_neg_four (a b : ℤ) :
    identityQuadraticShellPhase a b (-4 : ZMod 8) = a := by
  rw [show (-4 : ZMod 8) = 4 by decide]
  exact identityQuadraticShellPhase_four a b

/-- Convolution by the one-coordinate shell kernel updates the period-four phase
parameters in the closed shell model. -/
theorem identityQuadraticShellPhase_step (a b : ℤ) (r : ZMod 8) :
    identityQuadraticShellPhase a b r + 2 * identityQuadraticShellPhase a b (r - 1) +
      identityQuadraticShellPhase a b (r - 4) =
        identityQuadraticShellPhase (2 * a - 2 * b) (2 * a + 2 * b) r := by
  have hlt : r.val < 8 := ZMod.val_lt r
  rw [← ZMod.natCast_zmod_val r]
  interval_cases hv : r.val <;>
    norm_num [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellPhase_neg_one, identityQuadraticShellPhase_neg_two,
      identityQuadraticShellPhase_neg_three, identityQuadraticShellPhase_neg_four] <;>
    ring_nf

/-- Convolution by the one-coordinate shell kernel translates and doubles the
antiperiodic delta part of the closed shell model. -/
theorem identityQuadraticShellDelta_step (t r : ZMod 8) :
    identityQuadraticShellDelta t r + 2 * identityQuadraticShellDelta t (r - 1) +
      identityQuadraticShellDelta t (r - 4) =
        2 * identityQuadraticShellDelta (t + 1) r := by
  decide +revert

/-- One shell recursion step for the integer closed shell model. -/
theorem identityQuadraticShellModel_step (u a b v : ℤ) (t r : ZMod 8) :
    identityQuadraticShellStep (identityQuadraticShellModel u a b v t) r =
      identityQuadraticShellModel (4 * u) (2 * a - 2 * b) (2 * a + 2 * b) (2 * v)
        (t + 1) r := by
  have hδ : v * identityQuadraticShellDelta t r +
        2 * (v * identityQuadraticShellDelta t (r - 1)) +
        v * identityQuadraticShellDelta t (r - 4) =
      v * (2 * identityQuadraticShellDelta (t + 1) r) := by
    rw [← identityQuadraticShellDelta_step t r]
    ring
  calc
    identityQuadraticShellStep (identityQuadraticShellModel u a b v t) r
        = 4 * u +
          2 * (identityQuadraticShellPhase a b r +
            2 * identityQuadraticShellPhase a b (r - 1) +
            identityQuadraticShellPhase a b (r - 4)) +
          (v * identityQuadraticShellDelta t r +
            2 * (v * identityQuadraticShellDelta t (r - 1)) +
            v * identityQuadraticShellDelta t (r - 4)) := by
          simp only [identityQuadraticShellStep, identityQuadraticShellModel]
          ring
    _ = 4 * u +
          2 * identityQuadraticShellPhase (2 * a - 2 * b) (2 * a + 2 * b) r +
          v * (2 * identityQuadraticShellDelta (t + 1) r) := by
          rw [identityQuadraticShellPhase_step a b r, hδ]
    _ = identityQuadraticShellModel (4 * u) (2 * a - 2 * b) (2 * a + 2 * b) (2 * v)
          (t + 1) r := by
          simp only [identityQuadraticShellModel]
          ring

/-- Uniform parameter for the Type I integer shell model, indexed so `k`
corresponds to rank `k + 1`. -/
def identityQuadraticShellModelUniform : ℕ → ℤ
  | 0 => 4
  | k + 1 => 4 * identityQuadraticShellModelUniform k

/-- Delta coefficient for the Type I integer shell model, indexed so `k`
corresponds to rank `k + 1`. -/
def identityQuadraticShellModelDeltaCoeff : ℕ → ℤ
  | 0 => 8
  | k + 1 => 2 * identityQuadraticShellModelDeltaCoeff k

/-- Phase parameters for the Type I integer shell model, indexed so `k`
corresponds to rank `k + 1`. -/
def identityQuadraticShellModelPhase : ℕ → ℤ × ℤ
  | 0 => (2, 2)
  | k + 1 => (2 * (identityQuadraticShellModelPhase k).1 -
      2 * (identityQuadraticShellModelPhase k).2,
      2 * (identityQuadraticShellModelPhase k).1 +
      2 * (identityQuadraticShellModelPhase k).2)

/-- First phase coordinate for the Type I integer shell model. -/
def identityQuadraticShellModelPhaseA (k : ℕ) : ℤ :=
  (identityQuadraticShellModelPhase k).1

/-- Second phase coordinate for the Type I integer shell model. -/
def identityQuadraticShellModelPhaseB (k : ℕ) : ℤ :=
  (identityQuadraticShellModelPhase k).2

/-- First phase coordinate after one shell-model step. -/
theorem identityQuadraticShellModelPhaseA_succ (k : ℕ) :
    identityQuadraticShellModelPhaseA (k + 1) =
      2 * identityQuadraticShellModelPhaseA k - 2 * identityQuadraticShellModelPhaseB k := by
  simp [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhaseB,
    identityQuadraticShellModelPhase]

/-- Second phase coordinate after one shell-model step. -/
theorem identityQuadraticShellModelPhaseB_succ (k : ℕ) :
    identityQuadraticShellModelPhaseB (k + 1) =
      2 * identityQuadraticShellModelPhaseA k + 2 * identityQuadraticShellModelPhaseB k := by
  simp [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhaseB,
    identityQuadraticShellModelPhase]

/-- The first phase coordinate scales by `4096` after one full residue cycle. -/
theorem identityQuadraticShellModelPhaseA_add_eight (k : ℕ) :
    identityQuadraticShellModelPhaseA (k + 8) =
      4096 * identityQuadraticShellModelPhaseA k := by
  simp [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  ring

/-- The second phase coordinate scales by `4096` after one full residue cycle. -/
theorem identityQuadraticShellModelPhaseB_add_eight (k : ℕ) :
    identityQuadraticShellModelPhaseB (k + 8) =
      4096 * identityQuadraticShellModelPhaseB k := by
  simp [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  ring

/-- First phase coordinate in the `0 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q) = (2 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) = 8 * q + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `1 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_one (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 1) = (0 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 1 = (8 * q + 1) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `2 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_two (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 2) = (-16 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 2 = (8 * q + 2) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `3 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_three (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 3) = (-64 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 3 = (8 * q + 3) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `4 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_four (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 4) = (-128 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 4 = (8 * q + 4) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `5 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_five (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 5) = (0 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 5 = (8 * q + 5) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `6 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_six (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 6) = (1024 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 6 = (8 * q + 6) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- First phase coordinate in the `7 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseA_eight_mul_add_seven (q : ℕ) :
    identityQuadraticShellModelPhaseA (8 * q + 7) = (4096 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 7 = (8 * q + 7) + 8 by omega]
      rw [identityQuadraticShellModelPhaseA_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `0 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q) = (2 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) = 8 * q + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `1 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_one (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 1) = (8 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 1 = (8 * q + 1) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `2 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_two (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 2) = (16 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 2 = (8 * q + 2) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `3 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_three (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 3) = (0 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 3 = (8 * q + 3) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `4 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_four (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 4) = (-128 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 4 = (8 * q + 4) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `5 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_five (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 5) = (-512 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 5 = (8 * q + 5) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `6 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_six (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 6) = (-1024 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 6 = (8 * q + 6) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Second phase coordinate in the `7 mod 8` shell-model family. -/
theorem identityQuadraticShellModelPhaseB_eight_mul_add_seven (q : ℕ) :
    identityQuadraticShellModelPhaseB (8 * q + 7) = (0 : ℤ) * (4096 : ℤ) ^ q := by
  induction q with
  | zero => norm_num [identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase]
  | succ q ih =>
      rw [show 8 * (q + 1) + 7 = (8 * q + 7) + 8 by omega]
      rw [identityQuadraticShellModelPhaseB_add_eight]
      rw [ih, pow_succ]
      ring

/-- Convert the phase residue-family scale to a power of two. -/
theorem identityQuadraticShellModelPhaseScale_eq_pow (q : ℕ) :
    (4096 : ℤ) ^ q = (2 : ℤ) ^ (12 * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, ih]
      rw [show 12 * (q + 1) = 12 * q + 12 by omega]
      rw [pow_add]
      norm_num

/-- The shell step commutes with multiplying every shell count by a fixed integer. -/
theorem identityQuadraticShellStep_mul_left
    (c : ℤ) (f : identityQuadraticShellVector) (r : ZMod 8) :
    c * identityQuadraticShellStep f r = identityQuadraticShellStep (fun s => c * f s) r := by
  simp [identityQuadraticShellStep]
  ring

/-- The recursive shell count, scaled by eight, is the integer shell model with
recursively evolved parameters.  The index `k` corresponds to rank `k + 1`. -/
theorem identityQuadraticShellModEightCountInt_succ_eq_model (k : ℕ) (r : ZMod 8) :
    8 * identityQuadraticShellModEightCountInt (k + 1) r =
      identityQuadraticShellModel (identityQuadraticShellModelUniform k)
        (identityQuadraticShellModelPhaseA k) (identityQuadraticShellModelPhaseB k)
        (identityQuadraticShellModelDeltaCoeff k) ((k + 1 : ℕ) : ZMod 8) r := by
  induction k generalizing r with
  | zero =>
      simpa [identityQuadraticShellModelUniform, identityQuadraticShellModelPhaseA,
        identityQuadraticShellModelPhaseB, identityQuadraticShellModelPhase,
        identityQuadraticShellModelDeltaCoeff] using
        identityQuadraticShellModEightCountInt_one_model r
  | succ k ih =>
      rw [identityQuadraticShellModEightCountInt_succ (k + 1) r]
      rw [identityQuadraticShellStep_mul_left]
      rw [show ((k + 1 + 1 : ℕ) : ZMod 8) =
        (((k + 1 : ℕ) : ZMod 8) + 1) by norm_num [Nat.cast_add]]
      simp only [identityQuadraticShellModelUniform, identityQuadraticShellModelDeltaCoeff,
        identityQuadraticShellModelPhaseA, identityQuadraticShellModelPhaseB,
        identityQuadraticShellModelPhase]
      change identityQuadraticShellStep
          (fun s => 8 * identityQuadraticShellModEightCountInt (k + 1) s) r =
        identityQuadraticShellModel (4 * identityQuadraticShellModelUniform k)
          (2 * identityQuadraticShellModelPhaseA k -
            2 * identityQuadraticShellModelPhaseB k)
          (2 * identityQuadraticShellModelPhaseA k +
            2 * identityQuadraticShellModelPhaseB k)
          (2 * identityQuadraticShellModelDeltaCoeff k)
          (((k + 1 : ℕ) : ZMod 8) + 1) r
      rw [← identityQuadraticShellModel_step (identityQuadraticShellModelUniform k)
        (identityQuadraticShellModelPhaseA k) (identityQuadraticShellModelPhaseB k)
        (identityQuadraticShellModelDeltaCoeff k) (((k + 1 : ℕ) : ZMod 8)) r]
      simp only [identityQuadraticShellStep]
      rw [ih r, ih (r - 1), ih (r - 4)]

/-- Closed power form of the uniform shell-model parameter. -/
theorem identityQuadraticShellModelUniform_eq_pow (k : ℕ) :
    identityQuadraticShellModelUniform k = (2 : ℤ) ^ (2 * (k + 1)) := by
  induction k with
  | zero => simp [identityQuadraticShellModelUniform]
  | succ k ih =>
      simp [identityQuadraticShellModelUniform, ih]
      rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by omega]
      rw [pow_add]
      norm_num
      ring

/-- Closed power form of the delta shell-model parameter. -/
theorem identityQuadraticShellModelDeltaCoeff_eq_pow (k : ℕ) :
    identityQuadraticShellModelDeltaCoeff k = (2 : ℤ) ^ (k + 3) := by
  induction k with
  | zero => simp [identityQuadraticShellModelDeltaCoeff]
  | succ k ih =>
      simp [identityQuadraticShellModelDeltaCoeff, ih]
      rw [show k + 1 + 3 = (k + 3) + 1 by omega]
      rw [pow_add]
      norm_num
      ring

/-- The scaled recursive shell count with the uniform and delta model parameters
identified as powers.  The phase parameters remain the only recursive model
coordinates. -/
theorem identityQuadraticShellModEightCountInt_succ_eq_model_pow (k : ℕ) (r : ZMod 8) :
    8 * identityQuadraticShellModEightCountInt (k + 1) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (k + 1)))
        (identityQuadraticShellModelPhaseA k) (identityQuadraticShellModelPhaseB k)
        ((2 : ℤ) ^ (k + 3)) ((k + 1 : ℕ) : ZMod 8) r := by
  rw [identityQuadraticShellModEightCountInt_succ_eq_model]
  rw [identityQuadraticShellModelUniform_eq_pow, identityQuadraticShellModelDeltaCoeff_eq_pow]

/-- Explicit recursive formula for the total norm-one shell count.  This is the
finite-count identity that the closed Type I shell target must satisfy in the
next residue-family induction. -/
theorem identityQuadraticShellModEightCount_one_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 1 =
      identityQuadraticShellModEightCount n 1 +
        2 * identityQuadraticShellModEightCount n 0 +
        identityQuadraticShellModEightCount n 5 := by
  simp [identityQuadraticShellModEightCount]
  rw [show ((1 : ZMod 8) - 4) = 5 by decide]

/-- Explicit recursive formula for the residue-zero shell count. -/
theorem identityQuadraticShellModEightCount_zero_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 0 =
      identityQuadraticShellModEightCount n 0 +
        2 * identityQuadraticShellModEightCount n 7 +
        identityQuadraticShellModEightCount n 4 := by
  simp [identityQuadraticShellModEightCount]
  rw [show (-1 : ZMod 8) = 7 by decide, show (-4 : ZMod 8) = 4 by decide]

/-- Explicit recursive formula for the residue-five shell count. -/
theorem identityQuadraticShellModEightCount_five_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 5 =
      identityQuadraticShellModEightCount n 5 +
        2 * identityQuadraticShellModEightCount n 4 +
        identityQuadraticShellModEightCount n 1 := by
  simp [identityQuadraticShellModEightCount]
  norm_num

/-- Explicit recursive formula for the residue-two shell count. -/
theorem identityQuadraticShellModEightCount_two_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 2 =
      identityQuadraticShellModEightCount n 2 +
        2 * identityQuadraticShellModEightCount n 1 +
        identityQuadraticShellModEightCount n 6 := by
  norm_num [identityQuadraticShellModEightCount]
  rw [show (-2 : ZMod 8) = 6 by decide]

/-- Explicit recursive formula for the residue-three shell count. -/
theorem identityQuadraticShellModEightCount_three_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 3 =
      identityQuadraticShellModEightCount n 3 +
        2 * identityQuadraticShellModEightCount n 2 +
        identityQuadraticShellModEightCount n 7 := by
  norm_num [identityQuadraticShellModEightCount]
  rw [show (-1 : ZMod 8) = 7 by decide]

/-- Explicit recursive formula for the residue-four shell count. -/
theorem identityQuadraticShellModEightCount_four_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 4 =
      identityQuadraticShellModEightCount n 4 +
        2 * identityQuadraticShellModEightCount n 3 +
        identityQuadraticShellModEightCount n 0 := by
  norm_num [identityQuadraticShellModEightCount]

/-- Explicit recursive formula for the residue-six shell count. -/
theorem identityQuadraticShellModEightCount_six_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 6 =
      identityQuadraticShellModEightCount n 6 +
        2 * identityQuadraticShellModEightCount n 5 +
        identityQuadraticShellModEightCount n 2 := by
  norm_num [identityQuadraticShellModEightCount]

/-- Explicit recursive formula for the residue-seven shell count. -/
theorem identityQuadraticShellModEightCount_seven_succ (n : ℕ) :
    identityQuadraticShellModEightCount (n + 1) 7 =
      identityQuadraticShellModEightCount n 7 +
        2 * identityQuadraticShellModEightCount n 6 +
        identityQuadraticShellModEightCount n 3 := by
  norm_num [identityQuadraticShellModEightCount]

/-- Norm-one vectors are computed by the rank-`n`, residue-`1` shell-count formula. -/
theorem identityQuadraticUnitVectorsModFour_natCard_eq_shellCount (n : ℕ) :
    Nat.card (identityQuadraticUnitVectorsModFour n) =
      identityQuadraticShellModEightCount n 1 := by
  simpa [identityQuadraticUnitVectorsModFour] using
    identityQuadraticShellModEight_natCard_eq_count n (1 : ZMod 8)

/-- There are no norm-one vectors in dimension zero. -/
theorem identityQuadraticUnitVectorsModFour_natCard_zero :
    Nat.card (identityQuadraticUnitVectorsModFour 0) = 0 := by
  simpa [identityQuadraticUnitVectorsModFour] using
    identityQuadraticShellModEight_natCard_zero (1 : ZMod 8)

/-- One-dimensional Type I diagonal modulo-`8` shell counts. -/
theorem identityQuadraticShellModEight_natCard_one (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 1 r) =
      if r = 0 then 1 else if r = 1 then 2 else if r = 4 then 1 else 0 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_zero, identityQuadraticShellModEight_natCard_zero,
    identityQuadraticShellModEight_natCard_zero]
  fin_cases r <;> decide

/-- In dimension one, the Type I norm-one vectors are exactly the two odd
residue classes. -/
theorem identityQuadraticUnitVectorsModFour_natCard_one :
    Nat.card (identityQuadraticUnitVectorsModFour 1) = 2 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_zero, identityQuadraticShellModEight_natCard_zero,
    identityQuadraticShellModEight_natCard_zero]
  decide

/-- Two-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the one-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_two (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 2 r) =
      if r = 0 then 2 else if r = 1 then 4 else if r = 2 then 4 else
      if r = 4 then 2 else if r = 5 then 4 else 0 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_one, identityQuadraticShellModEight_natCard_one,
    identityQuadraticShellModEight_natCard_one]
  fin_cases r <;> decide

/-- In dimension two, the Type I norm-one shell has four elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_two :
    Nat.card (identityQuadraticUnitVectorsModFour 2) = 4 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_one, identityQuadraticShellModEight_natCard_one,
    identityQuadraticShellModEight_natCard_one]
  decide

/-- Three-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the two-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_three (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 3 r) =
      if r = 0 then 4 else if r = 1 then 12 else if r = 2 then 12 else
      if r = 3 then 8 else if r = 4 then 4 else if r = 5 then 12 else
      if r = 6 then 12 else 0 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_two, identityQuadraticShellModEight_natCard_two,
    identityQuadraticShellModEight_natCard_two]
  fin_cases r <;> decide

/-- In dimension three, the Type I norm-one shell has twelve elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_three :
    Nat.card (identityQuadraticUnitVectorsModFour 3) = 12 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_two, identityQuadraticShellModEight_natCard_two,
    identityQuadraticShellModEight_natCard_two]
  decide

/-- Four-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the three-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_four (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 4 r) =
      if r = 0 then 8 else if r = 1 then 32 else if r = 2 then 48 else
      if r = 3 then 32 else if r = 4 then 24 else if r = 5 then 32 else
      if r = 6 then 48 else 32 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_three, identityQuadraticShellModEight_natCard_three,
    identityQuadraticShellModEight_natCard_three]
  fin_cases r <;> decide

/-- In dimension four, the Type I norm-one shell has thirty-two elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_four :
    Nat.card (identityQuadraticUnitVectorsModFour 4) = 32 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_three, identityQuadraticShellModEight_natCard_three,
    identityQuadraticShellModEight_natCard_three]
  decide


/-- Five-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the four-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_five (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 5 r) =
      if r = 0 then 96 else if r = 1 then 80 else if r = 2 then 160 else
      if r = 3 then 160 else if r = 4 then 96 else if r = 5 then 112 else
      if r = 6 then 160 else 160 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_four, identityQuadraticShellModEight_natCard_four,
    identityQuadraticShellModEight_natCard_four]
  fin_cases r <;> decide

/-- In dimension five, the Type I norm-one shell has eighty elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_five :
    Nat.card (identityQuadraticUnitVectorsModFour 5) = 80 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_four, identityQuadraticShellModEight_natCard_four,
    identityQuadraticShellModEight_natCard_four]
  decide

/-- Six-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the five-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_six (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 6 r) =
      if r = 0 then 512 else if r = 1 then 384 else if r = 2 then 480 else
      if r = 3 then 640 else if r = 4 then 512 else if r = 5 then 384 else
      if r = 6 then 544 else 640 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_five, identityQuadraticShellModEight_natCard_five,
    identityQuadraticShellModEight_natCard_five]
  fin_cases r <;> decide

/-- In dimension six, the Type I norm-one shell has three hundred eighty-four elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_six :
    Nat.card (identityQuadraticUnitVectorsModFour 6) = 384 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_five, identityQuadraticShellModEight_natCard_five,
    identityQuadraticShellModEight_natCard_five]
  decide

/-- Seven-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the six-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_seven (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 7 r) =
      if r = 0 then 2304 else if r = 1 then 1792 else if r = 2 then 1792 else
      if r = 3 then 2240 else if r = 4 then 2304 else if r = 5 then 1792 else
      if r = 6 then 1792 else 2368 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_six, identityQuadraticShellModEight_natCard_six,
    identityQuadraticShellModEight_natCard_six]
  fin_cases r <;> decide

/-- In dimension seven, the Type I norm-one shell has seventeen hundred ninety-two elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_seven :
    Nat.card (identityQuadraticUnitVectorsModFour 7) = 1792 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_six, identityQuadraticShellModEight_natCard_six,
    identityQuadraticShellModEight_natCard_six]
  decide

/-- Eight-dimensional Type I diagonal modulo-`8` shell counts, obtained directly
from the explicit shell recurrence and the seven-dimensional shell table. -/
theorem identityQuadraticShellModEight_natCard_eight (r : ZMod 8) :
    Nat.card (identityQuadraticShellModEight 8 r) =
      if r = 0 then 9344 else if r = 1 then 8192 else if r = 2 then 7168 else
      if r = 3 then 8192 else if r = 4 then 9088 else if r = 5 then 8192 else
      if r = 6 then 7168 else 8192 := by
  rw [identityQuadraticShellModEight_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_seven, identityQuadraticShellModEight_natCard_seven,
    identityQuadraticShellModEight_natCard_seven]
  fin_cases r <;> decide

/-- In dimension eight, the Type I norm-one shell has eight thousand one hundred ninety-two elements. -/
theorem identityQuadraticUnitVectorsModFour_natCard_eight :
    Nat.card (identityQuadraticUnitVectorsModFour 8) = 8192 := by
  rw [identityQuadraticUnitVectorsModFour_natCard_succ_explicit]
  rw [identityQuadraticShellModEight_natCard_seven, identityQuadraticShellModEight_natCard_seven,
    identityQuadraticShellModEight_natCard_seven]
  decide


/-- The coordinate basis vector in `(ZMod 4)^n` with a `1` in coordinate `j`. -/
def identityQuadraticBasisVectorModFour {n : ℕ} (j : Fin n) : Fin n → ZMod 4 :=
  Pi.single j (1 : ZMod 4)

/-- Every coordinate basis vector has diagonal Type I norm `1` modulo `8`. -/
theorem identityQuadraticBasisVectorModFour_mem_unitVectors {n : ℕ} (j : Fin n) :
    identityQuadraticModEight (identityQuadraticBasisVectorModFour j) = 1 := by
  rw [identityQuadraticBasisVectorModFour, identityQuadraticModEight_single]
  change ((1 : ZMod 8) ^ 2 : ZMod 8) = 1
  norm_num

/-- A coordinate basis vector extracts the corresponding diagonal bilinear
coordinate. -/
theorem identityBilinearModFour_basis_right {n : ℕ} (v : Fin n → ZMod 4) (j : Fin n) :
    identityBilinearModFour v (identityQuadraticBasisVectorModFour j) = v j := by
  rw [identityBilinearModFour, Finset.sum_eq_single j]
  · simp [identityQuadraticBasisVectorModFour]
  · intro k _ hk
    simp [identityQuadraticBasisVectorModFour, Pi.single_eq_of_ne hk]
  · intro hj
    simp at hj

/-- The diagonal bilinear form is symmetric. -/
theorem identityBilinearModFour_comm {n : ℕ} (v w : Fin n → ZMod 4) :
    identityBilinearModFour v w = identityBilinearModFour w v := by
  rw [identityBilinearModFour, identityBilinearModFour]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The diagonal bilinear form is additive in the first variable with respect
to subtraction. -/
theorem identityBilinearModFour_sub_left {n : ℕ}
    (v w x : Fin n → ZMod 4) :
    identityBilinearModFour (v - w) x =
      identityBilinearModFour v x - identityBilinearModFour w x := by
  rw [identityBilinearModFour, identityBilinearModFour, identityBilinearModFour]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- The diagonal bilinear form is additive in the second variable with respect
to subtraction. -/
theorem identityBilinearModFour_sub_right {n : ℕ}
    (v x y : Fin n → ZMod 4) :
    identityBilinearModFour v (x - y) =
      identityBilinearModFour v x - identityBilinearModFour v y := by
  rw [identityBilinearModFour_comm v (x - y)]
  rw [identityBilinearModFour_sub_left]
  rw [identityBilinearModFour_comm x v, identityBilinearModFour_comm y v]

/-- Pulling a constant out of the second variable of the diagonal bilinear
form. -/
theorem identityBilinearModFour_const_mul_right {n : ℕ}
    (v w : Fin n → ZMod 4) (a : ZMod 4) :
    identityBilinearModFour v (fun i => a * w i) =
      a * identityBilinearModFour v w := by
  rw [identityBilinearModFour, identityBilinearModFour]
  calc
    (∑ i, v i * (a * w i)) = ∑ i, a * (v i * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a * ∑ i, v i * w i := by
      rw [Finset.mul_sum]

/-- Reducing a lifted `ZMod 4` square from `ZMod 8` back to `ZMod 4` gives the
ordinary square. -/
theorem zmodFourLiftToZModEight_sq_castHom (a : ZMod 4) :
    (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4))
        (zmodFourLiftToZModEight a ^ 2) = a ^ 2 := by
  fin_cases a <;> decide

/-- Reducing a lifted `ZMod 4` element from `ZMod 8` back to `ZMod 4` gives
the original element. -/
theorem zmodFourLiftToZModEight_cast (a : ZMod 4) :
    (zmodFourLiftToZModEight a).cast = a := by
  fin_cases a <;> decide

/-- Reducing the diagonal Type I norm modulo `8` to modulo `4` gives the
self-bilinear value. -/
theorem identityBilinearModFour_self_eq_cast_identityQuadraticModEight {n : ℕ}
    (v : Fin n → ZMod 4) :
    identityBilinearModFour v v =
      (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)) (identityQuadraticModEight v) := by
  rw [identityQuadraticModEight]
  rw [map_sum]
  simp [zmodFourLiftToZModEight_cast, identityBilinearModFour, pow_two]

/-- A vector of diagonal Type I norm `1` modulo `8` has self-bilinear value
`1` modulo `4`. -/
theorem identityBilinearModFour_self_of_identityQuadraticModEight_eq_one {n : ℕ}
    {v : Fin n → ZMod 4} (hunit : identityQuadraticModEight v = 1) :
    identityBilinearModFour v v = 1 := by
  rw [identityBilinearModFour_self_eq_cast_identityQuadraticModEight, hunit]
  rfl

/-- The fixed first coordinate vector in `(ZMod 4)^(n+1)`. -/
def identityQuadraticFirstBasisVectorModFour (n : ℕ) : Fin (n + 1) → ZMod 4 :=
  Pi.single (0 : Fin (n + 1)) (1 : ZMod 4)

/-- The fixed first coordinate vector has diagonal Type I norm `1` modulo `8`. -/
theorem identityQuadraticFirstBasisVectorModFour_mem_unitVectors (n : ℕ) :
    identityQuadraticModEight (identityQuadraticFirstBasisVectorModFour n) = 1 := by
  rw [identityQuadraticFirstBasisVectorModFour, identityQuadraticModEight_single]
  change ((1 : ZMod 8) ^ 2 : ZMod 8) = 1
  norm_num

/-- The elementary reflection matrix attached to an ordinary Type I first-column
candidate `v` and an even coordinate `j`.  The later preservation proof uses
the standard formula `I - (1 - v_j) (v - e_j)(v - e_j)^t` over `ZMod 4`. -/
def identityQuadraticOrdinaryReflectionMatrix {n : ℕ} (v : Fin n → ZMod 4) (j : Fin n) :
    Matrix (Fin n) (Fin n) (ZMod 4) :=
  fun i k => (if i = k then 1 else 0) -
    (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
      (v k - identityQuadraticBasisVectorModFour j k)

/-- The ordinary reflection matrix sends the chosen basis vector to `v` whenever
the chosen coordinate of `v` is even. -/
theorem identityQuadraticOrdinaryReflectionMatrix_mulVec_basis {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hven : v j = 0 ∨ v j = 2) :
    (identityQuadraticOrdinaryReflectionMatrix v j).mulVec
      (identityQuadraticBasisVectorModFour j) = v := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  simp only [identityQuadraticOrdinaryReflectionMatrix]
  have hsum :
      (∑ k, ((if i = k then 1 else 0) -
        (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          (v k - identityQuadraticBasisVectorModFour j k)) *
          identityQuadraticBasisVectorModFour j k) =
        ((if i = j then 1 else 0) -
          (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
            (v j - 1)) := by
    rw [Finset.sum_eq_single j]
    · simp [identityQuadraticBasisVectorModFour]
    · intro k _ hk
      simp [identityQuadraticBasisVectorModFour, Pi.single_eq_of_ne hk]
    · intro hj
      simp at hj
  rw [hsum]
  rcases hven with h0 | h2
  · by_cases hij : i = j
    · subst i
      simp [identityQuadraticBasisVectorModFour, h0]
    · simp [identityQuadraticBasisVectorModFour, h0, hij]
  · by_cases hij : i = j
    · subst i
      simp [identityQuadraticBasisVectorModFour, h2]
      ring
    · simp [identityQuadraticBasisVectorModFour, h2, hij]
      ring

/-- The ordinary reflection matrix acts as the expected rank-one update. -/
theorem identityQuadraticOrdinaryReflectionMatrix_mulVec {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (x : Fin n → ZMod 4) :
    (identityQuadraticOrdinaryReflectionMatrix v j).mulVec x =
      x - fun i : Fin n =>
        ((1 - v j) * identityBilinearModFour
          (v - identityQuadraticBasisVectorModFour j) x) *
          (v i - identityQuadraticBasisVectorModFour j i) := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  simp only [identityQuadraticOrdinaryReflectionMatrix]
  let w : Fin n → ZMod 4 := v - identityQuadraticBasisVectorModFour j
  have hdiag : (∑ k, (if i = k then 1 else 0 : ZMod 4) * x k) = x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      have hik : i ≠ k := fun h => hki h.symm
      simp [hik]
    · intro hi
      simp at hi
  have hrank :
      (∑ k, ((1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
            (v k - identityQuadraticBasisVectorModFour j k)) * x k) =
        (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          identityBilinearModFour w x := by
    rw [identityBilinearModFour]
    calc
      (∑ k, ((1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
            (v k - identityQuadraticBasisVectorModFour j k)) * x k) =
          ∑ k, ((1 - v j) * (v i - identityQuadraticBasisVectorModFour j i)) *
            ((v k - identityQuadraticBasisVectorModFour j k) * x k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          ∑ k, (v k - identityQuadraticBasisVectorModFour j k) * x k := by
        rw [Finset.mul_sum]
      _ = (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          ∑ k, w k * x k := by
        rfl
  calc
    (∑ k, ((if i = k then 1 else 0) -
        (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          (v k - identityQuadraticBasisVectorModFour j k)) * x k) =
        (∑ k, (if i = k then 1 else 0 : ZMod 4) * x k) -
          ∑ k, ((1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
            (v k - identityQuadraticBasisVectorModFour j k)) * x k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = x i - (1 - v j) * (v i - identityQuadraticBasisVectorModFour j i) *
          identityBilinearModFour w x := by
      rw [hdiag, hrank]
    _ = (x - fun i : Fin n =>
        ((1 - v j) * identityBilinearModFour
          (v - identityQuadraticBasisVectorModFour j) x) *
          (v i - identityQuadraticBasisVectorModFour j i)) i := by
      simp only [Pi.sub_apply]
      ring

/-- The ordinary reflection matrix also sends the target column back to the
chosen coordinate basis vector. -/
theorem identityQuadraticOrdinaryReflectionMatrix_mulVec_target {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hunit : identityQuadraticModEight v = 1)
    (hven : v j = 0 ∨ v j = 2) :
    (identityQuadraticOrdinaryReflectionMatrix v j).mulVec v =
      identityQuadraticBasisVectorModFour j := by
  have hbvv : identityBilinearModFour v v = 1 :=
    identityBilinearModFour_self_of_identityQuadraticModEight_eq_one hunit
  have hbe : identityBilinearModFour (identityQuadraticBasisVectorModFour j) v = v j := by
    rw [identityBilinearModFour_comm, identityBilinearModFour_basis_right]
  have hb :
      identityBilinearModFour (v - identityQuadraticBasisVectorModFour j) v =
        1 - v j := by
    rw [identityBilinearModFour_sub_left, hbvv, hbe]
  rw [identityQuadraticOrdinaryReflectionMatrix_mulVec]
  funext i
  simp only [Pi.sub_apply, hb]
  rcases hven with h0 | h2
  · by_cases hij : i = j
    · subst i
      simp [identityQuadraticBasisVectorModFour, h0]
    · simp [identityQuadraticBasisVectorModFour, h0, hij]
  · by_cases hij : i = j
    · subst i
      simp [identityQuadraticBasisVectorModFour, h2]
      ring
    · simp [identityQuadraticBasisVectorModFour, h2, hij]
      ring

/-- The difference `v - e_j` has the expected norm for an ordinary norm-one
target column with even `j`th coordinate. -/
theorem identityQuadraticOrdinaryReflectionVector_norm {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hunit : identityQuadraticModEight v = 1)
    (hven : v j = 0 ∨ v j = 2) :
    identityQuadraticModEight (v - identityQuadraticBasisVectorModFour j) =
      if v j = 0 then 2 else 6 := by
  rw [identityQuadraticModEight_sub, hunit, identityQuadraticBasisVectorModFour_mem_unitVectors,
    identityBilinearModFour_basis_right]
  rcases hven with h0 | h2
  · simp [h0, zmodFourLiftToZModEight]
    decide
  · simp [h2, zmodFourLiftToZModEight]
    decide

/-- The reflection vector `v - e_j` has self-bilinear value `2` modulo `4`. -/
theorem identityBilinearModFour_reflectionVector_self {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hunit : identityQuadraticModEight v = 1)
    (hven : v j = 0 ∨ v j = 2) :
    identityBilinearModFour
        (v - identityQuadraticBasisVectorModFour j)
        (v - identityQuadraticBasisVectorModFour j) = 2 := by
  rw [identityBilinearModFour_self_eq_cast_identityQuadraticModEight]
  have hQ := identityQuadraticOrdinaryReflectionVector_norm v j hunit hven
  rcases hven with h0 | h2
  · rw [hQ]
    simp only [h0, ↓reduceIte]
    change ((2 : ZMod 8).cast : ZMod 4) = 2
    decide
  · rw [hQ]
    simp only [h2]
    change ((6 : ZMod 8).cast : ZMod 4) = 2
    decide

/-- The ordinary reflection is an involution on vectors. -/
theorem identityQuadraticOrdinaryReflectionMatrix_mulVec_mulVec {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hunit : identityQuadraticModEight v = 1)
    (hven : v j = 0 ∨ v j = 2) (x : Fin n → ZMod 4) :
    (identityQuadraticOrdinaryReflectionMatrix v j).mulVec
        ((identityQuadraticOrdinaryReflectionMatrix v j).mulVec x) = x := by
  let R := identityQuadraticOrdinaryReflectionMatrix v j
  let w : Fin n → ZMod 4 := v - identityQuadraticBasisVectorModFour j
  let b : ZMod 4 := identityBilinearModFour w x
  let c : ZMod 4 := 1 - v j
  let a : ZMod 4 := c * b
  have hRx : R.mulVec x = x - fun i : Fin n => a * w i := by
    simpa [R, w, b, c, a] using identityQuadraticOrdinaryReflectionMatrix_mulVec v j x
  have hBww : identityBilinearModFour w w = 2 := by
    simpa [w] using identityBilinearModFour_reflectionVector_self v j hunit hven
  have hBRx : identityBilinearModFour w (R.mulVec x) = b - a * 2 := by
    rw [hRx, identityBilinearModFour_sub_right]
    rw [identityBilinearModFour_const_mul_right, hBww]
  rw [identityQuadraticOrdinaryReflectionMatrix_mulVec]
  have hBRx' :
      identityBilinearModFour (v - identityQuadraticBasisVectorModFour j)
          ((identityQuadraticOrdinaryReflectionMatrix v j).mulVec x) = b - a * 2 := by
    simpa [R, w] using hBRx
  simp only [hBRx']
  funext i
  rw [hRx]
  simp only [Pi.sub_apply]
  rcases hven with h0 | h2
  · simp [a, b, c, w, h0]
    ring_nf
  · simp [a, b, c, w, h2]
    ring_nf
    have hfour : (4 : ZMod 4) = 0 := by decide
    simp [hfour]

/-- The ordinary reflection matrix preserves the diagonal Type I quadratic form
modulo `8` when `v` is norm-one and has an even coordinate at `j`. -/
theorem identityQuadraticOrdinaryReflectionMatrix_preserves {n : ℕ}
    (v : Fin n → ZMod 4) (j : Fin n) (hunit : identityQuadraticModEight v = 1)
    (hven : v j = 0 ∨ v j = 2) (x : Fin n → ZMod 4) :
    identityQuadraticModEight ((identityQuadraticOrdinaryReflectionMatrix v j).mulVec x) =
      identityQuadraticModEight x := by
  let w : Fin n → ZMod 4 := v - identityQuadraticBasisVectorModFour j
  let b : ZMod 4 := identityBilinearModFour w x
  let a : ZMod 4 := (1 - v j) * b
  have hmul : (identityQuadraticOrdinaryReflectionMatrix v j).mulVec x =
      x - fun i : Fin n => a * w i := by
    simpa [w, b, a] using identityQuadraticOrdinaryReflectionMatrix_mulVec v j x
  have hQw : identityQuadraticModEight w = if v j = 0 then 2 else 6 := by
    simpa [w] using identityQuadraticOrdinaryReflectionVector_norm v j hunit hven
  have hbil : identityBilinearModFour x (fun i : Fin n => a * w i) = a * b := by
    rw [identityBilinearModFour]
    calc
      (∑ i, x i * (a * w i)) = a * ∑ i, w i * x i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = a * b := by
        rfl
  rw [hmul, identityQuadraticModEight_sub, identityQuadraticModEight_const_mul, hbil]
  have hextra :
      zmodFourLiftToZModEight a ^ 2 * identityQuadraticModEight w -
          (2 : ZMod 8) * zmodFourLiftToZModEight (a * b) = 0 := by
    rcases hven with h0 | h2
    · have hQw0 : identityQuadraticModEight w = 2 := by
        simpa [h0] using hQw
      have ha : a = b := by
        simp [a, h0]
      rw [hQw0, ha]
      have hcase : ∀ t : ZMod 4,
          zmodFourLiftToZModEight t ^ 2 * 2 -
            (2 : ZMod 8) * zmodFourLiftToZModEight (t * t) = 0 := by
        intro t
        fin_cases t <;> decide
      exact hcase b
    · have hQw2 : identityQuadraticModEight w = 6 := by
        simpa [h2] using hQw
      have ha : a = 3 * b := by
        simp [a, h2]
        have hcase : ∀ t : ZMod 4, ((1 - 2 : ZMod 4) * t) = 3 * t := by
          intro t
          fin_cases t <;> decide
        exact hcase b
      rw [hQw2, ha]
      have hcase : ∀ t : ZMod 4,
          zmodFourLiftToZModEight (3 * t) ^ 2 * 6 -
            (2 : ZMod 8) * zmodFourLiftToZModEight ((3 * t) * t) = 0 := by
        intro t
        fin_cases t <;> decide
      exact hcase b
  calc
    identityQuadraticModEight x + zmodFourLiftToZModEight a ^ 2 *
          identityQuadraticModEight w -
        (2 : ZMod 8) * zmodFourLiftToZModEight (a * b) =
        identityQuadraticModEight x +
          (zmodFourLiftToZModEight a ^ 2 * identityQuadraticModEight w -
            (2 : ZMod 8) * zmodFourLiftToZModEight (a * b)) := by
      ring
    _ = identityQuadraticModEight x := by
      rw [hextra]
      ring

/-- The ordinary reflection matrix, packaged as a Type I diagonal quadratic
isometry modulo `4`. -/
def identityQuadraticOrdinaryReflectionIsometry {n : ℕ}
    (v : identityQuadraticUnitVectorsModFour n) (j : Fin n)
    (hven : v.1 j = 0 ∨ v.1 j = 2) : identityQuadraticIsometryModFour n :=
  ⟨identityQuadraticOrdinaryReflectionMatrix v.1 j,
    identityQuadraticOrdinaryReflectionMatrix_preserves v.1 j v.2 hven⟩

/-- The packaged ordinary reflection isometry sends the chosen basis vector to
the target norm-one vector. -/
theorem identityQuadraticOrdinaryReflectionIsometry_mulVec_basis {n : ℕ}
    (v : identityQuadraticUnitVectorsModFour n) (j : Fin n)
    (hven : v.1 j = 0 ∨ v.1 j = 2) :
    (identityQuadraticOrdinaryReflectionIsometry v j hven).1.mulVec
      (identityQuadraticBasisVectorModFour j) = v.1 := by
  exact identityQuadraticOrdinaryReflectionMatrix_mulVec_basis v.1 j hven

/-- The packaged ordinary reflection isometry sends the target vector back to
the chosen coordinate basis vector. -/
theorem identityQuadraticOrdinaryReflectionIsometry_mulVec_target {n : ℕ}
    (v : identityQuadraticUnitVectorsModFour n) (j : Fin n)
    (hven : v.1 j = 0 ∨ v.1 j = 2) :
    (identityQuadraticOrdinaryReflectionIsometry v j hven).1.mulVec v.1 =
      identityQuadraticBasisVectorModFour j := by
  exact identityQuadraticOrdinaryReflectionMatrix_mulVec_target v.1 j v.2 hven

/-- The packaged ordinary reflection isometry is an involution on vectors. -/
theorem identityQuadraticOrdinaryReflectionIsometry_mulVec_mulVec {n : ℕ}
    (v : identityQuadraticUnitVectorsModFour n) (j : Fin n)
    (hven : v.1 j = 0 ∨ v.1 j = 2) (x : Fin n → ZMod 4) :
    (identityQuadraticOrdinaryReflectionIsometry v j hven).1.mulVec
        ((identityQuadraticOrdinaryReflectionIsometry v j hven).1.mulVec x) = x := by
  exact identityQuadraticOrdinaryReflectionMatrix_mulVec_mulVec v.1 j v.2 hven x

/-- The coordinate-permutation matrix attached to a permutation of the Type I
diagonal coordinates.  Its action sends `e_j` to `e_{σ j}`. -/
def identityQuadraticPermutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) (ZMod 4) :=
  fun i j => if i = σ j then 1 else 0

/-- A coordinate-permutation matrix acts by permuting vector coordinates. -/
theorem identityQuadraticPermutationMatrix_mulVec {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 4) :
    (identityQuadraticPermutationMatrix σ).mulVec x = fun i : Fin n => x (σ.symm i) := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp [identityQuadraticPermutationMatrix]
  · intro k _ hk
    have hik : i ≠ σ k := by
      intro h
      apply hk
      exact (by simpa using (congrArg σ.symm h).symm)
    simp [identityQuadraticPermutationMatrix, hik]
  · intro hmem
    simp at hmem

/-- Coordinate permutations preserve the diagonal Type I quadratic form modulo
`8`. -/
theorem identityQuadraticPermutationMatrix_preserves {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 4) :
    identityQuadraticModEight ((identityQuadraticPermutationMatrix σ).mulVec x) =
      identityQuadraticModEight x := by
  rw [identityQuadraticPermutationMatrix_mulVec]
  rw [identityQuadraticModEight, identityQuadraticModEight]
  exact σ.symm.sum_comp (fun i : Fin n => zmodFourLiftToZModEight (x i) ^ 2)

/-- A coordinate permutation, packaged as a Type I diagonal quadratic isometry. -/
def identityQuadraticPermutationIsometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    identityQuadraticIsometryModFour n :=
  ⟨identityQuadraticPermutationMatrix σ, identityQuadraticPermutationMatrix_preserves σ⟩

/-- A packaged coordinate-permutation isometry sends `e_j` to `e_{σ j}`. -/
theorem identityQuadraticPermutationIsometry_mulVec_basis {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (identityQuadraticPermutationIsometry σ).1.mulVec
      (identityQuadraticBasisVectorModFour j) = identityQuadraticBasisVectorModFour (σ j) := by
  rw [identityQuadraticPermutationIsometry, identityQuadraticPermutationMatrix_mulVec]
  funext i
  by_cases h : i = σ j
  · subst i
    have hs : σ.symm (σ j) = j := by simp
    rw [hs]
    simp [identityQuadraticBasisVectorModFour]
  · have hs : σ.symm i ≠ j := by
      intro hs
      apply h
      rw [← hs]
      simp
    simp [identityQuadraticBasisVectorModFour, h, hs]

/-- The coordinate swap moving the first basis vector to the chosen coordinate,
packaged as a Type I diagonal quadratic isometry. -/
def identityQuadraticSwapFirstToCoordinateIsometry (n : ℕ) (j : Fin (n + 1)) :
    identityQuadraticIsometryModFour (n + 1) :=
  identityQuadraticPermutationIsometry (Equiv.swap (0 : Fin (n + 1)) j)

/-- The coordinate swap transporter sends the fixed first basis vector to the
chosen coordinate basis vector. -/
theorem identityQuadraticSwapFirstToCoordinateIsometry_mulVec_first (n : ℕ)
    (j : Fin (n + 1)) :
    (identityQuadraticSwapFirstToCoordinateIsometry n j).1.mulVec
        (identityQuadraticFirstBasisVectorModFour n) =
      identityQuadraticBasisVectorModFour j := by
  simpa [identityQuadraticSwapFirstToCoordinateIsometry,
    identityQuadraticFirstBasisVectorModFour, identityQuadraticBasisVectorModFour,
    Equiv.swap_apply_left] using
    identityQuadraticPermutationIsometry_mulVec_basis
      (Equiv.swap (0 : Fin (n + 1)) j) (0 : Fin (n + 1))

/-- The coordinate swap transporter sends the chosen coordinate basis vector
back to the fixed first basis vector. -/
theorem identityQuadraticSwapFirstToCoordinateIsometry_mulVec_coordinate (n : ℕ)
    (j : Fin (n + 1)) :
    (identityQuadraticSwapFirstToCoordinateIsometry n j).1.mulVec
        (identityQuadraticBasisVectorModFour j) =
      identityQuadraticFirstBasisVectorModFour n := by
  simpa [identityQuadraticSwapFirstToCoordinateIsometry,
    identityQuadraticFirstBasisVectorModFour, identityQuadraticBasisVectorModFour]
    using identityQuadraticPermutationIsometry_mulVec_basis
      (Equiv.swap (0 : Fin (n + 1)) j) j

/-- The coordinate swap transporter is an involution on vectors. -/
theorem identityQuadraticSwapFirstToCoordinateIsometry_mulVec_mulVec (n : ℕ)
    (j : Fin (n + 1)) (x : Fin (n + 1) → ZMod 4) :
    (identityQuadraticSwapFirstToCoordinateIsometry n j).1.mulVec
        ((identityQuadraticSwapFirstToCoordinateIsometry n j).1.mulVec x) = x := by
  rw [identityQuadraticSwapFirstToCoordinateIsometry,
    identityQuadraticPermutationIsometry, identityQuadraticPermutationMatrix_mulVec,
    identityQuadraticPermutationMatrix_mulVec]
  funext i
  simp

/-- Multiplication by the fixed first basis vector extracts the first column. -/
theorem matrix_mulVec_identityQuadraticFirstBasisVectorModFour {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4)) :
    M.mulVec (identityQuadraticFirstBasisVectorModFour n) = fun i => M i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [identityQuadraticFirstBasisVectorModFour]
  · intro k _ hk
    simp [identityQuadraticFirstBasisVectorModFour, Pi.single_eq_of_ne hk]
  · intro hmem
    simp at hmem

/-- Multiplication by a coordinate basis vector extracts the corresponding
column. -/
theorem matrix_mulVec_identityQuadraticBasisVectorModFour {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 4)) (j : Fin n) :
    M.mulVec (identityQuadraticBasisVectorModFour j) = fun i => M i j := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp [identityQuadraticBasisVectorModFour]
  · intro k _ hk
    simp [identityQuadraticBasisVectorModFour, Pi.single_eq_of_ne hk]
  · intro hmem
    simp at hmem

/-- Two matrices over `(ZMod 4)^n` are equal if they have the same action on
all vectors. -/
theorem matrix_eq_of_mulVec_eq {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) (ZMod 4)}
    (h : ∀ x : Fin n → ZMod 4, M.mulVec x = N.mulVec x) : M = N := by
  ext i j
  have hj := congrFun (h (identityQuadraticBasisVectorModFour j)) i
  simpa [matrix_mulVec_identityQuadraticBasisVectorModFour] using hj

/-- Composition of two Type I diagonal quadratic isometries modulo `4`. -/
def identityQuadraticIsometryModFour_comp {n : ℕ}
    (Y X : identityQuadraticIsometryModFour n) : identityQuadraticIsometryModFour n :=
  ⟨Y.1 * X.1, by
    intro v
    rw [← Matrix.mulVec_mulVec]
    rw [Y.2, X.2]⟩


/-- The first-column map from Type I identity quadratic isometries to norm-one
vectors.  This is the first finite-count projection for the Type I dyadic
recurrence. -/
def identityQuadraticIsometryModFourFirstColumnMap (n : ℕ) :
    identityQuadraticIsometryModFour (n + 1) → identityQuadraticUnitVectorsModFour (n + 1) :=
  fun X => ⟨fun i : Fin (n + 1) => X.1 i 0,
    identityQuadraticIsometryModFour_column_norm X (0 : Fin (n + 1))⟩

/-- The fixed first-column unit vector, packaged in the norm-one shell. -/
def identityQuadraticFirstColumnUnitVector (n : ℕ) :
    identityQuadraticUnitVectorsModFour (n + 1) :=
  ⟨identityQuadraticFirstBasisVectorModFour n,
    identityQuadraticFirstBasisVectorModFour_mem_unitVectors n⟩

/-- The fiber of the first-column map over a prescribed norm-one first column. -/
abbrev identityQuadraticIsometryModFourFirstColumnFiber (n : ℕ)
    (v : identityQuadraticUnitVectorsModFour (n + 1)) : Type :=
  {X : identityQuadraticIsometryModFour (n + 1) //
    identityQuadraticIsometryModFourFirstColumnMap n X = v}

/-- Uniform fibers of the first-column map give the Type I identity finite-count
factorization.  The remaining mathematical task is the direct computation of
these fibers and the norm-one vector count. -/
theorem identityQuadraticIsometryModFour_natCard_eq_unitVectors_mul_of_firstColumn_fiber_card
    (n c : ℕ)
    (hfiber : ∀ v : identityQuadraticUnitVectorsModFour (n + 1),
      Nat.card (identityQuadraticIsometryModFourFirstColumnFiber n v) = c) :
    Nat.card (identityQuadraticIsometryModFour (n + 1)) =
      Nat.card (identityQuadraticUnitVectorsModFour (n + 1)) * c := by
  exact nat_card_eq_mul_of_fiber_card (identityQuadraticIsometryModFourFirstColumnMap n) c hfiber

/-- The first-column stabilizer of the fixed first basis vector inside the Type I
identity finite target. -/
abbrev identityQuadraticIsometryModFourFirstColumnStabilizer (n : ℕ) : Type :=
  identityQuadraticIsometryModFourFirstColumnFiber n (identityQuadraticFirstColumnUnitVector n)

noncomputable instance (n : ℕ) :
    Fintype (identityQuadraticIsometryModFourFirstColumnStabilizer n) := by
  unfold identityQuadraticIsometryModFourFirstColumnStabilizer
  infer_instance

/-- In `ZMod 4`, the elements whose canonical lift is killed by multiplication
by `2` in `ZMod 8` are exactly the even residue classes. -/
theorem zmodFour_eq_zero_or_two_of_two_mul_lift_eq_zero (a : ZMod 4)
    (ha : (2 : ZMod 8) * zmodFourLiftToZModEight a = 0) :
    a = 0 ∨ a = 2 := by
  have ha' : (((2 * a.val : ℕ) : ZMod 8) = 0) := by
    simpa [zmodFourLiftToZModEight, Nat.cast_mul] using ha
  have hdiv : 8 ∣ 2 * a.val := by
    exact (ZMod.natCast_eq_zero_iff (2 * a.val) 8).mp ha'
  have hlt : a.val < 4 := ZMod.val_lt a
  have hcases : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · left
    exact (ZMod.val_eq_zero a).mp h0
  · exfalso
    rw [h1] at hdiv
    rcases hdiv with ⟨k, hk⟩
    omega
  · right
    rw [← ZMod.natCast_zmod_val a, h2]
    norm_num
  · exfalso
    rw [h3] at hdiv
    rcases hdiv with ⟨k, hk⟩
    omega

/-- Reduction from `ZMod 4` to parity. -/
def zmodFourToZModTwo : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

/-- Reduction from `ZMod 8` to parity. -/
def zmodEightToZModTwo : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

/-- A vector over `ZMod 4` is characteristic for the Type I diagonal target when
all its coordinates are odd. -/
def identityQuadraticAllOddModFour {n : ℕ} (v : Fin n → ZMod 4) : Prop :=
  ∀ i, v i = 1 ∨ v i = 3

/-- A vector over `ZMod 4` is ordinary for the Type I diagonal target when at
least one coordinate is even.  This is the complement of the all-odd
characteristic shell used in the corrected Type I first-column recurrence. -/
def identityQuadraticHasEvenCoordinateModFour {n : ℕ} (v : Fin n → ZMod 4) : Prop :=
  ∃ i, v i = 0 ∨ v i = 2

/-- Every `ZMod 4` residue is either even (`0` or `2`) or odd (`1` or `3`). -/
theorem zmodFour_even_or_odd (a : ZMod 4) :
    (a = 0 ∨ a = 2) ∨ (a = 1 ∨ a = 3) := by
  fin_cases a
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

/-- All-odd and has-an-even-coordinate are disjoint. -/
theorem identityQuadraticAllOddModFour_not_hasEvenCoordinate {n : ℕ}
    {v : Fin n → ZMod 4} (hodd : identityQuadraticAllOddModFour v) :
    ¬ identityQuadraticHasEvenCoordinateModFour v := by
  rintro ⟨i, h0 | h2⟩
  · rcases hodd i with h1 | h3
    · have hneq : (0 : ZMod 4) ≠ 1 := by decide
      exact hneq (h0.symm.trans h1)
    · have hneq : (0 : ZMod 4) ≠ 3 := by decide
      exact hneq (h0.symm.trans h3)
  · rcases hodd i with h1 | h3
    · have hneq : (2 : ZMod 4) ≠ 1 := by decide
      exact hneq (h2.symm.trans h1)
    · have hneq : (2 : ZMod 4) ≠ 3 := by decide
      exact hneq (h2.symm.trans h3)

/-- For finite `ZMod 4` coordinate vectors, having an even coordinate is exactly
the negation of being all-odd. -/
theorem identityQuadraticHasEvenCoordinateModFour_iff_not_allOdd {n : ℕ}
    (v : Fin n → ZMod 4) :
    identityQuadraticHasEvenCoordinateModFour v ↔
      ¬ identityQuadraticAllOddModFour v := by
  constructor
  · intro heven hodd
    exact identityQuadraticAllOddModFour_not_hasEvenCoordinate hodd heven
  · intro hnot
    by_contra hnoeven
    apply hnot
    intro i
    rcases zmodFour_even_or_odd (v i) with (h0 | h2) | hodd
    · exact False.elim (hnoeven ⟨i, Or.inl h0⟩)
    · exact False.elim (hnoeven ⟨i, Or.inr h2⟩)
    · exact hodd

/-- An all-odd vector has diagonal Type I quadratic value equal to the rank
modulo `8`. -/
theorem identityQuadraticModEight_eq_rank_of_allOdd {n : ℕ} {v : Fin n → ZMod 4}
    (hodd : identityQuadraticAllOddModFour v) :
    identityQuadraticModEight v = (n : ZMod 8) := by
  rw [identityQuadraticModEight]
  calc
    (∑ i, zmodFourLiftToZModEight (v i) ^ 2) = ∑ _i : Fin n, (1 : ZMod 8) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hodd i with h1 | h3
      · rw [h1]
        change ((1 : ZMod 8) ^ 2 : ZMod 8) = 1
        norm_num
      · rw [h3]
        change ((3 : ZMod 8) ^ 2 : ZMod 8) = 1
        decide
    _ = (n : ZMod 8) := by
      simp

/-- All-odd `ZMod 4` vectors are just independent choices of `1` or `3` in
each coordinate. -/
def identityQuadraticAllOddModFourEquivFinTwo (n : ℕ) :
    {v : Fin n → ZMod 4 // identityQuadraticAllOddModFour v} ≃
      (Fin n → Fin 2) where
  toFun v := fun i => if v.1 i = 1 then 0 else 1
  invFun b :=
    ⟨fun i => if b i = 0 then (1 : ZMod 4) else 3, by
      intro i
      by_cases h : b i = 0
      · simp [h]
      · simp [h]⟩
  left_inv v := by
    ext i
    change
      (if (if v.1 i = 1 then (0 : Fin 2) else 1) = 0 then (1 : ZMod 4) else 3) =
        v.1 i
    rcases v.2 i with h1 | h3
    · simp [h1]
    · rw [h3]
      decide
  right_inv b := by
    funext i
    by_cases h : b i = 0
    · simp [h]
    · have h1 : b i = 1 := by
        apply Fin.ext
        have hlt := (b i).2
        have hne : (b i).val ≠ 0 := by
          intro hval
          apply h
          exact Fin.ext hval
        omega
      rw [h1]
      simp [h]
      decide

noncomputable instance (n : ℕ) :
    Fintype {v : Fin n → ZMod 4 // identityQuadraticAllOddModFour v} := by
  classical
  unfold identityQuadraticAllOddModFour
  infer_instance

/-- Cardinality of the all-odd vectors in `(ZMod 4)^n`. -/
theorem identityQuadraticAllOddModFour_natCard (n : ℕ) :
    Nat.card {v : Fin n → ZMod 4 // identityQuadraticAllOddModFour v} = 2 ^ n := by
  rw [Nat.card_congr (identityQuadraticAllOddModFourEquivFinTwo n)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Characteristic norm-one first-column targets: norm-one columns whose
coordinates are all odd. -/
abbrev identityQuadraticCharacteristicUnitVectorsModFour (n : ℕ) : Type :=
  {v : identityQuadraticUnitVectorsModFour n // identityQuadraticAllOddModFour v.1}

noncomputable instance (n : ℕ) :
    Fintype (identityQuadraticCharacteristicUnitVectorsModFour n) := by
  classical
  unfold identityQuadraticCharacteristicUnitVectorsModFour
  infer_instance

/-- If the rank is `1` modulo `8`, all-odd vectors are exactly the
characteristic norm-one targets. -/
def identityQuadraticCharacteristicUnitVectorsModFourEquivAllOdd (n : ℕ)
    (h : (n : ZMod 8) = 1) :
    identityQuadraticCharacteristicUnitVectorsModFour n ≃
      {v : Fin n → ZMod 4 // identityQuadraticAllOddModFour v} where
  toFun v := ⟨v.1.1, v.2⟩
  invFun v := ⟨⟨v.1, by
      rw [identityQuadraticModEight_eq_rank_of_allOdd v.2, h]⟩, v.2⟩
  left_inv v := by
    ext i
    rfl
  right_inv v := by
    ext i
    rfl

/-- Characteristic norm-one targets have cardinality `2^n` in ranks
`1 mod 8`. -/
theorem identityQuadraticCharacteristicUnitVectorsModFour_natCard_of_rank_mod_eq_one
    (n : ℕ) (h : (n : ZMod 8) = 1) :
    Nat.card (identityQuadraticCharacteristicUnitVectorsModFour n) = 2 ^ n := by
  rw [Nat.card_congr
    (identityQuadraticCharacteristicUnitVectorsModFourEquivAllOdd n h)]
  exact identityQuadraticAllOddModFour_natCard n

/-- Characteristic norm-one targets are empty outside ranks `1 mod 8`. -/
theorem identityQuadraticCharacteristicUnitVectorsModFour_isEmpty_of_rank_mod_ne_one
    (n : ℕ) (h : (n : ZMod 8) ≠ 1) :
    IsEmpty (identityQuadraticCharacteristicUnitVectorsModFour n) := by
  refine ⟨?_⟩
  intro v
  have hQ := identityQuadraticModEight_eq_rank_of_allOdd v.2
  exact h (hQ.symm.trans v.1.2)

/-- Cardinality of the characteristic norm-one targets in every rank. -/
theorem identityQuadraticCharacteristicUnitVectorsModFour_natCard (n : ℕ) :
    Nat.card (identityQuadraticCharacteristicUnitVectorsModFour n) =
      if (n : ZMod 8) = 1 then 2 ^ n else 0 := by
  by_cases h : (n : ZMod 8) = 1
  · rw [identityQuadraticCharacteristicUnitVectorsModFour_natCard_of_rank_mod_eq_one n h]
    simp [h]
  · haveI := identityQuadraticCharacteristicUnitVectorsModFour_isEmpty_of_rank_mod_ne_one n h
    have hzero : Nat.card (identityQuadraticCharacteristicUnitVectorsModFour n) = 0 :=
      Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hzero]
    simp [h]

/-- Modulo parity, the square of a lifted `ZMod 4` coordinate is the coordinate
itself. -/
theorem zmodEightToZModTwo_lift_square (a : ZMod 4) :
    zmodEightToZModTwo (zmodFourLiftToZModEight a ^ 2) = zmodFourToZModTwo a := by
  fin_cases a <;> decide

/-- The Type I diagonal quadratic value reduces modulo `2` to the parity sum of
coordinates. -/
theorem zmodEightToZModTwo_identityQuadraticModEight {n : ℕ} (u : Fin n → ZMod 4) :
    zmodEightToZModTwo (identityQuadraticModEight u) = ∑ i, zmodFourToZModTwo (u i) := by
  rw [identityQuadraticModEight]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact zmodEightToZModTwo_lift_square (u i)

/-- If multiplying the lifted `ZMod 4` residue by `2` vanishes modulo `8`, then
its parity is zero. -/
theorem zmodFourToZModTwo_eq_zero_of_two_mul_lift_eq_zero (a : ZMod 4)
    (ha : (2 : ZMod 8) * zmodFourLiftToZModEight a = 0) :
    zmodFourToZModTwo a = 0 := by
  rcases zmodFour_eq_zero_or_two_of_two_mul_lift_eq_zero a ha with rfl | rfl <;> decide

/-- Pairing with an all-odd vector reduces modulo `2` to summing coordinates. -/
theorem zmodFourToZModTwo_identityBilinearModFour_of_allOdd {n : ℕ}
    {v u : Fin n → ZMod 4} (hodd : identityQuadraticAllOddModFour v) :
    zmodFourToZModTwo (identityBilinearModFour v u) = ∑ i, zmodFourToZModTwo (u i) := by
  rw [identityBilinearModFour]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  rcases hodd i with h | h
  · rw [h]
    rw [show zmodFourToZModTwo (1 : ZMod 4) = 1 by decide, one_mul]
  · rw [h]
    rw [show zmodFourToZModTwo (3 : ZMod 4) = 1 by decide, one_mul]

/-- The stabilizer condition fixes the first column as the first basis vector. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_firstColumn {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    (fun i : Fin (n + 1) => X.1.1 i 0) = identityQuadraticFirstBasisVectorModFour n := by
  exact congrArg Subtype.val X.2

/-- The fixed first column has top entry `1`. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_apply_zero_zero {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    X.1.1 (0 : Fin (n + 1)) 0 = 1 := by
  have h := congrFun (identityQuadraticIsometryModFourFirstColumnStabilizer_firstColumn X)
    (0 : Fin (n + 1))
  simpa [identityQuadraticFirstBasisVectorModFour] using h

/-- The fixed first column has zero tail. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_apply_succ_zero {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) (i : Fin n) :
    X.1.1 (Fin.succ i) 0 = 0 := by
  have h := congrFun (identityQuadraticIsometryModFourFirstColumnStabilizer_firstColumn X)
    (Fin.succ i)
  simpa [identityQuadraticFirstBasisVectorModFour] using h

/-- In a fixed-first-column stabilizer, every top-row tail entry is an even
class modulo `4`.  This is the first direct column-level constraint for the
remaining first-column fiber count. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_top_tail_even {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) (j : Fin n) :
    X.1.1 (0 : Fin (n + 1)) (Fin.succ j) = 0 ∨
      X.1.1 (0 : Fin (n + 1)) (Fin.succ j) = 2 := by
  have hne : (0 : Fin (n + 1)) ≠ Fin.succ j := by
    exact (Fin.succ_ne_zero j).symm
  have hbilin := identityQuadraticIsometryModFour_column_bilinear_ne X.1 hne
  have hfirst := identityQuadraticIsometryModFourFirstColumnStabilizer_firstColumn X
  have hbilin_eq :
      identityBilinearModFour (fun i : Fin (n + 1) => X.1.1 i 0)
          (fun i => X.1.1 i (Fin.succ j)) = X.1.1 (0 : Fin (n + 1)) (Fin.succ j) := by
    rw [hfirst]
    rw [identityBilinearModFour, Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [identityQuadraticFirstBasisVectorModFour]
    · intro b _ hb
      simp [identityQuadraticFirstBasisVectorModFour, Pi.single_eq_of_ne hb]
    · intro hzero
      simp at hzero
  rw [hbilin_eq] at hbilin
  exact zmodFour_eq_zero_or_two_of_two_mul_lift_eq_zero _ hbilin

/-- The diagonal modulo-`8` quadratic form splits over a leading coordinate. -/
theorem identityQuadraticModEight_cons {n : ℕ} (a : ZMod 4) (w : Fin n → ZMod 4) :
    identityQuadraticModEight (Fin.cons a w) =
      zmodFourLiftToZModEight a ^ 2 + identityQuadraticModEight w := by
  rw [identityQuadraticModEight, Fin.sum_univ_succ]
  rfl

/-- The top-row tail vector of a fixed-first-column stabilizer. -/
def identityQuadraticIsometryModFourFirstColumnStabilizer_topTail {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) : Fin n → ZMod 4 :=
  fun j => X.1.1 (0 : Fin (n + 1)) (Fin.succ j)

/-- The tail block matrix of a fixed-first-column stabilizer. -/
def identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    Matrix (Fin n) (Fin n) (ZMod 4) :=
  fun i j => X.1.1 (Fin.succ i) (Fin.succ j)

/-- Matrix multiplication by a fixed-first-column stabilizer in block form. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_mulVec_cons {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) (a : ZMod 4)
    (w : Fin n → ZMod 4) :
    X.1.1.mulVec (Fin.cons a w) =
      Fin.cons (a + identityBilinearModFour
          (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X) w)
        ((identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix X).mulVec w) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rw [identityQuadraticIsometryModFourFirstColumnStabilizer_apply_zero_zero X]
    simp [identityBilinearModFour,
      identityQuadraticIsometryModFourFirstColumnStabilizer_topTail]
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rw [identityQuadraticIsometryModFourFirstColumnStabilizer_apply_succ_zero X i]
    simp
    rw [Matrix.mulVec, dotProduct]
    rfl

/-- Explicit block preservation identity for a fixed-first-column stabilizer. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_block_preserves {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) (a : ZMod 4)
    (w : Fin n → ZMod 4) :
    zmodFourLiftToZModEight
          (a + identityBilinearModFour
            (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X) w) ^ 2 +
        identityQuadraticModEight
          ((identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix X).mulVec w) =
      zmodFourLiftToZModEight a ^ 2 + identityQuadraticModEight w := by
  have hpres := X.1.2 (Fin.cons a w)
  rw [identityQuadraticIsometryModFourFirstColumnStabilizer_mulVec_cons X a w] at hpres
  rw [identityQuadraticModEight_cons, identityQuadraticModEight_cons] at hpres
  exact hpres

/-- A scalar identity used to read off the top-row tail from the two leading
coordinate values in the fixed-first-column block preservation identity. -/
theorem zmodFour_eq_zero_of_lift_sq_block (a : ZMod 4) (q q' : ZMod 8)
    (h0 : zmodFourLiftToZModEight a ^ 2 + q' = q)
    (h1 : zmodFourLiftToZModEight (1 + a) ^ 2 + q' = 1 + q) :
    a = 0 := by
  fin_cases a
  · rfl
  · exfalso
    rw [← h0] at h1
    change ((2 : ZMod 8) ^ 2 + q' = 1 + ((1 : ZMod 8) ^ 2 + q')) at h1
    norm_num at h1
    rw [show (1 + (1 + q') : ZMod 8) = 2 + q' by ring] at h1
    have hc : (4 : ZMod 8) = 2 := by
      apply add_right_cancel (b := q')
      exact h1
    exact (by decide : ¬ ((4 : ZMod 8) = 2)) hc
  · exfalso
    rw [← h0] at h1
    change ((3 : ZMod 8) ^ 2 + q' = 1 + ((2 : ZMod 8) ^ 2 + q')) at h1
    norm_num at h1
    rw [show (1 + (4 + q') : ZMod 8) = 5 + q' by ring] at h1
    have hc : (1 : ZMod 8) = 5 := by
      apply add_right_cancel (b := q')
      exact h1
    exact (by decide : ¬ ((1 : ZMod 8) = 5)) hc
  · exfalso
    rw [← h0] at h1
    change ((0 : ZMod 8) ^ 2 + q' = 1 + ((3 : ZMod 8) ^ 2 + q')) at h1
    norm_num at h1
    rw [show (1 + (9 + q') : ZMod 8) = 2 + q' by
      rw [show (9 : ZMod 8) = 1 by decide]
      ring] at h1
    have hc : (0 : ZMod 8) = 2 := by
      apply add_right_cancel (b := q')
      simpa using h1
    exact (by decide : ¬ ((0 : ZMod 8) = 2)) hc

/-- The top-row tail of a fixed-first-column stabilizer pairs trivially with every
tail vector. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_topTail_bilinear_eq_zero
    {n : ℕ} (X : identityQuadraticIsometryModFourFirstColumnStabilizer n)
    (w : Fin n → ZMod 4) :
    identityBilinearModFour
        (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X) w = 0 := by
  let a := identityBilinearModFour
    (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X) w
  let q := identityQuadraticModEight w
  let q' := identityQuadraticModEight
    ((identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix X).mulVec w)
  have h0 : zmodFourLiftToZModEight a ^ 2 + q' = q := by
    have h := identityQuadraticIsometryModFourFirstColumnStabilizer_block_preserves X
      (0 : ZMod 4) w
    simpa [a, q, q', zmodFourLiftToZModEight] using h
  have h1 : zmodFourLiftToZModEight (1 + a) ^ 2 + q' = 1 + q := by
    have h := identityQuadraticIsometryModFourFirstColumnStabilizer_block_preserves X
      (1 : ZMod 4) w
    simpa [a, q, q'] using h
  exact zmodFour_eq_zero_of_lift_sq_block a q q' h0 h1

/-- The top-row tail of a fixed-first-column stabilizer is zero. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_topTail_eq_zero {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X = 0 := by
  funext j
  have h := identityQuadraticIsometryModFourFirstColumnStabilizer_topTail_bilinear_eq_zero X
    (Pi.single j (1 : ZMod 4))
  have hsum :
      identityBilinearModFour
          (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X)
          (Pi.single j (1 : ZMod 4)) =
        identityQuadraticIsometryModFourFirstColumnStabilizer_topTail X j := by
    rw [identityBilinearModFour, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      simp at hj
  rw [hsum] at h
  exact h

/-- The tail block of a fixed-first-column stabilizer preserves the Type I
identity quadratic form modulo `8`. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix_preserves
    {n : ℕ} (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    ∀ w : Fin n → ZMod 4,
      identityQuadraticModEight
          ((identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix X).mulVec w) =
        identityQuadraticModEight w := by
  intro w
  have h := identityQuadraticIsometryModFourFirstColumnStabilizer_block_preserves X
    (0 : ZMod 4) w
  rw [identityQuadraticIsometryModFourFirstColumnStabilizer_topTail_bilinear_eq_zero X w] at h
  simpa [zmodFourLiftToZModEight] using h

/-- The tail block of a fixed-first-column stabilizer is itself a Type I identity
quadratic isometry. -/
def identityQuadraticIsometryModFourFirstColumnStabilizerToTail {n : ℕ}
    (X : identityQuadraticIsometryModFourFirstColumnStabilizer n) :
    identityQuadraticIsometryModFour n :=
  ⟨identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix X,
    identityQuadraticIsometryModFourFirstColumnStabilizer_tailMatrix_preserves X⟩

/-- Block diagonal embedding `Y ↦ 1 ⊕ Y` for the fixed-first-column stabilizer. -/
def identityQuadraticIsometryModFourTailBlockMatrix {n : ℕ}
    (Y : identityQuadraticIsometryModFour n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4) :=
  fun i j =>
    Fin.cases (Fin.cases (1 : ZMod 4) (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => Y.1 i' j') j) i

/-- The block diagonal matrix acts on a leading-coordinate vector by preserving
the leading coordinate and applying the tail matrix to the tail. -/
theorem identityQuadraticIsometryModFourTailBlockMatrix_mulVec_cons {n : ℕ}
    (Y : identityQuadraticIsometryModFour n) (a : ZMod 4) (w : Fin n → ZMod 4) :
    (identityQuadraticIsometryModFourTailBlockMatrix Y).mulVec (Fin.cons a w) =
      Fin.cons a (Y.1.mulVec w) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    simp [identityQuadraticIsometryModFourTailBlockMatrix]
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    simp [identityQuadraticIsometryModFourTailBlockMatrix, Matrix.mulVec, dotProduct]

/-- The block diagonal embedding preserves the Type I identity quadratic form. -/
theorem identityQuadraticIsometryModFourTailBlockMatrix_preserves {n : ℕ}
    (Y : identityQuadraticIsometryModFour n) :
    ∀ v : Fin (n + 1) → ZMod 4,
      identityQuadraticModEight
          ((identityQuadraticIsometryModFourTailBlockMatrix Y).mulVec v) =
        identityQuadraticModEight v := by
  intro v
  rw [← Fin.cons_self_tail v]
  rw [identityQuadraticIsometryModFourTailBlockMatrix_mulVec_cons]
  rw [identityQuadraticModEight_cons, identityQuadraticModEight_cons, Y.2]

/-- The reverse block construction from a tail Type I identity quadratic
isometry to the fixed-first-column stabilizer. -/
def identityQuadraticIsometryModFourFirstColumnStabilizerOfTail {n : ℕ}
    (Y : identityQuadraticIsometryModFour n) :
    identityQuadraticIsometryModFourFirstColumnStabilizer n :=
  ⟨⟨identityQuadraticIsometryModFourTailBlockMatrix Y,
      identityQuadraticIsometryModFourTailBlockMatrix_preserves Y⟩, by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [identityQuadraticIsometryModFourFirstColumnMap,
        identityQuadraticFirstColumnUnitVector, identityQuadraticFirstBasisVectorModFour,
        identityQuadraticIsometryModFourTailBlockMatrix]
    · simp [identityQuadraticIsometryModFourFirstColumnMap,
        identityQuadraticFirstColumnUnitVector, identityQuadraticFirstBasisVectorModFour,
        identityQuadraticIsometryModFourTailBlockMatrix]⟩

/-- Fixed-first-column stabilizers are equivalent to tail Type I identity
quadratic isometries by the block-tail decomposition. -/
def identityQuadraticIsometryModFourFirstColumnStabilizerEquivTail (n : ℕ) :
    identityQuadraticIsometryModFourFirstColumnStabilizer n ≃
      identityQuadraticIsometryModFour n where
  toFun := identityQuadraticIsometryModFourFirstColumnStabilizerToTail
  invFun := identityQuadraticIsometryModFourFirstColumnStabilizerOfTail
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [identityQuadraticIsometryModFourTailBlockMatrix,
          identityQuadraticIsometryModFourFirstColumnStabilizerToTail,
          identityQuadraticIsometryModFourFirstColumnStabilizerOfTail,
          identityQuadraticIsometryModFourFirstColumnStabilizer_apply_zero_zero]
      · have h := congrFun
          (identityQuadraticIsometryModFourFirstColumnStabilizer_topTail_eq_zero X) j
        simpa [identityQuadraticIsometryModFourTailBlockMatrix,
          identityQuadraticIsometryModFourFirstColumnStabilizerToTail,
          identityQuadraticIsometryModFourFirstColumnStabilizerOfTail,
          identityQuadraticIsometryModFourFirstColumnStabilizer_topTail] using h.symm
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [identityQuadraticIsometryModFourTailBlockMatrix,
          identityQuadraticIsometryModFourFirstColumnStabilizerToTail,
          identityQuadraticIsometryModFourFirstColumnStabilizerOfTail,
          identityQuadraticIsometryModFourFirstColumnStabilizer_apply_succ_zero]
      · rfl
  right_inv Y := by
    apply Subtype.ext
    ext i j
    rfl

/-- Cardinality of the fixed-first-column stabilizer as the tail count. -/
theorem identityQuadraticIsometryModFourFirstColumnStabilizer_natCard_eq_tail (n : ℕ) :
    Nat.card (identityQuadraticIsometryModFourFirstColumnStabilizer n) =
      Nat.card (identityQuadraticIsometryModFour n) := by
  exact Nat.card_congr (identityQuadraticIsometryModFourFirstColumnStabilizerEquivTail n)

/-- The fiber over the fixed first basis vector is the first-column stabilizer. -/
def identityQuadraticIsometryModFour_firstColumnFiberEquivStabilizer (n : ℕ) :
    {X : identityQuadraticIsometryModFour (n + 1) //
      identityQuadraticIsometryModFourFirstColumnMap n X =
        ⟨identityQuadraticFirstBasisVectorModFour n,
          identityQuadraticFirstBasisVectorModFour_mem_unitVectors n⟩} ≃
      identityQuadraticIsometryModFourFirstColumnStabilizer n where
  toFun X := X
  invFun X := X
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cardinality form of the fixed first-column fiber/stabilizer equivalence. -/
theorem identityQuadraticIsometryModFour_firstColumnFiber_natCard_eq_stabilizer (n : ℕ) :
    Nat.card {X : identityQuadraticIsometryModFour (n + 1) //
      identityQuadraticIsometryModFourFirstColumnMap n X =
        ⟨identityQuadraticFirstBasisVectorModFour n,
          identityQuadraticFirstBasisVectorModFour_mem_unitVectors n⟩} =
      Nat.card (identityQuadraticIsometryModFourFirstColumnStabilizer n) := by
  exact Nat.card_congr (identityQuadraticIsometryModFour_firstColumnFiberEquivStabilizer n)

/-- Cardinality of the fixed first-column fiber as the tail count. -/
theorem identityQuadraticIsometryModFour_firstColumnFiber_natCard_eq_tail (n : ℕ) :
    Nat.card {X : identityQuadraticIsometryModFour (n + 1) //
      identityQuadraticIsometryModFourFirstColumnMap n X =
        ⟨identityQuadraticFirstBasisVectorModFour n,
          identityQuadraticFirstBasisVectorModFour_mem_unitVectors n⟩} =
      Nat.card (identityQuadraticIsometryModFour n) := by
  rw [identityQuadraticIsometryModFour_firstColumnFiber_natCard_eq_stabilizer,
    identityQuadraticIsometryModFourFirstColumnStabilizer_natCard_eq_tail]

/-- A characteristic all-odd first column has empty fiber in dimensions at least
`2`.  This is the first interface for the corrected Type I
recurrence: characteristic norm-one columns are not transported to the fixed
first column. -/
theorem identityQuadraticIsometryModFourFirstColumnFiber_isEmpty_of_allOdd {n : ℕ}
    (hn : 1 ≤ n) (v : identityQuadraticUnitVectorsModFour (n + 1))
    (hodd : identityQuadraticAllOddModFour v.1) :
    IsEmpty (identityQuadraticIsometryModFourFirstColumnFiber n v) := by
  refine ⟨?_⟩
  intro X
  let k : Fin (n + 1) := ⟨1, by omega⟩
  let u : Fin (n + 1) → ZMod 4 := fun i => X.1.1 i k
  have hk_ne : (0 : Fin (n + 1)) ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    simp [k] at hval
  have hcross := identityQuadraticIsometryModFour_column_bilinear_ne X.1 hk_ne
  have hcol0 : (fun i : Fin (n + 1) => X.1.1 i 0) = v.1 := by
    exact congrArg Subtype.val X.2
  change (2 : ZMod 8) * zmodFourLiftToZModEight
        (identityBilinearModFour (fun i : Fin (n + 1) => X.1.1 i 0) u) = 0 at hcross
  rw [hcol0] at hcross
  have hdot0 : zmodFourToZModTwo (identityBilinearModFour v.1 u) = 0 :=
    zmodFourToZModTwo_eq_zero_of_two_mul_lift_eq_zero _ hcross
  have hnorm := identityQuadraticIsometryModFour_column_norm X.1 k
  change identityQuadraticModEight u = 1 at hnorm
  have hsum1 : (∑ i, zmodFourToZModTwo (u i)) = 1 := by
    have hcast := congrArg zmodEightToZModTwo hnorm
    rw [zmodEightToZModTwo_identityQuadraticModEight] at hcast
    simpa [zmodEightToZModTwo] using hcast
  have hsum0 : (∑ i, zmodFourToZModTwo (u i)) = 0 := by
    rw [← zmodFourToZModTwo_identityBilinearModFour_of_allOdd (v := v.1) (u := u) hodd]
    exact hdot0
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  exact h01 (hsum0.symm.trans hsum1)

/-- Cardinality form of characteristic-fiber emptiness. -/
theorem identityQuadraticIsometryModFourFirstColumnFiber_natCard_eq_zero_of_allOdd {n : ℕ}
    (hn : 1 ≤ n) (v : identityQuadraticUnitVectorsModFour (n + 1))
    (hodd : identityQuadraticAllOddModFour v.1) :
    Nat.card (identityQuadraticIsometryModFourFirstColumnFiber n v) = 0 := by
  haveI := identityQuadraticIsometryModFourFirstColumnFiber_isEmpty_of_allOdd hn v hodd
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- The ordinary norm-one first-column target: norm-one columns with at least
one even coordinate.  Characteristic all-odd columns are handled separately by
the empty-fiber theorem. -/
abbrev identityQuadraticOrdinaryUnitVectorsModFour (n : ℕ) : Type :=
  {v : identityQuadraticUnitVectorsModFour n // identityQuadraticHasEvenCoordinateModFour v.1}

noncomputable instance (n : ℕ) : Fintype (identityQuadraticOrdinaryUnitVectorsModFour n) := by
  classical
  unfold identityQuadraticOrdinaryUnitVectorsModFour
  infer_instance

noncomputable instance (n : ℕ) :
    Fintype {v : identityQuadraticUnitVectorsModFour n //
      ¬ identityQuadraticAllOddModFour v.1} := by
  classical
  infer_instance

/-- Ordinary norm-one targets are the complement of the characteristic all-odd
targets inside the norm-one shell. -/
def identityQuadraticOrdinaryUnitVectorsModFourEquivNotAllOdd (n : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFour n ≃
      {v : identityQuadraticUnitVectorsModFour n // ¬ identityQuadraticAllOddModFour v.1} where
  toFun v := ⟨v.1, (identityQuadraticHasEvenCoordinateModFour_iff_not_allOdd v.1.1).mp v.2⟩
  invFun v := ⟨v.1, (identityQuadraticHasEvenCoordinateModFour_iff_not_allOdd v.1.1).mpr v.2⟩
  left_inv v := by
    ext
    rfl
  right_inv v := by
    ext
    rfl

/-- Ordinary norm-one targets are counted by subtracting the characteristic
all-odd norm-one targets from the whole norm-one shell. -/
theorem identityQuadraticOrdinaryUnitVectorsModFour_natCard_eq_unitVectors_sub_characteristic
    (n : ℕ) :
    Nat.card (identityQuadraticOrdinaryUnitVectorsModFour n) =
      Nat.card (identityQuadraticUnitVectorsModFour n) -
        Nat.card (identityQuadraticCharacteristicUnitVectorsModFour n) := by
  calc
    Nat.card (identityQuadraticOrdinaryUnitVectorsModFour n) =
        Nat.card {v : identityQuadraticUnitVectorsModFour n //
          ¬ identityQuadraticAllOddModFour v.1} := by
      exact Nat.card_congr (identityQuadraticOrdinaryUnitVectorsModFourEquivNotAllOdd n)
    _ = Fintype.card {v : identityQuadraticUnitVectorsModFour n //
          ¬ identityQuadraticAllOddModFour v.1} := by
      exact Nat.card_eq_fintype_card
    _ = Fintype.card (identityQuadraticUnitVectorsModFour n) -
          Fintype.card (identityQuadraticCharacteristicUnitVectorsModFour n) := by
      exact Fintype.card_subtype_compl
        (fun v : identityQuadraticUnitVectorsModFour n =>
          identityQuadraticAllOddModFour v.1)
    _ = Nat.card (identityQuadraticUnitVectorsModFour n) -
          Nat.card (identityQuadraticCharacteristicUnitVectorsModFour n) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- Closed ordinary norm-one target count in terms of the total norm-one shell
and the explicit characteristic all-odd contribution. -/
theorem identityQuadraticOrdinaryUnitVectorsModFour_natCard (n : ℕ) :
    Nat.card (identityQuadraticOrdinaryUnitVectorsModFour n) =
      Nat.card (identityQuadraticUnitVectorsModFour n) -
        if (n : ZMod 8) = 1 then 2 ^ n else 0 := by
  rw [identityQuadraticOrdinaryUnitVectorsModFour_natCard_eq_unitVectors_sub_characteristic,
    identityQuadraticCharacteristicUnitVectorsModFour_natCard]

/-- A chosen even coordinate of an ordinary norm-one vector in positive rank. -/
noncomputable def identityQuadraticOrdinaryUnitVectorsModFour_evenIndex {n : ℕ}
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) : Fin (n + 1) :=
  Classical.choose v.2

/-- The chosen coordinate of an ordinary norm-one vector is even. -/
theorem identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec {n : ℕ}
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    v.1.1 (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v) = 0 ∨
      v.1.1 (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v) = 2 :=
  Classical.choose_spec v.2

/-- The composed transporter from the fixed first basis vector to any ordinary
norm-one column: first swap the fixed coordinate into an even coordinate of the
target, then apply the ordinary reflection. -/
noncomputable def identityQuadraticOrdinaryColumnTransportIsometry (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFour (n + 1) :=
  identityQuadraticIsometryModFour_comp
    (identityQuadraticOrdinaryReflectionIsometry v.1
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v)
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec v))
    (identityQuadraticSwapFirstToCoordinateIsometry n
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v))

/-- The composed ordinary-column transporter sends the fixed first basis vector
to the prescribed ordinary norm-one column. -/
theorem identityQuadraticOrdinaryColumnTransportIsometry_mulVec_first (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    (identityQuadraticOrdinaryColumnTransportIsometry n v).1.mulVec
        (identityQuadraticFirstBasisVectorModFour n) = v.1.1 := by
  rw [identityQuadraticOrdinaryColumnTransportIsometry,
    identityQuadraticIsometryModFour_comp]
  rw [← Matrix.mulVec_mulVec]
  rw [identityQuadraticSwapFirstToCoordinateIsometry_mulVec_first]
  exact identityQuadraticOrdinaryReflectionIsometry_mulVec_basis v.1
    (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v)
    (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec v)

/-- The inverse-ordered ordinary-column transporter: first reflect the target
column back to the chosen coordinate basis vector, then swap that coordinate
back to the fixed first coordinate. -/
noncomputable def identityQuadraticOrdinaryColumnTransportInverseIsometry (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFour (n + 1) :=
  identityQuadraticIsometryModFour_comp
    (identityQuadraticSwapFirstToCoordinateIsometry n
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v))
    (identityQuadraticOrdinaryReflectionIsometry v.1
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v)
      (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec v))

/-- The inverse-ordered transporter sends the ordinary target column back to
the fixed first basis vector. -/
theorem identityQuadraticOrdinaryColumnTransportInverseIsometry_mulVec_target (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    (identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1.mulVec v.1.1 =
      identityQuadraticFirstBasisVectorModFour n := by
  rw [identityQuadraticOrdinaryColumnTransportInverseIsometry,
    identityQuadraticIsometryModFour_comp]
  rw [← Matrix.mulVec_mulVec]
  rw [identityQuadraticOrdinaryReflectionIsometry_mulVec_target]
  exact identityQuadraticSwapFirstToCoordinateIsometry_mulVec_coordinate n
    (identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v)

/-- The inverse-ordered transporter cancels the ordinary-column transporter on
vectors. -/
theorem identityQuadraticOrdinaryColumnTransportInverseIsometry_mulVec_mulVec (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1))
    (x : Fin (n + 1) → ZMod 4) :
    (identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1.mulVec
        ((identityQuadraticOrdinaryColumnTransportIsometry n v).1.mulVec x) = x := by
  let j := identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v
  let hven := identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec v
  let S := identityQuadraticSwapFirstToCoordinateIsometry n j
  let R := identityQuadraticOrdinaryReflectionIsometry v.1 j hven
  have hS : S.1.mulVec (S.1.mulVec x) = x := by
    simpa [S, j] using identityQuadraticSwapFirstToCoordinateIsometry_mulVec_mulVec n j x
  have hR : R.1.mulVec (R.1.mulVec (S.1.mulVec x)) = S.1.mulVec x := by
    simpa [R, j, hven] using
      identityQuadraticOrdinaryReflectionIsometry_mulVec_mulVec v.1 j hven (S.1.mulVec x)
  rw [identityQuadraticOrdinaryColumnTransportInverseIsometry,
    identityQuadraticOrdinaryColumnTransportIsometry, identityQuadraticIsometryModFour_comp,
    identityQuadraticIsometryModFour_comp]
  change (S.1 * R.1).mulVec ((R.1 * S.1).mulVec x) = x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hR, hS]

/-- The ordinary-column transporter cancels the inverse-ordered transporter on
vectors. -/
theorem identityQuadraticOrdinaryColumnTransportIsometry_mulVec_mulVec_inverse (n : ℕ)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1))
    (x : Fin (n + 1) → ZMod 4) :
    (identityQuadraticOrdinaryColumnTransportIsometry n v).1.mulVec
        ((identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1.mulVec x) = x := by
  let j := identityQuadraticOrdinaryUnitVectorsModFour_evenIndex v
  let hven := identityQuadraticOrdinaryUnitVectorsModFour_evenIndex_spec v
  let S := identityQuadraticSwapFirstToCoordinateIsometry n j
  let R := identityQuadraticOrdinaryReflectionIsometry v.1 j hven
  have hR : R.1.mulVec (R.1.mulVec x) = x := by
    simpa [R, j, hven] using
      identityQuadraticOrdinaryReflectionIsometry_mulVec_mulVec v.1 j hven x
  have hS : S.1.mulVec (S.1.mulVec (R.1.mulVec x)) = R.1.mulVec x := by
    simpa [S, j] using
      identityQuadraticSwapFirstToCoordinateIsometry_mulVec_mulVec n j (R.1.mulVec x)
  rw [identityQuadraticOrdinaryColumnTransportInverseIsometry,
    identityQuadraticOrdinaryColumnTransportIsometry, identityQuadraticIsometryModFour_comp,
    identityQuadraticIsometryModFour_comp]
  change (R.1 * S.1).mulVec ((S.1 * R.1).mulVec x) = x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hS, hR]

/-- Matrix form of cancellation of the inverse-ordered transporter against the
ordinary-column transporter. -/
theorem identityQuadraticOrdinaryColumnTransportInverseIsometry_mul_transport_matrix
    (n : ℕ) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4)) :
    (identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1 *
        ((identityQuadraticOrdinaryColumnTransportIsometry n v).1 * M) = M := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact identityQuadraticOrdinaryColumnTransportInverseIsometry_mulVec_mulVec n v (M.mulVec x)

/-- Matrix form of cancellation of the ordinary-column transporter against the
inverse-ordered transporter. -/
theorem identityQuadraticOrdinaryColumnTransportIsometry_mul_inverse_matrix
    (n : ℕ) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4)) :
    (identityQuadraticOrdinaryColumnTransportIsometry n v).1 *
        ((identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1 * M) = M := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact identityQuadraticOrdinaryColumnTransportIsometry_mulVec_mulVec_inverse n v (M.mulVec x)

/-- In dimensions at least two, the first column of a Type I identity quadratic
isometry is automatically ordinary: a characteristic all-odd first column would
have empty fiber, but the isometry itself lies in that fiber. -/
def identityQuadraticIsometryModFourFirstOrdinaryColumnMap (n : ℕ) (hn : 1 ≤ n) :
    identityQuadraticIsometryModFour (n + 1) →
      identityQuadraticOrdinaryUnitVectorsModFour (n + 1) :=
  fun X =>
    let v := identityQuadraticIsometryModFourFirstColumnMap n X
    ⟨v, by
      rw [identityQuadraticHasEvenCoordinateModFour_iff_not_allOdd]
      intro hodd
      haveI := identityQuadraticIsometryModFourFirstColumnFiber_isEmpty_of_allOdd hn v hodd
      exact isEmptyElim (⟨X, rfl⟩ : identityQuadraticIsometryModFourFirstColumnFiber n v)⟩

/-- The fiber of the corrected first-column projection over an ordinary
norm-one column. -/
abbrev identityQuadraticIsometryModFourFirstOrdinaryColumnFiber (n : ℕ) (hn : 1 ≤ n)
    (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) : Type :=
  {X : identityQuadraticIsometryModFour (n + 1) //
    identityQuadraticIsometryModFourFirstOrdinaryColumnMap n hn X = v}

/-- Left multiplication by the ordinary-column transporter sends the fixed
first-column stabilizer into the ordinary first-column fiber over the target
column.  This is the forward half of the ordinary-fiber uniformity bijection. -/
noncomputable def identityQuadraticIsometryModFourFirstOrdinaryColumnFiberTransportFromFixed
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFourFirstColumnStabilizer n →
      identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v :=
  fun X =>
    ⟨identityQuadraticIsometryModFour_comp
      (identityQuadraticOrdinaryColumnTransportIsometry n v) X.1, by
      have hcolX :
          X.1.1.mulVec (identityQuadraticFirstBasisVectorModFour n) =
            identityQuadraticFirstBasisVectorModFour n := by
        rw [matrix_mulVec_identityQuadraticFirstBasisVectorModFour]
        exact identityQuadraticIsometryModFourFirstColumnStabilizer_firstColumn X
      have hfirst :
          (fun i : Fin (n + 1) =>
              ((identityQuadraticOrdinaryColumnTransportIsometry n v).1 * X.1.1) i 0) =
            v.1.1 := by
        rw [← matrix_mulVec_identityQuadraticFirstBasisVectorModFour]
        calc
          ((identityQuadraticOrdinaryColumnTransportIsometry n v).1 * X.1.1).mulVec
              (identityQuadraticFirstBasisVectorModFour n) =
              (identityQuadraticOrdinaryColumnTransportIsometry n v).1.mulVec
                (X.1.1.mulVec (identityQuadraticFirstBasisVectorModFour n)) := by
            rw [Matrix.mulVec_mulVec]
          _ = (identityQuadraticOrdinaryColumnTransportIsometry n v).1.mulVec
              (identityQuadraticFirstBasisVectorModFour n) := by
            rw [hcolX]
          _ = v.1.1 := identityQuadraticOrdinaryColumnTransportIsometry_mulVec_first n v
      apply Subtype.ext
      apply Subtype.ext
      exact hfirst⟩

/-- Left multiplication by the inverse-ordered transporter sends the ordinary
first-column fiber back into the fixed first-column stabilizer.  Together with
`identityQuadraticIsometryModFourFirstOrdinaryColumnFiberTransportFromFixed`,
this supplies the two explicit maps needed for the ordinary-fiber equivalence. -/
noncomputable def identityQuadraticIsometryModFourFirstOrdinaryColumnFiberTransportToFixed
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v →
      identityQuadraticIsometryModFourFirstColumnStabilizer n :=
  fun X =>
    ⟨identityQuadraticIsometryModFour_comp
      (identityQuadraticOrdinaryColumnTransportInverseIsometry n v) X.1, by
      have hcolX :
          X.1.1.mulVec (identityQuadraticFirstBasisVectorModFour n) = v.1.1 := by
        rw [matrix_mulVec_identityQuadraticFirstBasisVectorModFour]
        have h := congrArg Subtype.val (congrArg Subtype.val X.2)
        exact h
      have hfirst :
          (fun i : Fin (n + 1) =>
              ((identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1 * X.1.1) i 0) =
            identityQuadraticFirstBasisVectorModFour n := by
        rw [← matrix_mulVec_identityQuadraticFirstBasisVectorModFour]
        calc
          ((identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1 * X.1.1).mulVec
              (identityQuadraticFirstBasisVectorModFour n) =
              (identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1.mulVec
                (X.1.1.mulVec (identityQuadraticFirstBasisVectorModFour n)) := by
            rw [Matrix.mulVec_mulVec]
          _ = (identityQuadraticOrdinaryColumnTransportInverseIsometry n v).1.mulVec v.1.1 := by
            rw [hcolX]
          _ = identityQuadraticFirstBasisVectorModFour n :=
            identityQuadraticOrdinaryColumnTransportInverseIsometry_mulVec_target n v
      apply Subtype.ext
      exact hfirst⟩

/-- Ordinary first-column fibers are equivalent to the fixed first-column
stabilizer by left multiplication with the ordinary-column transporter and its
inverse-ordered companion. -/
noncomputable def identityQuadraticIsometryModFourFirstOrdinaryColumnFiberEquivStabilizer
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v ≃
      identityQuadraticIsometryModFourFirstColumnStabilizer n where
  toFun := identityQuadraticIsometryModFourFirstOrdinaryColumnFiberTransportToFixed n hn v
  invFun := identityQuadraticIsometryModFourFirstOrdinaryColumnFiberTransportFromFixed n hn v
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact identityQuadraticOrdinaryColumnTransportIsometry_mul_inverse_matrix n v X.1.1
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact identityQuadraticOrdinaryColumnTransportInverseIsometry_mul_transport_matrix n v X.1.1

/-- Forgetting the ordinary-column proof identifies corrected first-column
fibers with the original first-column fibers. -/
def identityQuadraticIsometryModFourFirstOrdinaryColumnFiberEquivFirstColumnFiber
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v ≃
      identityQuadraticIsometryModFourFirstColumnFiber n v.1 where
  toFun X := ⟨X.1, by
    have h := congrArg Subtype.val X.2
    exact h⟩
  invFun X := ⟨X.1, by
    ext i
    exact congrFun (congrArg Subtype.val X.2) i⟩
  left_inv X := by
    ext
    rfl
  right_inv X := by
    ext
    rfl

/-- Cardinality form of the corrected ordinary-fiber/original-fiber
identification. -/
theorem identityQuadraticIsometryModFourFirstOrdinaryColumnFiber_natCard_eq_firstColumnFiber
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    Nat.card (identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v) =
      Nat.card (identityQuadraticIsometryModFourFirstColumnFiber n v.1) := by
  exact Nat.card_congr
    (identityQuadraticIsometryModFourFirstOrdinaryColumnFiberEquivFirstColumnFiber n hn v)

/-- Every ordinary first-column fiber has the fixed stabilizer/tail cardinality.
This is the orbit-stabilizer uniformity input for the corrected Type I
first-column recurrence. -/
theorem identityQuadraticIsometryModFourFirstOrdinaryColumnFiber_natCard_eq_tail
    (n : ℕ) (hn : 1 ≤ n) (v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) :
    Nat.card (identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v) =
      Nat.card (identityQuadraticIsometryModFour n) := by
  rw [Nat.card_congr
    (identityQuadraticIsometryModFourFirstOrdinaryColumnFiberEquivStabilizer n hn v)]
  exact identityQuadraticIsometryModFourFirstColumnStabilizer_natCard_eq_tail n

/-- Corrected first-column recurrence: it is enough to prove uniform fibers over
ordinary norm-one columns.  Characteristic all-odd columns have already been
removed from the codomain by the empty-fiber theorem. -/
theorem identityQuadraticIsometryModFour_natCard_eq_ordinaryUnitVectors_mul_tail_of_firstOrdinaryColumn_uniform
    (n : ℕ) (hn : 1 ≤ n)
    (huniform : ∀ v : identityQuadraticOrdinaryUnitVectorsModFour (n + 1),
      Nat.card (identityQuadraticIsometryModFourFirstOrdinaryColumnFiber n hn v) =
        Nat.card (identityQuadraticIsometryModFour n)) :
    Nat.card (identityQuadraticIsometryModFour (n + 1)) =
      Nat.card (identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) *
        Nat.card (identityQuadraticIsometryModFour n) := by
  exact nat_card_eq_mul_of_fiber_card
    (identityQuadraticIsometryModFourFirstOrdinaryColumnMap n hn)
    (Nat.card (identityQuadraticIsometryModFour n)) huniform

/-- Corrected Type I first-column recurrence over ordinary columns.  The
characteristic all-odd columns have empty fibers, while ordinary columns are all
transported to the fixed first-column stabilizer. -/
theorem identityQuadraticIsometryModFour_natCard_eq_ordinaryUnitVectors_mul_tail
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (identityQuadraticIsometryModFour (n + 1)) =
      Nat.card (identityQuadraticOrdinaryUnitVectorsModFour (n + 1)) *
        Nat.card (identityQuadraticIsometryModFour n) := by
  apply identityQuadraticIsometryModFour_natCard_eq_ordinaryUnitVectors_mul_tail_of_firstOrdinaryColumn_uniform
  intro v
  exact identityQuadraticIsometryModFourFirstOrdinaryColumnFiber_natCard_eq_tail n hn v

/-- Corrected Type I first-column recurrence with the ordinary-column count
rewritten as the total norm-one shell count minus the characteristic all-odd
contribution. -/
theorem identityQuadraticIsometryModFour_natCard_eq_unitVectors_sub_characteristic_mul_tail
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (identityQuadraticIsometryModFour (n + 1)) =
      (Nat.card (identityQuadraticUnitVectorsModFour (n + 1)) -
          if ((n + 1 : ℕ) : ZMod 8) = 1 then 2 ^ (n + 1) else 0) *
        Nat.card (identityQuadraticIsometryModFour n) := by
  rw [identityQuadraticIsometryModFour_natCard_eq_ordinaryUnitVectors_mul_tail n hn,
    identityQuadraticOrdinaryUnitVectorsModFour_natCard]

/-- Recursive finite formula for the Type I ordinary norm-one first columns:
the total norm-one shell count minus the explicit characteristic all-odd
contribution. -/
def identityQuadraticOrdinaryUnitVectorsModFourCount (n : ℕ) : ℕ :=
  identityQuadraticShellModEightCount n 1 - if (n : ZMod 8) = 1 then 2 ^ n else 0

/-- The recursive ordinary-column formula computes the actual ordinary norm-one
first-column cardinality. -/
theorem identityQuadraticOrdinaryUnitVectorsModFour_natCard_eq_count (n : ℕ) :
    Nat.card (identityQuadraticOrdinaryUnitVectorsModFour n) =
      identityQuadraticOrdinaryUnitVectorsModFourCount n := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCount,
    identityQuadraticOrdinaryUnitVectorsModFour_natCard,
    identityQuadraticUnitVectorsModFour_natCard_eq_shellCount]

/-- Recursive finite formula for the diagonal Type I quadratic-isometry counts.
The zero- and one-dimensional targets are seeds; from dimension two onward the
corrected ordinary-column recurrence supplies the next factor. -/
def identityQuadraticIsometryModFourCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 =>
      identityQuadraticOrdinaryUnitVectorsModFourCount (n + 2) *
        identityQuadraticIsometryModFourCount (n + 1)

/-- The recursive finite formula computes the actual diagonal Type I
quadratic-isometry cardinality in every rank. -/
theorem identityQuadraticIsometryModFour_natCard_eq_count (n : ℕ) :
    Nat.card (identityQuadraticIsometryModFour n) =
      identityQuadraticIsometryModFourCount n := by
  induction n with
  | zero =>
      rw [identityQuadraticIsometryModFour_natCard_zero]
      rfl
  | succ n ih =>
      cases n with
      | zero =>
          rw [identityQuadraticIsometryModFour_natCard_one]
          rfl
      | succ n =>
          rw [identityQuadraticIsometryModFour_natCard_eq_ordinaryUnitVectors_mul_tail (n + 1)
            (by omega)]
          rw [identityQuadraticOrdinaryUnitVectorsModFour_natCard_eq_count, ih]
          rfl

/-- The first rank beyond the signed-permutation range follows from the
ordinary-column recurrence, without the unrestricted-uniformity hypothesis,
which is false. -/
theorem identityQuadraticIsometryModFour_natCard_three :
    Nat.card (identityQuadraticIsometryModFour 3) = 96 := by
  rw [identityQuadraticIsometryModFour_natCard_eq_count]
  decide

/-- If every norm-one first-column fiber has the same cardinality as the fixed
first-column fiber, then the Type I identity finite target satisfies the direct
orbit-stabilizer recurrence with the already-computed fixed tail count. -/
theorem identityQuadraticIsometryModFour_natCard_eq_unitVectors_mul_tail_of_firstColumn_uniform
    (n : ℕ)
    (huniform : ∀ v : identityQuadraticUnitVectorsModFour (n + 1),
      Nat.card (identityQuadraticIsometryModFourFirstColumnFiber n v) =
        Nat.card (identityQuadraticIsometryModFourFirstColumnFiber n
          (identityQuadraticFirstColumnUnitVector n))) :
    Nat.card (identityQuadraticIsometryModFour (n + 1)) =
      Nat.card (identityQuadraticUnitVectorsModFour (n + 1)) *
        Nat.card (identityQuadraticIsometryModFour n) := by
  apply identityQuadraticIsometryModFour_natCard_eq_unitVectors_mul_of_firstColumn_fiber_card
  intro v
  rw [huniform v]
  exact identityQuadraticIsometryModFour_firstColumnFiber_natCard_eq_tail n

/-- In the first nontrivial orbit-stabilizer case, every norm-one first-column
fiber has the same cardinality as the fixed first-column fiber. -/
theorem identityQuadraticIsometryModFour_firstColumnFiber_natCard_uniform_one
    (v : identityQuadraticUnitVectorsModFour 2) :
    Nat.card (identityQuadraticIsometryModFourFirstColumnFiber 1 v) =
      Nat.card (identityQuadraticIsometryModFourFirstColumnFiber 1
        (identityQuadraticFirstColumnUnitVector 1)) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  fin_cases v
  all_goals decide

/-- The two-dimensional Type I identity finite target satisfies the first-column
orbit-stabilizer recurrence. -/
theorem identityQuadraticIsometryModFour_natCard_two_eq_unitVectors_mul_tail :
    Nat.card (identityQuadraticIsometryModFour 2) =
      Nat.card (identityQuadraticUnitVectorsModFour 2) *
        Nat.card (identityQuadraticIsometryModFour 1) := by
  exact identityQuadraticIsometryModFour_natCard_eq_unitVectors_mul_tail_of_firstColumn_uniform
    1 identityQuadraticIsometryModFour_firstColumnFiber_natCard_uniform_one

/-- In dimension three, the first-column recurrence reduces the Type I identity
finite target to the still-open uniformity of first-column fibers. -/
theorem identityQuadraticIsometryModFour_natCard_three_eq_of_firstColumn_uniform
    (huniform : ∀ v : identityQuadraticUnitVectorsModFour 3,
      Nat.card (identityQuadraticIsometryModFourFirstColumnFiber 2 v) =
        Nat.card (identityQuadraticIsometryModFourFirstColumnFiber 2
          (identityQuadraticFirstColumnUnitVector 2))) :
    Nat.card (identityQuadraticIsometryModFour 3) = 96 := by
  rw [identityQuadraticIsometryModFour_natCard_eq_unitVectors_mul_tail_of_firstColumn_uniform 2
    huniform]
  rw [identityQuadraticUnitVectorsModFour_natCard_three, identityQuadraticIsometryModFour_natCard_two]

/-- The quotient-family form of the depth-three coordinate solution target for `Iₙ`. -/
abbrev identityLatticeDepthThreeCoordinateSolutionFamily (n : ℕ) :=
  {Y : Fin n → localDualQuotientTarget
      (primePowCoordinateSubmodule (n := n) 2 2) //
    Y ∈ localDualQuotientSolutionFamilies (identityLattice n) 2 3
      (primePowCoordinateSubmodule (n := n) 2 2)
      (primePowCoordinateSubmodule_rank (n := n) 2 2)}

/-- The matrix form of the depth-three coordinate solution target for `Iₙ`. -/
abbrev identityLatticeDepthThreeCoordinateSolutionMatrix (n : ℕ) :=
  {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus 2 2 : ℕ)) //
    localDualQuotientLiftFamily (n := n) 2 2 X ∈
      localDualQuotientSolutionFamilies (identityLattice n) 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2)}

instance (n : ℕ) : Fintype (identityLatticeDepthThreeCoordinateSolutionMatrix n) := by
  classical
  unfold identityLatticeDepthThreeCoordinateSolutionMatrix
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A depth-three coordinate solution for the diagonal Type I seed preserves the
mod-`8` diagonal quadratic form on `ZMod 4` coordinates. -/
theorem identityLatticeDepthThreeCoordinateSolutionMatrix_to_quadraticIsometryModFour_mem
    {n : ℕ} (X : identityLatticeDepthThreeCoordinateSolutionMatrix n) :
    ∀ v : Fin n → ZMod 4,
      identityQuadraticModEight (X.1.mulVec v) = identityQuadraticModEight v := by
  intro v
  let x : Fin n → ℤ := fun i => (v i).val
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) 2 2
  let Y : Fin n → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := n) 2 2 X.1
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let y : Fin n → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ y := by
    change q = D.mkQ y
    exact (Submodule.Quotient.mk_out q).symm
  have hquad :
      ((identityLattice n).quadForm y : ZMod (primePowModulus 2 3 : ℕ)) =
        ((identityLattice n).quadForm x : ZMod (primePowModulus 2 3 : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp X.2) x y hq
  have hxv : (fun i : Fin n => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hvec :
      (fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
        X.1.mulVec v := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := n) 2 2 Y x
    have hqcoord :
        primePowQuotientVector (n := n) 2 2
            (quotientBasisFamilyMap D Y x) =
          fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ)) := by
      rw [hq]
      exact primePowQuotientVector_mkQ (n := n) 2 2 y
    have hm : localDualQuotientFamilyMatrix (n := n) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
    calc
      (fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
          (localDualQuotientFamilyMatrix (n := n) 2 2 Y).mulVec
            (fun j : Fin n => (x j : ZMod (primePowModulus 2 2 : ℕ))) := by
            exact (hmat.trans hqcoord).symm
      _ = X.1.mulVec v := by
            rw [hm]
            change X.1.mulVec (fun j : Fin n => (x j : ZMod 4)) = X.1.mulVec v
            rw [hxv]
  have hsum :
      ((∑ i, y i ^ 2 : ℤ) : ZMod 8) = ((∑ i, x i ^ 2 : ℤ) : ZMod 8) := by
    simpa [primePowModulus, identityLattice_quadForm_eq_sum_sq] using hquad
  calc
    identityQuadraticModEight (X.1.mulVec v)
        = identityQuadraticModEight (fun i : Fin n => (y i : ZMod 4)) := by
            rw [← hvec]
    _ = ((∑ i, y i ^ 2 : ℤ) : ZMod 8) := identityQuadraticModEight_intCast y
    _ = ((∑ i, x i ^ 2 : ℤ) : ZMod 8) := hsum
    _ = identityQuadraticModEight (fun i : Fin n => (x i : ZMod 4)) :=
            (identityQuadraticModEight_intCast x).symm
    _ = identityQuadraticModEight v := by rw [hxv]

/-- The depth-three Type I identity-lattice matrix target maps into the
mod-`4` quadratic-isometry target. -/
def identityLatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour
    {n : ℕ} (X : identityLatticeDepthThreeCoordinateSolutionMatrix n) :
    identityQuadraticIsometryModFour n :=
  ⟨X.1, identityLatticeDepthThreeCoordinateSolutionMatrix_to_quadraticIsometryModFour_mem X⟩

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, a matrix preserving the diagonal Type I quadratic form modulo
`8` is a depth-three coordinate solution for the diagonal identity lattice. -/
theorem identityQuadraticIsometryModFour_to_depthThreeCoordinateSolutionMatrix_mem
    {n : ℕ} (X : identityQuadraticIsometryModFour n) :
    localDualQuotientLiftFamily (n := n) 2 2 X.1 ∈
      localDualQuotientSolutionFamilies (identityLattice n) 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) 2 2
  let Y : Fin n → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := n) 2 2 X.1
  have hvec :
      (fun i : Fin n => (y i : ZMod 4)) =
        X.1.mulVec (fun j : Fin n => (x j : ZMod 4)) := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := n) 2 2 Y x
    have hq := congrArg (primePowQuotientVector (n := n) 2 2) hxy
    have hm : localDualQuotientFamilyMatrix (n := n) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
    calc
      (fun i : Fin n => (y i : ZMod 4)) =
          primePowQuotientVector (n := n) 2 2 (D.mkQ y) := by
            exact (primePowQuotientVector_mkQ (n := n) 2 2 y).symm
      _ = primePowQuotientVector (n := n) 2 2
            (quotientBasisFamilyMap D Y x) := by
            exact hq.symm
      _ = (localDualQuotientFamilyMatrix (n := n) 2 2 Y).mulVec
            (fun j : Fin n => (x j : ZMod 4)) := by
            exact hmat.symm
      _ = X.1.mulVec (fun j : Fin n => (x j : ZMod 4)) := by
            rw [hm]
  have hsum :
      ((∑ i, y i ^ 2 : ℤ) : ZMod 8) = ((∑ i, x i ^ 2 : ℤ) : ZMod 8) := by
    calc
      ((∑ i, y i ^ 2 : ℤ) : ZMod 8)
          = identityQuadraticModEight (fun i : Fin n => (y i : ZMod 4)) :=
            (identityQuadraticModEight_intCast y).symm
      _ = identityQuadraticModEight (X.1.mulVec (fun j : Fin n => (x j : ZMod 4))) := by
            rw [hvec]
      _ = identityQuadraticModEight (fun j : Fin n => (x j : ZMod 4)) := X.2 _
      _ = ((∑ i, x i ^ 2 : ℤ) : ZMod 8) := identityQuadraticModEight_intCast x
  simpa [primePowModulus, identityLattice_quadForm_eq_sum_sq] using hsum

/-- The diagonal Type I `ZMod 4` quadratic-isometry target maps back to the
native depth-three coordinate-solution subtype. -/
def identityQuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix
    {n : ℕ} (X : identityQuadraticIsometryModFour n) :
    identityLatticeDepthThreeCoordinateSolutionMatrix n :=
  ⟨X.1, identityQuadraticIsometryModFour_to_depthThreeCoordinateSolutionMatrix_mem X⟩

/-- The native depth-three matrix target for `Iₙ` is exactly the diagonal
mod-`4` quadratic-isometry target preserving `∑ xᵢ²` modulo `8`. -/
def identityLatticeDepthThreeCoordinateSolutionMatrixEquivQuadraticIsometryModFour
    (n : ℕ) :
    identityLatticeDepthThreeCoordinateSolutionMatrix n ≃ identityQuadraticIsometryModFour n where
  toFun := identityLatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour
  invFun := identityQuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl

/-- The native depth-three matrix target for `Iₙ` has the same cardinality as
the diagonal mod-`4` quadratic-isometry target. -/
theorem identityLatticeDepthThreeCoordinateSolutionMatrix_natCard_eq_quadraticIsometryModFour
    (n : ℕ) :
    Nat.card (identityLatticeDepthThreeCoordinateSolutionMatrix n) =
      Nat.card (identityQuadraticIsometryModFour n) :=
  Nat.card_congr (identityLatticeDepthThreeCoordinateSolutionMatrixEquivQuadraticIsometryModFour n)

/-- The quotient-family and `ZMod 4` matrix presentations of the Type I
identity-lattice depth-three coordinate target are equivalent. -/
noncomputable def identityLatticeDepthThreeCoordinateSolutionMatrixEquivFamily (n : ℕ) :
    identityLatticeDepthThreeCoordinateSolutionMatrix n ≃
      identityLatticeDepthThreeCoordinateSolutionFamily n where
  toFun X := ⟨localDualQuotientLiftFamily (n := n) 2 2 X.1, X.2⟩
  invFun Y :=
    ⟨localDualQuotientFamilyMatrix (n := n) 2 2 Y.1, by
      rw [localDualQuotientLiftFamily_familyMatrix]
      simp⟩
  left_inv X := by
    apply Subtype.ext
    exact localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
  right_inv Y := by
    apply Subtype.ext
    exact localDualQuotientLiftFamily_familyMatrix (n := n) 2 2 Y.1

/-- The Type I identity-lattice matrix and quotient-family finite targets have
the same cardinality. -/
theorem identityLattice_depthThreeCoordinateSolutionMatrix_natCard_eq_family
    (n : ℕ) :
    Nat.card (identityLatticeDepthThreeCoordinateSolutionMatrix n) =
      Nat.card (identityLatticeDepthThreeCoordinateSolutionFamily n) :=
  Nat.card_congr (identityLatticeDepthThreeCoordinateSolutionMatrixEquivFamily n)

/-- The quotient-family presentation of the Type I identity-lattice depth-three
target computes the native coordinate quotient count. -/
theorem identityLattice_depthThreeCoordinateSolutionFamily_natCard
    (n : ℕ) :
    Nat.card (identityLatticeDepthThreeCoordinateSolutionFamily n) =
      coordinateLocalDualQuotientCount (identityLattice n) 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  unfold identityLatticeDepthThreeCoordinateSolutionFamily coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The matrix presentation of the Type I identity-lattice depth-three target
computes the native coordinate quotient count. -/
theorem identityLattice_depthThreeCoordinateSolutionMatrix_natCard_eq_coordinateLocalDualQuotientCount
    (n : ℕ) :
    Nat.card (identityLatticeDepthThreeCoordinateSolutionMatrix n) =
      coordinateLocalDualQuotientCount (identityLattice n) 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  rw [identityLattice_depthThreeCoordinateSolutionMatrix_natCard_eq_family,
    identityLattice_depthThreeCoordinateSolutionFamily_natCard]

/-- The depth-three coordinate quotient count for `Iₙ` is the recursive Type I
quadratic-isometry count. -/
theorem identityLattice_coordinateLocalDualQuotientCount_two_three_eq_isometryCount
    (n : ℕ) :
    coordinateLocalDualQuotientCount (identityLattice n) 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) =
      identityQuadraticIsometryModFourCount n := by
  rw [← identityLattice_depthThreeCoordinateSolutionMatrix_natCard_eq_coordinateLocalDualQuotientCount]
  rw [identityLatticeDepthThreeCoordinateSolutionMatrix_natCard_eq_quadraticIsometryModFour,
    identityQuadraticIsometryModFour_natCard_eq_count]

/-- The native depth-three associated-bilinear dyadic count for `Iₙ` is the
recursive Type I quadratic-isometry count. -/
theorem identityLattice_associatedBilinearDualQuotientCount_two_three_eq_isometryCount
    (n : ℕ) :
    associatedBilinearDualQuotientCount (identityLattice n) 2 3 =
      identityQuadraticIsometryModFourCount n := by
  rw [associatedBilinearDualQuotientCount_two_three_eq_primePowCoordinateSubmodule
    (n := n) (L := identityLattice n) (identityLattice_isUnimodular n)]
  exact identityLattice_coordinateLocalDualQuotientCount_two_three_eq_isometryCount n

/-- The Type I identity-lattice dyadic local factor in native Schulze--Pillot
normalization, with the finite quotient count replaced by the recursive Type I
quadratic-isometry count. -/
theorem identityLattice_massLocalFactor_two_eq_isometryCount
    (n : ℕ) :
    (identityLattice n).massLocalFactor 2 =
      (((1 / 2 : ℚ) * (2 : ℚ) ^ n *
        ((2 : ℚ) ^ (3 * (n * (n - 1) / 2)))⁻¹ *
        (identityQuadraticIsometryModFourCount n : ℚ) : ℚ) : ℝ) *
        gramDetPadicValuationFactor 2 n n := by
  rw [massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular
    (n := n) (L := identityLattice n) (identityLattice_isUnimodular n),
    identityLattice_associatedBilinearDualQuotientCount_two_three_eq_isometryCount]

/-- In the classically unimodular dyadic identity-lattice case, the visible
Schulze--Pillot Gram-determinant valuation factor is the tangent half-power. -/
theorem gramDetPadicValuationFactor_two_rank_eq_tangentPow (n : ℕ) :
    gramDetPadicValuationFactor 2 n n =
      (2 : ℝ) ^ (n * (n - 1) / 2) := by
  unfold gramDetPadicValuationFactor
  rw [← Real.rpow_natCast (2 : ℝ) (n * (n - 1) / 2)]
  congr 1
  symm
  by_cases hn : n = 0
  · simp [hn]
  have hn_one : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  have hhalf :
      n * (n - 1) / 2 + n * (n - 1) / 2 = n * (n - 1) := by
    have h := Nat.div_two_mul_two_of_even heven
    omega
  have hhalf_real := congrArg (fun m : ℕ => (m : ℝ)) hhalf
  push_cast at hhalf_real
  rw [Nat.cast_sub hn_one] at hhalf_real
  norm_num at hhalf_real ⊢
  nlinarith

/-- The Type I identity-lattice dyadic local factor after cancelling one
tangent half-power from the depth-three quotient denominator.  This is the
first general simplification of the recursive finite count in the native
Schulze--Pillot normalization. -/
theorem identityLattice_massLocalFactor_two_eq_isometryCount_reduced
    (n : ℕ) :
    (identityLattice n).massLocalFactor 2 =
      (((1 / 2 : ℚ) * (2 : ℚ) ^ n *
        ((2 : ℚ) ^ (n * (n - 1)))⁻¹ *
        (identityQuadraticIsometryModFourCount n : ℚ) : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_eq_isometryCount]
  rw [gramDetPadicValuationFactor_two_rank_eq_tangentPow]
  have htri :
      3 * (n * (n - 1) / 2) = n * (n - 1) + n * (n - 1) / 2 := by
    have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
    have h := Nat.div_two_mul_two_of_even heven
    omega
  rw [htri, pow_add]
  norm_num [Rat.cast_mul, Rat.cast_inv, Rat.cast_pow]
  field_simp

/-- Positive-rank form of the Type I identity-lattice dyadic local factor:
the native local factor is the recursive finite isometry count divided by the
square power `2^((n-1)^2)`. -/
theorem identityLattice_massLocalFactor_two_eq_isometryCount_div_pow
    (n : ℕ) (hn : 1 ≤ n) :
    (identityLattice n).massLocalFactor 2 =
      (((identityQuadraticIsometryModFourCount n : ℚ) *
        ((2 : ℚ) ^ ((n - 1) * (n - 1)))⁻¹ : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_reduced]
  have hsq : n * (n - 1) = (n - 1) * (n - 1) + (n - 1) := by
    have hn_eq : n = (n - 1) + 1 := by omega
    nth_rewrite 1 [hn_eq]
    ring
  rw [hsq, pow_add]
  have hnexp : n = (n - 1) + 1 := by omega
  rw [hnexp, pow_add]
  norm_num [Rat.cast_mul, Rat.cast_inv, Rat.cast_pow]
  field_simp

/-- Successive positive-rank Type I identity-lattice dyadic local factors
differ by the ordinary norm-one column count divided by the new square-power
denominator.  This is the local-factor form of the corrected first-column
recurrence. -/
theorem identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount
    (n : ℕ) (hn : 1 ≤ n) :
    (identityLattice (n + 1)).massLocalFactor 2 =
      (identityLattice n).massLocalFactor 2 *
        (((identityQuadraticOrdinaryUnitVectorsModFourCount (n + 1) : ℚ) *
          ((2 : ℚ) ^ (2 * n - 1))⁻¹ : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow
    (n + 1) (by omega)]
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow n hn]
  have hcount :
      identityQuadraticIsometryModFourCount (n + 1) =
        identityQuadraticOrdinaryUnitVectorsModFourCount (n + 1) *
          identityQuadraticIsometryModFourCount n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hcount]
  have hsquare : n * n = (n - 1) * (n - 1) + (2 * n - 1) := by
    have hn_eq : n = (n - 1) + 1 := by omega
    nth_rewrite 1 [hn_eq]
    nth_rewrite 2 [hn_eq]
    ring_nf
    omega
  change (((identityQuadraticOrdinaryUnitVectorsModFourCount (n + 1) *
        identityQuadraticIsometryModFourCount n : ℕ) : ℚ) *
      ((2 : ℚ) ^ (n * n))⁻¹ : ℚ) =
    (((identityQuadraticIsometryModFourCount n : ℚ) *
        ((2 : ℚ) ^ ((n - 1) * (n - 1)))⁻¹ : ℚ) : ℝ) *
      (((identityQuadraticOrdinaryUnitVectorsModFourCount (n + 1) : ℚ) *
        ((2 : ℚ) ^ (2 * n - 1))⁻¹ : ℚ) : ℝ)
  rw [hsquare, pow_add]
  norm_num [Rat.cast_mul, Rat.cast_inv, Rat.cast_pow]
  ring_nf

/-- The normalized ordinary-column multiplier that advances the Type I identity
local factor from rank `m - 1` to rank `m`.  It is kept as a rational number so
finite products can be stated without repeatedly expanding real casts. -/
def identityQuadraticTypeILocalFactorStep (m : ℕ) : ℚ :=
  (identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) *
    ((2 : ℚ) ^ (2 * m - 3))⁻¹

/-- Candidate closed residue-class formula for the normalized Type I identity
local-factor step.  The remaining Type I finite-count problem is to prove that
`identityQuadraticTypeILocalFactorStep m` agrees with this branch formula in the
rank families needed by the mass assembly. -/
def identityQuadraticTypeILocalFactorStepClosed (m : ℕ) : ℚ :=
  if m % 4 = 0 then 1
  else if m % 8 = 2 then 1 + ((2 : ℚ) ^ (m / 2 - 1))⁻¹
  else if m % 8 = 6 then 1 - ((2 : ℚ) ^ (m / 2 - 1))⁻¹
  else if m % 8 = 3 then 1 + ((2 : ℚ) ^ ((m - 1) / 2))⁻¹
  else if m % 8 = 7 then 1 - ((2 : ℚ) ^ ((m - 1) / 2))⁻¹
  else if m % 8 = 1 then
    1 + (((2 : ℚ) ^ ((m - 3) / 2) - 1) * ((2 : ℚ) ^ (m - 2))⁻¹)
  else if m % 8 = 5 then
    1 - (((2 : ℚ) ^ ((m - 3) / 2) + 1) * ((2 : ℚ) ^ (m - 2))⁻¹)
  else 0

/-- The closed Type I step candidate is `1` in ranks divisible by four. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_four_eq_zero {m : ℕ}
    (hm : m % 4 = 0) :
    identityQuadraticTypeILocalFactorStepClosed m = 1 := by
  simp [identityQuadraticTypeILocalFactorStepClosed, hm]

/-- The closed Type I step candidate in ranks `2 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_two {m : ℕ}
    (hm : m % 8 = 2) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 + ((2 : ℚ) ^ (m / 2 - 1))⁻¹ := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- The closed Type I step candidate in ranks `6 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_six {m : ℕ}
    (hm : m % 8 = 6) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 - ((2 : ℚ) ^ (m / 2 - 1))⁻¹ := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- The closed Type I step candidate in ranks `3 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_three {m : ℕ}
    (hm : m % 8 = 3) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 + ((2 : ℚ) ^ ((m - 1) / 2))⁻¹ := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- The closed Type I step candidate in ranks `7 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_seven {m : ℕ}
    (hm : m % 8 = 7) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 - ((2 : ℚ) ^ ((m - 1) / 2))⁻¹ := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- The closed Type I step candidate in ranks `1 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_one {m : ℕ}
    (hm : m % 8 = 1) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 + (((2 : ℚ) ^ ((m - 3) / 2) - 1) * ((2 : ℚ) ^ (m - 2))⁻¹) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- The closed Type I step candidate in ranks `5 mod 8`. -/
theorem identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_five {m : ℕ}
    (hm : m % 8 = 5) :
    identityQuadraticTypeILocalFactorStepClosed m =
      1 - (((2 : ℚ) ^ ((m - 3) / 2) + 1) * ((2 : ℚ) ^ (m - 2))⁻¹) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticTypeILocalFactorStepClosed, h4, hm]

/-- Natural-number closed-count target for ordinary norm-one Type I columns.
This is the integral version of `identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ`.
The remaining finite-count problem can be stated without rational inverses:
prove that the recursive ordinary-column count equals this branch formula. -/
def identityQuadraticOrdinaryUnitVectorsModFourCountClosed (m : ℕ) : ℕ :=
  if m % 4 = 0 then 2 ^ (2 * m - 3)
  else if m % 8 = 2 then 2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - (m / 2 - 1))
  else if m % 8 = 6 then 2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - (m / 2 - 1))
  else if m % 8 = 3 then 2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - ((m - 1) / 2))
  else if m % 8 = 7 then 2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - ((m - 1) / 2))
  else if m % 8 = 1 then 2 ^ (2 * m - 3) + (2 ^ ((m - 3) / 2) - 1) * 2 ^ (m - 1)
  else if m % 8 = 5 then 2 ^ (2 * m - 3) - (2 ^ ((m - 3) / 2) + 1) * 2 ^ (m - 1)
  else 0

/-- Natural closed ordinary-column target in ranks divisible by four. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_four_eq_zero
    {m : ℕ} (hm : m % 4 = 0) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m = 2 ^ (2 * m - 3) := by
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, hm]

/-- Natural closed ordinary-column target in ranks `2 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_two
    {m : ℕ} (hm : m % 8 = 2) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - (m / 2 - 1)) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural closed ordinary-column target in ranks `6 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_six
    {m : ℕ} (hm : m % 8 = 6) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - (m / 2 - 1)) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural closed ordinary-column target in ranks `3 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - ((m - 1) / 2)) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural closed ordinary-column target in ranks `7 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - ((m - 1) / 2)) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural closed ordinary-column target in ranks `1 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_one
    {m : ℕ} (hm : m % 8 = 1) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + (2 ^ ((m - 3) / 2) - 1) * 2 ^ (m - 1) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural closed ordinary-column target in ranks `5 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_five
    {m : ℕ} (hm : m % 8 = 5) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - (2 ^ ((m - 3) / 2) + 1) * 2 ^ (m - 1) := by
  have h4 : m % 4 ≠ 0 := by omega
  simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosed, h4, hm]

/-- Natural-number closed-count target for the full norm-one Type I shell.
It is the ordinary-column target plus the characteristic all-odd contribution
that occurs exactly in ranks congruent to `1 mod 8`.  Proving the recursive
shell count equals this target implies the ordinary-column closed count. -/
def identityQuadraticUnitVectorsModFourCountClosed (m : ℕ) : ℕ :=
  identityQuadraticOrdinaryUnitVectorsModFourCountClosed m +
    if ((m : ℕ) : ZMod 8) = 1 then 2 ^ m else 0

/-- A modulo-eight equality, phrased as an ordinary natural remainder, gives the
corresponding equality in `ZMod 8`. -/
theorem natCast_zmod_eight_eq_of_mod_eq {m a : ℕ} (h : m % 8 = a % 8) :
    ((m : ℕ) : ZMod 8) = (a : ZMod 8) := by
  exact (ZMod.natCast_eq_natCast_iff' m a 8).mpr h

/-- A `ZMod 8` equality can be read back as equality of natural remainders. -/
theorem mod_eq_of_natCast_zmod_eight_eq {m a : ℕ}
    (h : ((m : ℕ) : ZMod 8) = (a : ZMod 8)) :
    m % 8 = a % 8 := by
  exact (ZMod.natCast_eq_natCast_iff' m a 8).mp h

/-- If a natural rank is divisible by four, it is not congruent to one in `ZMod 8`. -/
theorem natCast_zmod_eight_ne_one_of_mod_four_eq_zero {m : ℕ} (hm : m % 4 = 0) :
    ((m : ℕ) : ZMod 8) ≠ 1 := by
  intro hz
  have hm8 : m % 8 = 1 := by
    have h := mod_eq_of_natCast_zmod_eight_eq (m := m) (a := 1) hz
    simpa using h
  omega

/-- Ranks congruent to a residue other than one modulo eight are not congruent to
one in `ZMod 8`. -/
theorem natCast_zmod_eight_ne_one_of_mod_eight_eq {m a : ℕ}
    (hm : m % 8 = a) (ha : a ≠ 1) :
    ((m : ℕ) : ZMod 8) ≠ 1 := by
  intro hz
  have hm8 : m % 8 = 1 := by
    have h := mod_eq_of_natCast_zmod_eight_eq (m := m) (a := 1) hz
    simpa using h
  omega

/-- Total closed shell target in ranks divisible by four. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero
    {m : ℕ} (hm : m % 4 = 0) :
    identityQuadraticUnitVectorsModFourCountClosed m = 2 ^ (2 * m - 3) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_four_eq_zero hm]
  have hnot := natCast_zmod_eight_ne_one_of_mod_four_eq_zero hm
  simp [hnot]

/-- Total closed shell target in ranks `2 mod 8`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_two
    {m : ℕ} (hm : m % 8 = 2) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - (m / 2 - 1)) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_two hm]
  have hnot : ((m : ℕ) : ZMod 8) ≠ 1 :=
    natCast_zmod_eight_ne_one_of_mod_eight_eq hm (by norm_num)
  simp [hnot]

/-- Total closed shell target in ranks `6 mod 8`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_six
    {m : ℕ} (hm : m % 8 = 6) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - (m / 2 - 1)) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_six hm]
  have hnot : ((m : ℕ) : ZMod 8) ≠ 1 :=
    natCast_zmod_eight_ne_one_of_mod_eight_eq hm (by norm_num)
  simp [hnot]

/-- Total closed shell target in ranks `3 mod 8`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + 2 ^ (2 * m - 3 - ((m - 1) / 2)) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_three hm]
  have hnot : ((m : ℕ) : ZMod 8) ≠ 1 :=
    natCast_zmod_eight_ne_one_of_mod_eight_eq hm (by norm_num)
  simp [hnot]

/-- Total closed shell target in ranks `7 mod 8`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - 2 ^ (2 * m - 3 - ((m - 1) / 2)) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_seven hm]
  have hnot : ((m : ℕ) : ZMod 8) ≠ 1 :=
    natCast_zmod_eight_ne_one_of_mod_eight_eq hm (by norm_num)
  simp [hnot]

/-- Total closed shell target in ranks `1 mod 8`, where the characteristic
all-odd shell contributes `2^m`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_one
    {m : ℕ} (hm : m % 8 = 1) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) + (2 ^ ((m - 3) / 2) + 1) * 2 ^ (m - 1) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_one hm]
  have hz : ((m : ℕ) : ZMod 8) = 1 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 1) (by simpa using hm)
  simp [hz]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hmpos : 1 ≤ m := by omega
    have hm_eq : m = (m - 1) + 1 := by omega
    rw [hm_eq, pow_add]
    norm_num [mul_comm]
  rw [hpow]
  let a : ℕ := 2 ^ ((m - 3) / 2)
  let p : ℕ := 2 ^ (m - 1)
  have ha : 1 ≤ a := by
    dsimp [a]
    exact Nat.one_le_pow _ _ (by norm_num)
  change 2 ^ (2 * m - 3) + (a - 1) * p + 2 * p =
      2 ^ (2 * m - 3) + (a + 1) * p
  have hterm : (a - 1) * p + 2 * p = (a + 1) * p := by
    have hp_le : p ≤ a * p := by
      simpa [one_mul] using Nat.mul_le_mul_right p ha
    rw [Nat.sub_mul, add_mul, one_mul]
    omega
  omega

/-- Total closed shell target in ranks `5 mod 8`. -/
theorem identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_five
    {m : ℕ} (hm : m % 8 = 5) :
    identityQuadraticUnitVectorsModFourCountClosed m =
      2 ^ (2 * m - 3) - (2 ^ ((m - 3) / 2) + 1) * 2 ^ (m - 1) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_five hm]
  have hnot : ((m : ℕ) : ZMod 8) ≠ 1 :=
    natCast_zmod_eight_ne_one_of_mod_eight_eq hm (by norm_num)
  simp [hnot]

/-- Even-frequency correction for the all-residue closed Type I shell target.
This is the finite Fourier contribution from the two primitive fourth-root
frequencies in the diagonal mod-`8` shell count. -/
def identityQuadraticShellModEightEvenCorrectionClosed (m : ℕ) (r : ZMod 8) : ℤ :=
  let evenMag : ℤ := (2 : ℤ) ^ (3 * (m / 2) - 2)
  let oddMag : ℤ := (2 : ℤ) ^ ((3 * m - 5) / 2)
  if m % 8 = 0 then
    if r = 0 ∨ r = 4 then evenMag else if r = 2 ∨ r = 6 then -evenMag else 0
  else if m % 8 = 2 then
    if r = 1 ∨ r = 5 then evenMag else if r = 3 ∨ r = 7 then -evenMag else 0
  else if m % 8 = 4 then
    if r = 2 ∨ r = 6 then evenMag else if r = 0 ∨ r = 4 then -evenMag else 0
  else if m % 8 = 6 then
    if r = 3 ∨ r = 7 then evenMag else if r = 1 ∨ r = 5 then -evenMag else 0
  else if m % 8 = 1 then
    if r = 0 ∨ r = 1 ∨ r = 4 ∨ r = 5 then oddMag else -oddMag
  else if m % 8 = 3 then
    if r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 6 then oddMag else -oddMag
  else if m % 8 = 5 then
    if r = 2 ∨ r = 3 ∨ r = 6 ∨ r = 7 then oddMag else -oddMag
  else
    if r = 0 ∨ r = 3 ∨ r = 4 ∨ r = 7 then oddMag else -oddMag

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `2 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_two
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 1))
      (identityQuadraticShellModelPhaseB (8 * q + 1)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 2) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_one,
    identityQuadraticShellModelPhaseB_eight_mul_add_one,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 2) % 8 = 2 := by omega
  have hdiv : (8 * q + 2) / 2 = 4 * q + 1 := by omega
  have hpow : 3 * (4 * q + 1) - 2 = 12 * q + 1 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 1) = 16 * 2 ^ (12 * q) := by
    rw [show (16 : ℤ) = 2 ^ 4 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((0 : ZMod 8) = 1 ∨ (0 : ZMod 8) = 5) := by decide
  have h1 : ¬((0 : ZMod 8) = 3 ∨ (0 : ZMod 8) = 7) := by decide
  have h2 : ¬((2 : ZMod 8) = 1 ∨ (2 : ZMod 8) = 5) := by decide
  have h3 : ¬((2 : ZMod 8) = 3 ∨ (2 : ZMod 8) = 7) := by decide
  have h4 : ¬((3 : ZMod 8) = 1 ∨ (3 : ZMod 8) = 5) := by decide
  have h5 : ¬((4 : ZMod 8) = 1 ∨ (4 : ZMod 8) = 5) := by decide
  have h6 : ¬((4 : ZMod 8) = 3 ∨ (4 : ZMod 8) = 7) := by decide
  have h7 : ¬((6 : ZMod 8) = 1 ∨ (6 : ZMod 8) = 5) := by decide
  have h8 : ¬((6 : ZMod 8) = 3 ∨ (6 : ZMod 8) = 7) := by decide
  have h9 : ¬((7 : ZMod 8) = 1 ∨ (7 : ZMod 8) = 5) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hdiv, hpow, hscale, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `3 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_three
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 2))
      (identityQuadraticShellModelPhaseB (8 * q + 2)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 3) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_two,
    identityQuadraticShellModelPhaseB_eight_mul_add_two,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 3) % 8 = 3 := by omega
  have hpow : (3 * (8 * q + 3) - 5) / 2 = 12 * q + 2 := by omega
  have h0 : ¬((0 : ZMod 8) = 1 ∨ (0 : ZMod 8) = 2 ∨
      (0 : ZMod 8) = 5 ∨ (0 : ZMod 8) = 6) := by decide
  have h3 : ¬((3 : ZMod 8) = 1 ∨ (3 : ZMod 8) = 2 ∨
      (3 : ZMod 8) = 5 ∨ (3 : ZMod 8) = 6) := by decide
  have h4 : ¬((4 : ZMod 8) = 1 ∨ (4 : ZMod 8) = 2 ∨
      (4 : ZMod 8) = 5 ∨ (4 : ZMod 8) = 6) := by decide
  have h7 : ¬((7 : ZMod 8) = 1 ∨ (7 : ZMod 8) = 2 ∨
      (7 : ZMod 8) = 5 ∨ (7 : ZMod 8) = 6) := by decide
  have h16 : (16 : ℤ) * 2 ^ (12 * q) = 2 ^ (12 * q + 4) := by
    rw [show (16 : ℤ) = 2 ^ 4 by norm_num]
    rw [← pow_add]
    congr 1
    omega
  have h8 : (8 : ℤ) * 2 ^ (12 * q + 2) = 2 ^ (12 * q + 5) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add]
    congr 1
    omega
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hpow, h0, h3, h4, h7,
      h16, h8] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `4 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_four
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 3))
      (identityQuadraticShellModelPhaseB (8 * q + 3)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 4) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_three,
    identityQuadraticShellModelPhaseB_eight_mul_add_three,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 4) % 8 = 4 := by omega
  have hdiv : (8 * q + 4) / 2 = 4 * q + 2 := by omega
  have hpow : 3 * (4 * q + 2) - 2 = 12 * q + 4 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 4) = 128 * 2 ^ (12 * q) := by
    rw [show (128 : ℤ) = 2 ^ 7 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((0 : ZMod 8) = 2 ∨ (0 : ZMod 8) = 6) := by decide
  have h1 : ¬((1 : ZMod 8) = 2 ∨ (1 : ZMod 8) = 6) := by decide
  have h2 : ¬((1 : ZMod 8) = 0 ∨ (1 : ZMod 8) = 4) := by decide
  have h3 : ¬((3 : ZMod 8) = 2 ∨ (3 : ZMod 8) = 6) := by decide
  have h4 : ¬((3 : ZMod 8) = 0 ∨ (3 : ZMod 8) = 4) := by decide
  have h5 : ¬((4 : ZMod 8) = 2 ∨ (4 : ZMod 8) = 6) := by decide
  have h6 : ¬((5 : ZMod 8) = 2 ∨ (5 : ZMod 8) = 6) := by decide
  have h7 : ¬((5 : ZMod 8) = 0 ∨ (5 : ZMod 8) = 4) := by decide
  have h8 : ¬((7 : ZMod 8) = 2 ∨ (7 : ZMod 8) = 6) := by decide
  have h9 : ¬((7 : ZMod 8) = 0 ∨ (7 : ZMod 8) = 4) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hdiv, hpow, hscale, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `5 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_five
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 4))
      (identityQuadraticShellModelPhaseB (8 * q + 4)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 5) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_four,
    identityQuadraticShellModelPhaseB_eight_mul_add_four,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 5) % 8 = 5 := by omega
  have hpow : (3 * (8 * q + 5) - 5) / 2 = 12 * q + 5 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 5) = 256 * 2 ^ (12 * q) := by
    rw [show (256 : ℤ) = 2 ^ 8 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((0 : ZMod 8) = 2 ∨ (0 : ZMod 8) = 3 ∨ (0 : ZMod 8) = 6 ∨ (0 : ZMod 8) = 7) := by decide
  have h1 : ¬((1 : ZMod 8) = 2 ∨ (1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 6 ∨ (1 : ZMod 8) = 7) := by decide
  have h2 : ¬((4 : ZMod 8) = 2 ∨ (4 : ZMod 8) = 3 ∨ (4 : ZMod 8) = 6 ∨ (4 : ZMod 8) = 7) := by decide
  have h3 : ¬((5 : ZMod 8) = 2 ∨ (5 : ZMod 8) = 3 ∨ (5 : ZMod 8) = 6 ∨ (5 : ZMod 8) = 7) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hpow, hscale, h0, h1, h2, h3] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `6 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_six
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 5))
      (identityQuadraticShellModelPhaseB (8 * q + 5)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 6) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_five,
    identityQuadraticShellModelPhaseB_eight_mul_add_five,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 6) % 8 = 6 := by omega
  have hdiv : (8 * q + 6) / 2 = 4 * q + 3 := by omega
  have hpow : 3 * (4 * q + 3) - 2 = 12 * q + 7 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 7) = 1024 * 2 ^ (12 * q) := by
    rw [show (1024 : ℤ) = 2 ^ 10 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((0 : ZMod 8) = 3 ∨ (0 : ZMod 8) = 7) := by decide
  have h1 : ¬((0 : ZMod 8) = 1 ∨ (0 : ZMod 8) = 5) := by decide
  have h2 : ¬((1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 7) := by decide
  have h3 : ¬((2 : ZMod 8) = 3 ∨ (2 : ZMod 8) = 7) := by decide
  have h4 : ¬((2 : ZMod 8) = 1 ∨ (2 : ZMod 8) = 5) := by decide
  have h5 : ¬((4 : ZMod 8) = 3 ∨ (4 : ZMod 8) = 7) := by decide
  have h6 : ¬((4 : ZMod 8) = 1 ∨ (4 : ZMod 8) = 5) := by decide
  have h7 : ¬((5 : ZMod 8) = 3 ∨ (5 : ZMod 8) = 7) := by decide
  have h8 : ¬((6 : ZMod 8) = 3 ∨ (6 : ZMod 8) = 7) := by decide
  have h9 : ¬((6 : ZMod 8) = 1 ∨ (6 : ZMod 8) = 5) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hdiv, hpow, hscale, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In ranks `7 mod 8`, the closed phase part of the shell model is exactly
the even-frequency correction in the all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_seven
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 6))
      (identityQuadraticShellModelPhaseB (8 * q + 6)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 7) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_six,
    identityQuadraticShellModelPhaseB_eight_mul_add_six,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 7) % 8 = 7 := by omega
  have hpow : (3 * (8 * q + 7) - 5) / 2 = 12 * q + 8 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 8) = 2048 * 2 ^ (12 * q) := by
    rw [show (2048 : ℤ) = 2 ^ 11 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((1 : ZMod 8) = 0 ∨ (1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 4 ∨ (1 : ZMod 8) = 7) := by decide
  have h1 : ¬((2 : ZMod 8) = 0 ∨ (2 : ZMod 8) = 3 ∨ (2 : ZMod 8) = 4 ∨ (2 : ZMod 8) = 7) := by decide
  have h2 : ¬((5 : ZMod 8) = 0 ∨ (5 : ZMod 8) = 3 ∨ (5 : ZMod 8) = 4 ∨ (5 : ZMod 8) = 7) := by decide
  have h3 : ¬((6 : ZMod 8) = 0 ∨ (6 : ZMod 8) = 3 ∨ (6 : ZMod 8) = 4 ∨ (6 : ZMod 8) = 7) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hpow, hscale, h0, h1, h2, h3] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In positive ranks `0 mod 8`, written as `8 * q + 8`, the closed phase
part of the shell model is exactly the even-frequency correction in the
all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_eight
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 7))
      (identityQuadraticShellModelPhaseB (8 * q + 7)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 8) r := by
  rw [identityQuadraticShellModelPhaseA_eight_mul_add_seven,
    identityQuadraticShellModelPhaseB_eight_mul_add_seven,
    identityQuadraticShellModelPhaseScale_eq_pow]
  have hmod : (8 * q + 8) % 8 = 0 := by omega
  have hdiv : (8 * q + 8) / 2 = 4 * q + 4 := by omega
  have hpow : 3 * (4 * q + 4) - 2 = 12 * q + 10 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 10) = 8192 * 2 ^ (12 * q) := by
    rw [show (8192 : ℤ) = 2 ^ 13 by norm_num, show (8 : ℤ) = 2 ^ 3 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((1 : ZMod 8) = 0 ∨ (1 : ZMod 8) = 4) := by decide
  have h1 : ¬((1 : ZMod 8) = 2 ∨ (1 : ZMod 8) = 6) := by decide
  have h2 : ¬((2 : ZMod 8) = 0 ∨ (2 : ZMod 8) = 4) := by decide
  have h3 : ¬((3 : ZMod 8) = 0 ∨ (3 : ZMod 8) = 4) := by decide
  have h4 : ¬((3 : ZMod 8) = 2 ∨ (3 : ZMod 8) = 6) := by decide
  have h5 : ¬((5 : ZMod 8) = 0 ∨ (5 : ZMod 8) = 4) := by decide
  have h6 : ¬((5 : ZMod 8) = 2 ∨ (5 : ZMod 8) = 6) := by decide
  have h7 : ¬((6 : ZMod 8) = 0 ∨ (6 : ZMod 8) = 4) := by decide
  have h8 : ¬((7 : ZMod 8) = 0 ∨ (7 : ZMod 8) = 4) := by decide
  have h9 : ¬((7 : ZMod 8) = 2 ∨ (7 : ZMod 8) = 6) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hdiv, hpow, hscale, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- In positive ranks `1 mod 8`, written as `8 * q + 9`, the closed phase
part of the shell model is exactly the even-frequency correction in the
all-residue integer shell target. -/
theorem identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_nine
    (q : ℕ) (r : ZMod 8) :
    2 * identityQuadraticShellPhase
      (identityQuadraticShellModelPhaseA (8 * q + 8))
      (identityQuadraticShellModelPhaseB (8 * q + 8)) r =
    8 * identityQuadraticShellModEightEvenCorrectionClosed (8 * q + 9) r := by
  rw [show 8 * q + 8 = 8 * (q + 1) by omega]
  rw [identityQuadraticShellModelPhaseA_eight_mul,
    identityQuadraticShellModelPhaseB_eight_mul,
    identityQuadraticShellModelPhaseScale_eq_pow]
  rw [show 12 * (q + 1) = 12 * q + 12 by omega]
  have hmod : (8 * q + 9) % 8 = 1 := by omega
  have hpow : (3 * (8 * q + 9) - 5) / 2 = 12 * q + 11 := by omega
  have hscale : (8 : ℤ) * 2 ^ (12 * q + 11) = 4 * 2 ^ (12 * q + 12) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, show (4 : ℤ) = 2 ^ 2 by norm_num]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h0 : ¬((2 : ZMod 8) = 0 ∨ (2 : ZMod 8) = 1 ∨ (2 : ZMod 8) = 4 ∨ (2 : ZMod 8) = 5) := by decide
  have h1 : ¬((3 : ZMod 8) = 0 ∨ (3 : ZMod 8) = 1 ∨ (3 : ZMod 8) = 4 ∨ (3 : ZMod 8) = 5) := by decide
  have h2 : ¬((6 : ZMod 8) = 0 ∨ (6 : ZMod 8) = 1 ∨ (6 : ZMod 8) = 4 ∨ (6 : ZMod 8) = 5) := by decide
  have h3 : ¬((7 : ZMod 8) = 0 ∨ (7 : ZMod 8) = 1 ∨ (7 : ZMod 8) = 4 ∨ (7 : ZMod 8) = 5) := by decide
  fin_cases r <;>
    simp [identityQuadraticShellPhase_zero, identityQuadraticShellPhase_one,
      identityQuadraticShellPhase_two, identityQuadraticShellPhase_three,
      identityQuadraticShellPhase_four, identityQuadraticShellPhase_five,
      identityQuadraticShellPhase_six, identityQuadraticShellPhase_seven,
      identityQuadraticShellModEightEvenCorrectionClosed, hmod, hpow, hscale,
      h0, h1, h2, h3] <;> ring

/-- Odd-character correction for the all-residue closed Type I shell target.
It contributes in the two residues differing by four from the rank. -/
def identityQuadraticShellModEightOddCharacterClosed (m : ℕ) (r : ZMod 8) : ℤ :=
  let oddCharMag : ℤ := (2 : ℤ) ^ (m - 1)
  if r = ((m : ℕ) : ZMod 8) then oddCharMag
  else if r = ((m : ℕ) : ZMod 8) - 4 then -oddCharMag
  else 0


/-- The delta part of the powered shell model is exactly the scaled odd-character
correction in positive rank. -/
theorem identityQuadraticShellDelta_eq_scaled_oddCharacterClosed
    {m : ℕ} (hm : 0 < m) (r : ZMod 8) :
    (2 : ℤ) ^ (m + 2) * identityQuadraticShellDelta ((m : ℕ) : ZMod 8) r =
      8 * identityQuadraticShellModEightOddCharacterClosed m r := by
  by_cases h : r = ((m : ℕ) : ZMod 8)
  · have hpow : (8 : ℤ) * 2 ^ (m - 1) = 2 ^ (m + 2) := by
      rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
      rw [← pow_add]
      congr 1
      omega
    simp [identityQuadraticShellDelta, identityQuadraticShellModEightOddCharacterClosed, h, hpow]
  · by_cases h4 : r = ((m : ℕ) : ZMod 8) - 4
    · have hpow : (8 : ℤ) * 2 ^ (m - 1) = 2 ^ (m + 2) := by
        rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
        rw [← pow_add]
        congr 1
        omega
      simp [identityQuadraticShellDelta, identityQuadraticShellModEightOddCharacterClosed, h4, hpow]
    · simp [identityQuadraticShellDelta, identityQuadraticShellModEightOddCharacterClosed, h, h4]

/-- Integer closed target for every residue of the Type I diagonal mod-`8`
shell count.  The residue-`1` branch is designed to recover
`identityQuadraticUnitVectorsModFourCountClosed`. -/
def identityQuadraticShellModEightCountClosedInt (m : ℕ) (r : ZMod 8) : ℤ :=
  (2 : ℤ) ^ (2 * m - 3) +
    identityQuadraticShellModEightEvenCorrectionClosed m r +
    identityQuadraticShellModEightOddCharacterClosed m r


/-- If the phase part matches the closed even-frequency correction, then the
whole powered shell model matches eight times the all-residue integer closed
shell target. -/
theorem identityQuadraticShellModel_eq_scaled_closedInt_of_phase
    {m : ℕ} (hm : 2 ≤ m) (a b : ℤ) (r : ZMod 8)
    (hphase : 2 * identityQuadraticShellPhase a b r =
      8 * identityQuadraticShellModEightEvenCorrectionClosed m r) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * m)) a b ((2 : ℤ) ^ (m + 2))
        ((m : ℕ) : ZMod 8) r =
      8 * identityQuadraticShellModEightCountClosedInt m r := by
  have hmpos : 0 < m := by omega
  have huniform : (2 : ℤ) ^ (2 * m) = 8 * (2 : ℤ) ^ (2 * m - 3) := by
    rw [show 2 * m = (2 * m - 3) + 3 by omega]
    rw [pow_add]
    norm_num
    ring
  rw [identityQuadraticShellModel, identityQuadraticShellModEightCountClosedInt]
  rw [hphase, identityQuadraticShellDelta_eq_scaled_oddCharacterClosed hmpos r, huniform]
  ring

/-- Powered shell-model comparison with the all-residue closed target in the
`two` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_two
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 2)))
      (identityQuadraticShellModelPhaseA (8 * q + 1))
      (identityQuadraticShellModelPhaseB (8 * q + 1))
      ((2 : ℤ) ^ (8 * q + 4)) (((8 * q + 2 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 2) r := by
  simpa [show (8 * q + 2) + 2 = 8 * q + 4 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 2) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 1))
      (identityQuadraticShellModelPhaseB (8 * q + 1)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_two q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`three` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_three
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 3)))
      (identityQuadraticShellModelPhaseA (8 * q + 2))
      (identityQuadraticShellModelPhaseB (8 * q + 2))
      ((2 : ℤ) ^ (8 * q + 5)) (((8 * q + 3 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 3) r := by
  simpa [show (8 * q + 3) + 2 = 8 * q + 5 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 3) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 2))
      (identityQuadraticShellModelPhaseB (8 * q + 2)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_three q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`four` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_four
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 4)))
      (identityQuadraticShellModelPhaseA (8 * q + 3))
      (identityQuadraticShellModelPhaseB (8 * q + 3))
      ((2 : ℤ) ^ (8 * q + 6)) (((8 * q + 4 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 4) r := by
  simpa [show (8 * q + 4) + 2 = 8 * q + 6 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 4) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 3))
      (identityQuadraticShellModelPhaseB (8 * q + 3)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_four q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`five` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_five
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 5)))
      (identityQuadraticShellModelPhaseA (8 * q + 4))
      (identityQuadraticShellModelPhaseB (8 * q + 4))
      ((2 : ℤ) ^ (8 * q + 7)) (((8 * q + 5 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 5) r := by
  simpa [show (8 * q + 5) + 2 = 8 * q + 7 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 5) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 4))
      (identityQuadraticShellModelPhaseB (8 * q + 4)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_five q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`six` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_six
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 6)))
      (identityQuadraticShellModelPhaseA (8 * q + 5))
      (identityQuadraticShellModelPhaseB (8 * q + 5))
      ((2 : ℤ) ^ (8 * q + 8)) (((8 * q + 6 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 6) r := by
  simpa [show (8 * q + 6) + 2 = 8 * q + 8 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 6) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 5))
      (identityQuadraticShellModelPhaseB (8 * q + 5)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_six q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`seven` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_seven
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 7)))
      (identityQuadraticShellModelPhaseA (8 * q + 6))
      (identityQuadraticShellModelPhaseB (8 * q + 6))
      ((2 : ℤ) ^ (8 * q + 9)) (((8 * q + 7 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 7) r := by
  simpa [show (8 * q + 7) + 2 = 8 * q + 9 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 7) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 6))
      (identityQuadraticShellModelPhaseB (8 * q + 6)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_seven q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`eight` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_eight
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 8)))
      (identityQuadraticShellModelPhaseA (8 * q + 7))
      (identityQuadraticShellModelPhaseB (8 * q + 7))
      ((2 : ℤ) ^ (8 * q + 10)) (((8 * q + 8 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 8) r := by
  simpa [show (8 * q + 8) + 2 = 8 * q + 10 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 8) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 7))
      (identityQuadraticShellModelPhaseB (8 * q + 7)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_eight q r)

/-- Powered shell-model comparison with the all-residue closed target in the
`nine` residue family. -/
theorem identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_nine
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 9)))
      (identityQuadraticShellModelPhaseA (8 * q + 8))
      (identityQuadraticShellModelPhaseB (8 * q + 8))
      ((2 : ℤ) ^ (8 * q + 11)) (((8 * q + 9 : ℕ) : ZMod 8)) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 9) r := by
  simpa [show (8 * q + 9) + 2 = 8 * q + 11 by omega] using
    identityQuadraticShellModel_eq_scaled_closedInt_of_phase (m := 8 * q + 9) (by omega)
      (identityQuadraticShellModelPhaseA (8 * q + 8))
      (identityQuadraticShellModelPhaseB (8 * q + 8)) r
      (identityQuadraticShellModelPhase_evenCorrection_eight_mul_add_nine q r)

/-- Recursive integer shell count equals the all-residue closed target in the
`two` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_two
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 2) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 2) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 2) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 2)))
        (identityQuadraticShellModelPhaseA (8 * q + 1))
        (identityQuadraticShellModelPhaseB (8 * q + 1))
        ((2 : ℤ) ^ (8 * q + 4)) (((8 * q + 2 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 1) + 1 = 8 * q + 2 by omega, show (8 * q + 1) + 3 = 8 * q + 4 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 1) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_two q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 2) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 2) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`three` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_three
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 3) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 3) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 3) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 3)))
        (identityQuadraticShellModelPhaseA (8 * q + 2))
        (identityQuadraticShellModelPhaseB (8 * q + 2))
        ((2 : ℤ) ^ (8 * q + 5)) (((8 * q + 3 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 2) + 1 = 8 * q + 3 by omega, show (8 * q + 2) + 3 = 8 * q + 5 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 2) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_three q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 3) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 3) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`four` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_four
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 4) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 4) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 4) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 4)))
        (identityQuadraticShellModelPhaseA (8 * q + 3))
        (identityQuadraticShellModelPhaseB (8 * q + 3))
        ((2 : ℤ) ^ (8 * q + 6)) (((8 * q + 4 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 3) + 1 = 8 * q + 4 by omega, show (8 * q + 3) + 3 = 8 * q + 6 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 3) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_four q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 4) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 4) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`five` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_five
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 5) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 5) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 5) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 5)))
        (identityQuadraticShellModelPhaseA (8 * q + 4))
        (identityQuadraticShellModelPhaseB (8 * q + 4))
        ((2 : ℤ) ^ (8 * q + 7)) (((8 * q + 5 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 4) + 1 = 8 * q + 5 by omega, show (8 * q + 4) + 3 = 8 * q + 7 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 4) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_five q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 5) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 5) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`six` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_six
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 6) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 6) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 6) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 6)))
        (identityQuadraticShellModelPhaseA (8 * q + 5))
        (identityQuadraticShellModelPhaseB (8 * q + 5))
        ((2 : ℤ) ^ (8 * q + 8)) (((8 * q + 6 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 5) + 1 = 8 * q + 6 by omega, show (8 * q + 5) + 3 = 8 * q + 8 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 5) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_six q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 6) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 6) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`seven` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_seven
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 7) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 7) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 7) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 7)))
        (identityQuadraticShellModelPhaseA (8 * q + 6))
        (identityQuadraticShellModelPhaseB (8 * q + 6))
        ((2 : ℤ) ^ (8 * q + 9)) (((8 * q + 7 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 6) + 1 = 8 * q + 7 by omega, show (8 * q + 6) + 3 = 8 * q + 9 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 6) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_seven q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 7) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 7) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`eight` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_eight
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 8) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 8) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 8) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 8)))
        (identityQuadraticShellModelPhaseA (8 * q + 7))
        (identityQuadraticShellModelPhaseB (8 * q + 7))
        ((2 : ℤ) ^ (8 * q + 10)) (((8 * q + 8 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 7) + 1 = 8 * q + 8 by omega, show (8 * q + 7) + 3 = 8 * q + 10 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 7) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_eight q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 8) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 8) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- Recursive integer shell count equals the all-residue closed target in the
`nine` residue family. -/
theorem identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_nine
    (q : ℕ) (r : ZMod 8) :
    identityQuadraticShellModEightCountInt (8 * q + 9) r =
      identityQuadraticShellModEightCountClosedInt (8 * q + 9) r := by
  have hmodel : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 9) r =
      identityQuadraticShellModel ((2 : ℤ) ^ (2 * (8 * q + 9)))
        (identityQuadraticShellModelPhaseA (8 * q + 8))
        (identityQuadraticShellModelPhaseB (8 * q + 8))
        ((2 : ℤ) ^ (8 * q + 11)) (((8 * q + 9 : ℕ) : ZMod 8)) r := by
    simpa [show (8 * q + 8) + 1 = 8 * q + 9 by omega, show (8 * q + 8) + 3 = 8 * q + 11 by omega] using
      identityQuadraticShellModEightCountInt_succ_eq_model_pow (8 * q + 8) r
  have hclosed := identityQuadraticShellModel_pow_eq_scaled_closedInt_eight_mul_add_nine q r
  have h : (8 : ℤ) * identityQuadraticShellModEightCountInt (8 * q + 9) r =
      8 * identityQuadraticShellModEightCountClosedInt (8 * q + 9) r := hmodel.trans hclosed
  exact mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) h

/-- The all-residue closed target recovers the residue-one target in rank
three, the first rank beyond the signed-permutation range. -/
theorem identityQuadraticShellModEightCountClosedInt_three_one :
    identityQuadraticShellModEightCountClosedInt 3 1 =
      (identityQuadraticUnitVectorsModFourCountClosed 3 : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_three (by norm_num)]
  have h13 : (1 : ZMod 8) ≠ 3 := by decide
  have h13m4 : (1 : ZMod 8) ≠ 3 - 4 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, h13, h13m4]

/-- The all-residue closed target recovers the existing residue-one target in
the first rank where the characteristic all-odd branch contributes. -/
theorem identityQuadraticShellModEightCountClosedInt_nine_one :
    identityQuadraticShellModEightCountClosedInt 9 1 =
      (identityQuadraticUnitVectorsModFourCountClosed 9 : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_one (by norm_num)]
  have h19 : (1 : ZMod 8) = 9 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, h19]

/-- The all-residue closed target recovers the existing residue-one target in
ranks `3 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_three_one
    {m : ℕ} (hm : m % 8 = 3) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_three hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 3 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 3) (by simpa using hm)
  have hexp : (3 * m - 5) / 2 = 2 * m - 3 - (m - 1) / 2 := by omega
  have h13 : (1 : ZMod 8) ≠ 3 := by decide
  have h13m4 : (1 : ZMod 8) ≠ 3 - 4 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hexp, h13, h13m4]

/-- The all-residue closed target recovers the existing residue-one target in
ranks `6 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_six_one
    {m : ℕ} (hm : m % 8 = 6) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_six hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 6 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 6) (by simpa using hm)
  have hexp : 3 * (m / 2) - 2 = 2 * m - 3 - (m / 2 - 1) := by omega
  let a : ℕ := 2 * m - 3
  let b : ℕ := 2 * m - 3 - (m / 2 - 1)
  have hb_le_a : b ≤ a := by dsimp [a, b]; omega
  have hpowle : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hb_le_a
  rw [Nat.cast_sub hpowle]
  have h16 : (1 : ZMod 8) ≠ 6 := by decide
  have h16m4 : (1 : ZMod 8) ≠ 6 - 4 := by decide
  have hnot37 : ¬((1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 7) := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hexp, h16, h16m4,
    hnot37, a, b]
  ring


/-- The all-residue closed target recovers the existing residue-one target in
ranks `0 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_zero_one
    {m : ℕ} (hm : m % 8 = 0) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  have hm4 : m % 4 = 0 := by omega
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero hm4]
  have hmcast : ((m : ℕ) : ZMod 8) = 0 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 0) (by simpa using hm)
  have h10 : (1 : ZMod 8) ≠ 0 := by decide
  have h14 : (1 : ZMod 8) ≠ 4 := by decide
  have h12 : (1 : ZMod 8) ≠ 2 := by decide
  have h16 : (1 : ZMod 8) ≠ 6 := by decide
  have h1neg4 : (1 : ZMod 8) ≠ -4 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, h10, h14, h12, h16, h1neg4]

/-- The all-residue closed target recovers the existing residue-one target in
ranks `1 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_one_one
    {m : ℕ} (hm : m % 8 = 1) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_one hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 1 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 1) (by simpa using hm)
  have hexp : (3 * m - 5) / 2 = (m - 3) / 2 + (m - 1) := by omega
  have hpow : ((2 : ℤ) ^ ((3 * m - 5) / 2)) =
      (2 : ℤ) ^ ((m - 3) / 2) * (2 : ℤ) ^ (m - 1) := by
    rw [hexp, pow_add]
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hpow]
  ring

/-- The all-residue closed target recovers the existing residue-one target in
ranks `2 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_two_one
    {m : ℕ} (hm : m % 8 = 2) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_two hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 2 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 2) (by simpa using hm)
  have hexp : 3 * (m / 2) - 2 = 2 * m - 3 - (m / 2 - 1) := by omega
  have h12 : (1 : ZMod 8) ≠ 2 := by decide
  have h12m4 : (1 : ZMod 8) ≠ 2 - 4 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hexp, h12, h12m4]

/-- The all-residue closed target recovers the existing residue-one target in
ranks `4 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_four_one
    {m : ℕ} (hm : m % 8 = 4) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  have hm4 : m % 4 = 0 := by omega
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero hm4]
  have hmcast : ((m : ℕ) : ZMod 8) = 4 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 4) (by simpa using hm)
  have h10 : (1 : ZMod 8) ≠ 0 := by decide
  have h12 : (1 : ZMod 8) ≠ 2 := by decide
  have h14 : (1 : ZMod 8) ≠ 4 := by decide
  have h16 : (1 : ZMod 8) ≠ 6 := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, h10, h12, h14, h16]

/-- The all-residue closed target recovers the existing residue-one target in
ranks `5 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_five_one
    {m : ℕ} (hm : m % 8 = 5) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_five hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 5 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 5) (by simpa using hm)
  have hexp : (3 * m - 5) / 2 = (m - 3) / 2 + (m - 1) := by omega
  have hpow : ((2 : ℤ) ^ ((3 * m - 5) / 2)) =
      (2 : ℤ) ^ ((m - 3) / 2) * (2 : ℤ) ^ (m - 1) := by
    rw [hexp, pow_add]
  let a : ℕ := 2 * m - 3
  let c : ℕ := (m - 3) / 2
  let p : ℕ := m - 1
  let subtrahend : ℕ := (2 ^ c + 1) * 2 ^ p
  have hsum_le : 2 ^ c + 1 ≤ 2 ^ (c + 1) := by
    have hpow_pos : 1 ≤ 2 ^ c := Nat.one_le_pow c 2 (by norm_num)
    have hdouble : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := by
      rw [pow_succ]
      ring
    rw [← hdouble]
    omega
  have hsub_le_pow : subtrahend ≤ 2 ^ (c + 1) * 2 ^ p := by
    dsimp [subtrahend]
    exact Nat.mul_le_mul_right _ hsum_le
  have hpow_mul : 2 ^ (c + 1) * 2 ^ p = 2 ^ (c + 1 + p) := by
    rw [← pow_add]
  have hcp_le_a : c + 1 + p ≤ a := by dsimp [a, c, p]; omega
  have hpow_le : 2 ^ (c + 1 + p) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hcp_le_a
  have hle : subtrahend ≤ 2 ^ a := by
    calc
      subtrahend ≤ 2 ^ (c + 1) * 2 ^ p := hsub_le_pow
      _ = 2 ^ (c + 1 + p) := hpow_mul
      _ ≤ 2 ^ a := hpow_le
  rw [Nat.cast_sub hle]
  have h15m4 : (1 : ZMod 8) = 5 - 4 := by decide
  have hnot5m4 : ¬((5 : ZMod 8) - 4 = 2 ∨ (5 : ZMod 8) - 4 = 3 ∨
      (5 : ZMod 8) - 4 = 6 ∨ (5 : ZMod 8) - 4 = 7) := by decide
  have h40 : ¬((4 : ZMod 8) = 0) := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hpow, h15m4, h40, hnot5m4,
    a, c, p, subtrahend]
  ring

/-- The all-residue closed target recovers the existing residue-one target in
ranks `7 mod 8`. -/
theorem identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_seven_one
    {m : ℕ} (hm : m % 8 = 7) :
    identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
  rw [identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_seven hm]
  have hmcast : ((m : ℕ) : ZMod 8) = 7 := by
    exact natCast_zmod_eight_eq_of_mod_eq (m := m) (a := 7) (by simpa using hm)
  have hexp : (3 * m - 5) / 2 = 2 * m - 3 - (m - 1) / 2 := by omega
  let a : ℕ := 2 * m - 3
  let b : ℕ := 2 * m - 3 - (m - 1) / 2
  have hb_le_a : b ≤ a := by dsimp [a, b]; omega
  have hpowle : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hb_le_a
  rw [Nat.cast_sub hpowle]
  have h17 : (1 : ZMod 8) ≠ 7 := by decide
  have h17m4 : (1 : ZMod 8) ≠ 7 - 4 := by decide
  have hnot034 : ¬((1 : ZMod 8) = 0 ∨ (1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 4) := by decide
  simp [identityQuadraticShellModEightCountClosedInt,
    identityQuadraticShellModEightEvenCorrectionClosed,
    identityQuadraticShellModEightOddCharacterClosed, hm, hmcast, hexp, h17, h17m4, hnot034, a, b]
  ring

/-- Extract the existing natural residue-one shell target from the integer
all-residue target.  This is the interface that will consume the future proof
that the recursive shell count equals `identityQuadraticShellModEightCountClosedInt`
in every residue. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    {m : ℕ}
    (hclosed : (identityQuadraticShellModEightCount m 1 : ℤ) =
      identityQuadraticShellModEightCountClosedInt m 1)
    (hcompat : identityQuadraticShellModEightCountClosedInt m 1 =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ)) :
    identityQuadraticShellModEightCount m 1 =
      identityQuadraticUnitVectorsModFourCountClosed m := by
  have h : (identityQuadraticShellModEightCount m 1 : ℤ) =
      (identityQuadraticUnitVectorsModFourCountClosed m : ℤ) := by
    rw [hclosed, hcompat]
  exact_mod_cast h


/-- Residue-one total shell count equals the existing natural closed target in the
`two` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_two
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 2) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 2) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_two q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_two_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`three` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_three
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 3) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 3) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_three q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_three_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`four` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_four
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 4) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 4) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_four q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_four_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`five` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_five
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 5) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 5) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_five q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_five_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`six` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_six
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 6) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 6) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_six q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_six_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`seven` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_seven
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 7) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 7) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_seven q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_seven_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`eight` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_eight
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 8) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 8) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_eight q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_zero_one (by omega))

/-- Residue-one total shell count equals the existing natural closed target in the
`nine` positive-rank family. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_nine
    (q : ℕ) :
    identityQuadraticShellModEightCount (8 * q + 9) 1 =
      identityQuadraticUnitVectorsModFourCountClosed (8 * q + 9) := by
  exact identityQuadraticShellModEightCount_one_eq_closed_of_closedInt
    (by
      simpa [identityQuadraticShellModEightCountInt] using
        identityQuadraticShellModEightCountInt_eq_closedInt_eight_mul_add_nine q (1 : ZMod 8))
    (identityQuadraticShellModEightCountClosedInt_of_mod_eight_eq_one_one (by omega))

/-- Rational closed-count target for the ordinary norm-one Type I columns.
This is the closed step candidate multiplied by the normalizing power removed in
`identityQuadraticTypeILocalFactorStep`.  Proving the recursive ordinary-column
count equals this rational target is equivalent to the closed step formula. -/
def identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ (m : ℕ) : ℚ :=
  identityQuadraticTypeILocalFactorStepClosed m * ((2 : ℚ) ^ (2 * m - 3))

/-- Closed ordinary-column rational target in ranks divisible by four. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_four_eq_zero
    {m : ℕ} (hm : m % 4 = 0) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (2 : ℚ) ^ (2 * m - 3) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_four_eq_zero hm]
  ring

/-- Closed ordinary-column rational target in ranks `2 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_two
    {m : ℕ} (hm : m % 8 = 2) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 + ((2 : ℚ) ^ (m / 2 - 1))⁻¹) * ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_two hm]

/-- Closed ordinary-column rational target in ranks `6 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_six
    {m : ℕ} (hm : m % 8 = 6) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 - ((2 : ℚ) ^ (m / 2 - 1))⁻¹) * ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_six hm]

/-- Closed ordinary-column rational target in ranks `3 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 + ((2 : ℚ) ^ ((m - 1) / 2))⁻¹) * ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_three hm]

/-- Closed ordinary-column rational target in ranks `7 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 - ((2 : ℚ) ^ ((m - 1) / 2))⁻¹) * ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_seven hm]

/-- Closed ordinary-column rational target in ranks `1 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_one
    {m : ℕ} (hm : m % 8 = 1) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 + (((2 : ℚ) ^ ((m - 3) / 2) - 1) * ((2 : ℚ) ^ (m - 2))⁻¹)) *
        ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_one hm]

/-- Closed ordinary-column rational target in ranks `5 mod 8`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_five
    {m : ℕ} (hm : m % 8 = 5) :
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m =
      (1 - (((2 : ℚ) ^ ((m - 3) / 2) + 1) * ((2 : ℚ) ^ (m - 2))⁻¹)) *
        ((2 : ℚ) ^ (2 * m - 3)) := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ,
    identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_five hm]

/-- In ranks divisible by four, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_four_eq_zero
    {m : ℕ} (hm : m % 4 = 0) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_four_eq_zero hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_four_eq_zero hm]
  norm_num

/-- In ranks `2 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_two
    {m : ℕ} (hm : m % 8 = 2) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_two hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_two hm]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have hle : m / 2 - 1 ≤ 2 * m - 3 := by omega
  rw [pow_sub₀ (2 : ℚ) (by norm_num) hle]
  ring

/-- In ranks `3 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_three hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_three hm]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have hle : (m - 1) / 2 ≤ 2 * m - 3 := by omega
  rw [pow_sub₀ (2 : ℚ) (by norm_num) hle]
  ring

/-- In ranks `6 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_six
    {m : ℕ} (hm : m % 8 = 6) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_six hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_six hm]
  let e : ℕ := m / 2 - 1
  have hle : e ≤ 2 * m - 3 := by dsimp [e]; omega
  have hpowle : 2 ^ (2 * m - 3 - e) ≤ 2 ^ (2 * m - 3) := by
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.sub_le _ _)
  rw [Nat.cast_sub hpowle]
  have hpow : ((2 ^ (2 * m - 3 - e) : ℕ) : ℚ) =
      (2 : ℚ) ^ (2 * m - 3) * ((2 : ℚ) ^ e)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ (2 : ℚ) (by norm_num) hle]
  rw [hpow]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  dsimp [e]
  ring_nf

/-- In ranks `7 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_seven hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_seven hm]
  let e : ℕ := (m - 1) / 2
  have hle : e ≤ 2 * m - 3 := by dsimp [e]; omega
  have hpowle : 2 ^ (2 * m - 3 - e) ≤ 2 ^ (2 * m - 3) := by
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.sub_le _ _)
  rw [Nat.cast_sub hpowle]
  have hpow : ((2 ^ (2 * m - 3 - e) : ℕ) : ℚ) =
      (2 : ℚ) ^ (2 * m - 3) * ((2 : ℚ) ^ e)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ (2 : ℚ) (by norm_num) hle]
  rw [hpow]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  dsimp [e]
  ring_nf

/-- In ranks `1 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_one
    {m : ℕ} (hm : m % 8 = 1) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_one hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_one hm]
  have hsub : 1 ≤ 2 ^ ((m - 3) / 2) :=
    Nat.one_le_pow ((m - 3) / 2) 2 (by norm_num)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsub]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hsplit : 2 * m - 3 = (m - 2) + (m - 1) := by omega
  rw [hsplit, pow_add]
  field_simp [pow_ne_zero]

/-- In ranks `5 mod 8`, the natural closed target casts to the rational
closed ordinary-column target. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_five
    {m : ℕ} (hm : m % 8 = 5) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCountClosed_of_mod_eight_eq_five hm,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ_of_mod_eight_eq_five hm]
  let e : ℕ := (m - 3) / 2
  have hle_exp : e + (m - 1) + 1 ≤ 2 * m - 3 := by dsimp [e]; omega
  have hsmall : m - 1 ≤ e + (m - 1) := by omega
  have hterm2 : 2 ^ (m - 1) ≤ 2 ^ (e + (m - 1)) := by
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hsmall
  have hsum_le_double : 2 ^ (e + (m - 1)) + 2 ^ (m - 1) ≤
      2 ^ (e + (m - 1)) + 2 ^ (e + (m - 1)) := by
    exact Nat.add_le_add_left hterm2 _
  have hdouble : 2 ^ (e + (m - 1)) + 2 ^ (e + (m - 1)) =
      2 ^ (e + (m - 1) + 1) := by
    rw [← two_mul, ← pow_succ']
  have hpowle_sum : 2 ^ (e + (m - 1)) + 2 ^ (m - 1) ≤ 2 ^ (2 * m - 3) := by
    calc
      2 ^ (e + (m - 1)) + 2 ^ (m - 1) ≤
          2 ^ (e + (m - 1)) + 2 ^ (e + (m - 1)) := hsum_le_double
      _ = 2 ^ (e + (m - 1) + 1) := hdouble
      _ ≤ 2 ^ (2 * m - 3) := by
          exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle_exp
  have hmul : (2 ^ e + 1) * 2 ^ (m - 1) =
      2 ^ (e + (m - 1)) + 2 ^ (m - 1) := by
    rw [add_mul, one_mul, ← pow_add]
  have hsuble : (2 ^ e + 1) * 2 ^ (m - 1) ≤ 2 ^ (2 * m - 3) := by
    rw [hmul]
    exact hpowle_sum
  rw [Nat.cast_sub hsuble]
  rw [Nat.cast_mul, Nat.cast_add]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hsplit : 2 * m - 3 = (m - 2) + (m - 1) := by omega
  rw [hsplit, pow_add]
  dsimp [e]
  field_simp [pow_ne_zero]

/-- The natural closed ordinary-column target casts to the rational closed target
in every rank.  This packages the residue-class cast lemmas into the interface
needed to reduce the Type I closed step formula to a pure natural-number count. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ (m : ℕ) :
    ((identityQuadraticOrdinaryUnitVectorsModFourCountClosed m : ℕ) : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  have hmod : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨
      m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have h4zero : m % 4 = 0 := by omega
    exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_four_eq_zero h4zero
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_one h1
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_two h2
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_three h3
  · have h4zero : m % 4 = 0 := by omega
    exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_four_eq_zero h4zero
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_five h5
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_six h6
  · exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ_of_mod_eight_eq_seven h7

/-- The closed step formula follows from the corresponding rational ordinary-column
count formula. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closedQ
    {m : ℕ}
    (hcount : (identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m) :
    identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m := by
  rw [identityQuadraticTypeILocalFactorStep, hcount,
    identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ]
  field_simp [pow_ne_zero]

/-- Conversely, the closed step formula is exactly the rational ordinary-column
count formula after multiplying back by the normalizing power. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closedQ_of_step_eq_closed
    {m : ℕ}
    (hstep : identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m) :
    (identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  let d : ℚ := (2 : ℚ) ^ (2 * m - 3)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
  have hmul := congrArg (fun x : ℚ => x * d) hstep
  change ((identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) * d⁻¹) * d =
      identityQuadraticTypeILocalFactorStepClosed m * d at hmul
  calc
    (identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) =
        ((identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) * d⁻¹) * d := by
          field_simp [hd]
    _ = identityQuadraticTypeILocalFactorStepClosed m * d := hmul
    _ = identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
          simp [identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ, d]

/-- The closed step formula is equivalent to the rational ordinary-column count
formula. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_iff_ordinaryCount_eq_closedQ
    (m : ℕ) :
    identityQuadraticTypeILocalFactorStep m =
        identityQuadraticTypeILocalFactorStepClosed m ↔
      (identityQuadraticOrdinaryUnitVectorsModFourCount m : ℚ) =
        identityQuadraticOrdinaryUnitVectorsModFourCountClosedQ m := by
  constructor
  · exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closedQ_of_step_eq_closed
  · exact identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closedQ

/-- The closed step formula follows from the corresponding natural-number
ordinary-column count formula. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closed
    {m : ℕ}
    (hcount : identityQuadraticOrdinaryUnitVectorsModFourCount m =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed m) :
    identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m := by
  apply identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closedQ
  rw [hcount]
  exact identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ m

/-- The closed Type I step formula is equivalent to the natural-number closed
ordinary-column count formula. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_iff_ordinaryCount_eq_closed
    {m : ℕ} :
    identityQuadraticTypeILocalFactorStep m =
        identityQuadraticTypeILocalFactorStepClosed m ↔
      identityQuadraticOrdinaryUnitVectorsModFourCount m =
        identityQuadraticOrdinaryUnitVectorsModFourCountClosed m := by
  constructor
  · intro hstep
    have hq :=
      (identityQuadraticTypeILocalFactorStep_eq_closed_iff_ordinaryCount_eq_closedQ
        (m := m)).mp hstep
    rw [← identityQuadraticOrdinaryUnitVectorsModFourCountClosed_cast_eq_closedQ m] at hq
    exact_mod_cast hq
  · intro hcount
    exact identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closed hcount


/-- A closed formula for the total norm-one shell count implies the closed formula
for ordinary norm-one columns, because ordinary columns subtract exactly the
characteristic all-odd contribution. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    {m : ℕ}
    (hshell : identityQuadraticShellModEightCount m 1 =
      identityQuadraticUnitVectorsModFourCountClosed m) :
    identityQuadraticOrdinaryUnitVectorsModFourCount m =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed m := by
  rw [identityQuadraticOrdinaryUnitVectorsModFourCount, hshell,
    identityQuadraticUnitVectorsModFourCountClosed]
  by_cases hm : ((m : ℕ) : ZMod 8) = 1
  · simp [hm]
  · simp [hm]

/-- A closed formula for the total norm-one shell count is enough to prove the
closed Type I normalized step formula. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    {m : ℕ}
    (hshell : identityQuadraticShellModEightCount m 1 =
      identityQuadraticUnitVectorsModFourCountClosed m) :
    identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_ordinaryCount_eq_closed
    (identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed hshell)

/-- Closed ordinary-column count in the `two` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_two
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 2) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 2) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_two q)

/-- Closed normalized Type I step factor in the `two` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_two
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 2) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 2) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_two q)

/-- Closed ordinary-column count in the `three` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_three
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 3) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 3) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_three q)

/-- Closed normalized Type I step factor in the `three` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_three
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 3) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 3) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_three q)

/-- Closed ordinary-column count in the `four` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_four
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 4) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 4) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_four q)

/-- Closed normalized Type I step factor in the `four` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_four
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 4) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 4) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_four q)

/-- Closed ordinary-column count in the `five` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_five
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 5) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 5) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_five q)

/-- Closed normalized Type I step factor in the `five` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_five
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 5) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 5) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_five q)

/-- Closed ordinary-column count in the `six` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_six
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 6) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 6) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_six q)

/-- Closed normalized Type I step factor in the `six` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_six
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 6) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 6) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_six q)

/-- Closed ordinary-column count in the `seven` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_seven
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 7) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 7) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_seven q)

/-- Closed normalized Type I step factor in the `seven` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_seven
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 7) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 7) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_seven q)

/-- Closed ordinary-column count in the `eight` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_eight
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 8) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 8) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_eight q)

/-- Closed normalized Type I step factor in the `eight` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_eight
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 8) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 8) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_eight q)

/-- Closed ordinary-column count in the `nine` positive-rank family. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_eight_mul_add_nine
    (q : ℕ) :
    identityQuadraticOrdinaryUnitVectorsModFourCount (8 * q + 9) =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed (8 * q + 9) := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_nine q)

/-- Closed normalized Type I step factor in the `nine` positive-rank family. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_eight_mul_add_nine
    (q : ℕ) :
    identityQuadraticTypeILocalFactorStep (8 * q + 9) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 9) := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_nine q)


/-- The residue-one total shell count agrees with the closed target in every rank
`m ≥ 2`.  The proof packages the eight positive-rank residue-family branches. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_of_two_le
    {m : ℕ} (hm : 2 ≤ m) :
    identityQuadraticShellModEightCount m 1 =
      identityQuadraticUnitVectorsModFourCountClosed m := by
  have hmod : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨
      m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hdecomp : m = 8 * (m / 8 - 1) + 8 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_eight (m / 8 - 1)
  · have hdecomp : m = 8 * (m / 8 - 1) + 9 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_nine (m / 8 - 1)
  · have hdecomp : m = 8 * (m / 8) + 2 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_two (m / 8)
  · have hdecomp : m = 8 * (m / 8) + 3 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_three (m / 8)
  · have hdecomp : m = 8 * (m / 8) + 4 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_four (m / 8)
  · have hdecomp : m = 8 * (m / 8) + 5 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_five (m / 8)
  · have hdecomp : m = 8 * (m / 8) + 6 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_six (m / 8)
  · have hdecomp : m = 8 * (m / 8) + 7 := by omega
    rw [hdecomp]
    exact identityQuadraticShellModEightCount_one_eq_closed_eight_mul_add_seven (m / 8)

/-- The ordinary norm-one Type I column count agrees with its closed target in
every rank `m ≥ 2`. -/
theorem identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_two_le
    {m : ℕ} (hm : 2 ≤ m) :
    identityQuadraticOrdinaryUnitVectorsModFourCount m =
      identityQuadraticOrdinaryUnitVectorsModFourCountClosed m := by
  exact identityQuadraticOrdinaryUnitVectorsModFourCount_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_of_two_le hm)

/-- The normalized Type I identity-lattice local-factor step agrees with the
closed residue-class formula in every rank `m ≥ 2`. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_of_two_le
    {m : ℕ} (hm : 2 ≤ m) :
    identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m := by
  exact identityQuadraticTypeILocalFactorStep_eq_closed_of_shellCount_eq_closed
    (identityQuadraticShellModEightCount_one_eq_closed_of_two_le hm)

set_option maxHeartbeats 1000000 in
/-- The recursive total norm-one shell count agrees with the closed shell target
for the checked Type I sample range.  Unlike the downstream step samples, this
is stated before applying the local-factor normalization. -/
theorem identityQuadraticShellModEightCount_one_eq_closed_of_three_le_of_le_sixteen
    {m : ℕ} (hlo : 3 ≤ m) (hhi : m ≤ 16) :
    identityQuadraticShellModEightCount m 1 =
      identityQuadraticUnitVectorsModFourCountClosed m := by
  interval_cases m
  · have hshell : identityQuadraticShellModEightCount 3 1 = 12 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_three (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 4 1 = 32 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 5 1 = 80 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_five (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 6 1 = 384 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_six (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 7 1 = 1792 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_seven (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 8 1 = 8192 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 9 1 = 35072 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_one (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 10 1 = 139264 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_two (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 11 1 = 540672 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_three (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 12 1 = 2097152 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 13 1 = 8253440 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_five (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 14 1 = 33030144 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_six (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 15 1 = 133169152 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_eight_eq_seven (by norm_num)]
    norm_num
  · have hshell : identityQuadraticShellModEightCount 16 1 = 536870912 := by decide
    rw [hshell, identityQuadraticUnitVectorsModFourCountClosed_of_mod_four_eq_zero (by norm_num)]
    norm_num

/-- Restatement of the normalized Type I identity local-factor recurrence using
`identityQuadraticTypeILocalFactorStep`. -/
theorem identityLattice_massLocalFactor_two_succ_eq_mul_step
    (n : ℕ) (hn : 1 ≤ n) :
    (identityLattice (n + 1)).massLocalFactor 2 =
      (identityLattice n).massLocalFactor 2 *
        ((identityQuadraticTypeILocalFactorStep (n + 1) : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount n hn]
  have hexp : 2 * (n + 1) - 3 = 2 * n - 1 := by omega
  simp [identityQuadraticTypeILocalFactorStep, hexp]

/-- The Type I identity-lattice local factor in rank three, obtained from the
recursive finite count. -/
theorem identityLattice_three_massLocalFactor_two_eq :
    (identityLattice 3).massLocalFactor 2 = 6 := by
  have hcount : identityQuadraticIsometryModFourCount 3 = 96 := by
    rw [← identityQuadraticIsometryModFour_natCard_eq_count,
      identityQuadraticIsometryModFour_natCard_three]
  rw [identityLattice_massLocalFactor_two_eq_isometryCount, hcount]
  norm_num [gramDetPadicValuationFactor]

/-- Finite-product solution of the normalized Type I identity local-factor
recurrence from the rank-three seed.  The remaining closed-form problem is
the residue-class simplification of the step factors
`identityQuadraticTypeILocalFactorStep m`. -/
theorem identityLattice_massLocalFactor_two_eq_three_mul_prod_steps
    (n : ℕ) (hn : 3 ≤ n) :
    (identityLattice n).massLocalFactor 2 =
      (6 : ℝ) * (((Finset.Icc 4 n).prod
        (fun m => identityQuadraticTypeILocalFactorStep m) : ℚ) : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [identityLattice_three_massLocalFactor_two_eq]
      simp
  | succ n hn ih =>
      rw [identityLattice_massLocalFactor_two_succ_eq_mul_step n (by omega)]
      rw [ih]
      rw [Finset.prod_Icc_succ_top (by omega : 4 ≤ n + 1)]
      norm_num [Rat.cast_mul]
      ring

/-- Finite-product solution of the Type I identity local factor with every
normalized step replaced by the closed residue-class formula.  This packages the
recursive finite count into the closed dyadic finite product without using the
global mass formula. -/
theorem identityLattice_massLocalFactor_two_eq_three_mul_prod_closed_steps
    (n : ℕ) (hn : 3 ≤ n) :
    (identityLattice n).massLocalFactor 2 =
      (6 : ℝ) * (((Finset.Icc 4 n).prod
        (fun m => identityQuadraticTypeILocalFactorStepClosed m) : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_eq_three_mul_prod_steps n hn]
  have hprod : (Finset.Icc 4 n).prod (fun m => identityQuadraticTypeILocalFactorStep m) =
      (Finset.Icc 4 n).prod (fun m => identityQuadraticTypeILocalFactorStepClosed m) := by
    refine Finset.prod_congr rfl ?_
    intro m hm
    exact identityQuadraticTypeILocalFactorStep_eq_closed_of_two_le (by
      have hm4 : 4 ≤ m := (Finset.mem_Icc.mp hm).1
      omega)
  rw [hprod]

/-- Successive Type I identity-lattice dyadic local factors advance by the closed
residue-class step.  This is the ratio form of the closed finite-count result,
ready to compare with the explicit odd/even-rank GenusMass local-factor
candidates. -/
theorem identityLattice_massLocalFactor_two_succ_eq_mul_closed_step
    (n : ℕ) (hn : 1 ≤ n) :
    (identityLattice (n + 1)).massLocalFactor 2 =
      (identityLattice n).massLocalFactor 2 *
        ((identityQuadraticTypeILocalFactorStepClosed (n + 1) : ℚ) : ℝ) := by
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_step n hn]
  rw [identityQuadraticTypeILocalFactorStep_eq_closed_of_two_le (by omega : 2 ≤ n + 1)]

/-- A candidate closed formula for the Type I identity-lattice dyadic local factor
is equal to the native local factor once it has the rank-three seed and the same
closed-step ratio.  This avoids regrouping the full finite product when proving
the odd-rank and even-rank local-factor shapes used by `GenusMass.lean`. -/
theorem identityLattice_massLocalFactor_two_eq_of_same_closed_step
    (F : ℕ → ℝ)
    (hbase : F 3 = 6)
    (hstep : ∀ n : ℕ, 3 ≤ n →
      F (n + 1) = F n * ((identityQuadraticTypeILocalFactorStepClosed (n + 1) : ℚ) : ℝ))
    {n : ℕ} (hn : 3 ≤ n) :
    (identityLattice n).massLocalFactor 2 = F n := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [identityLattice_three_massLocalFactor_two_eq, hbase]
  | succ n hn ih =>
      rw [identityLattice_massLocalFactor_two_succ_eq_mul_closed_step n (by omega),
        ih, hstep n hn]

/-- Closed form of the Type I identity-lattice dyadic local factor, matching the
three local-factor RHS shapes used by `GenusMass.lean`.  The following branch
lemmas expose the odd-rank, even-rank odd-half, and even-rank even-half forms.
Its identification with the dyadic local factor is
`massLocalFactor_two_eq_typeIClosedForm` (`TypeIIdentityMass`). -/
def identityLatticeTypeILocalFactorClosedForm (n : ℕ) : ℝ :=
  if n % 2 = 1 then
    let r := n / 2
    ((4 : ℝ) * (2 : ℝ) ^ r *
      ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (r * (r - 1) / 2 + r) /
      (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ))
  else if (n / 2) % 2 = 1 then
    let m := n / 2
    ((4 : ℝ) *
      ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (m * (m - 1) / 2))
  else
    let m := n / 2
    ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
      ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (m * (m - 1) / 2) /
      (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ))

/-- The closed Type I local-factor formula has the rank-three seed. -/
theorem identityLatticeTypeILocalFactorClosedForm_three :
    identityLatticeTypeILocalFactorClosedForm 3 = 6 := by
  norm_num [identityLatticeTypeILocalFactorClosedForm, typeIOddRankSign]

/-- Odd-rank branch of the closed Type I local-factor formula. -/
theorem identityLatticeTypeILocalFactorClosedForm_oddRank (r : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (2 * r + 1) =
      ((4 : ℝ) * (2 : ℝ) ^ r *
        ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (r * (r - 1) / 2 + r) /
        (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ)) := by
  have hodd : (2 * r + 1) % 2 = 1 := by omega
  have hdiv : (2 * r + 1) / 2 = r := by omega
  simp [identityLatticeTypeILocalFactorClosedForm, hodd, hdiv]

/-- Even-rank, odd-half-rank branch of the closed Type I local-factor formula. -/
theorem identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf (k : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (2 * (2 * k + 1)) =
      ((4 : ℝ) *
        ((Finset.Icc 1 (2 * k + 1 - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) := by
  have hdiv : (2 * (2 * k + 1)) / 2 = 2 * k + 1 := by omega
  have hhalf : (2 * k + 1) % 2 = 1 := by omega
  simp [identityLatticeTypeILocalFactorClosedForm, hdiv, hhalf]

/-- Even-rank, even-half-rank branch of the closed Type I local-factor formula. -/
theorem identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf
    {m : ℕ} (hm : Even m) :
    identityLatticeTypeILocalFactorClosedForm (2 * m) =
      ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
        ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) /
        (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ)) := by
  have hdiv : (2 * m) / 2 = m := by omega
  have hhalf : m % 2 ≠ 1 := by
    rcases hm with ⟨a, rfl⟩
    omega
  simp [identityLatticeTypeILocalFactorClosedForm, hdiv, hhalf]

/-- Closed local-factor recurrence in the `3 mod 8` rank family.
Here the next closed step is `1`, and the odd-rank branch agrees with the
following even-rank even-half branch by exact product and exponent matching. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_three
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 4) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 3) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 4) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 2) = 8 * q + 4 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf
    (m := 4 * q + 2) ⟨2 * q + 1, by ring⟩]
  rw [← show 2 * (4 * q + 1) + 1 = 8 * q + 3 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 1)]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_four_eq_zero
    (by omega : (2 * (4 * q + 2)) % 4 = 0)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 1) + 1) = -1 := by
    rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_three]
    omega
  have hsignEven : typeIEvenRankSign (2 * (4 * q + 2)) = -1 := by
    rw [typeIEvenRankSign_eq_neg_one_of_mod_eight_eq_four]
    omega
  rw [hsignOdd, hsignEven]
  have hprod : (4 * q + 2 - 1) = 4 * q + 1 := by omega
  rw [hprod]
  have hpow_left : (4 * q + 2) * (4 * q + 1) / 2 =
      (2 * q + 1) * (4 * q + 1) := by
    have hmul : (4 * q + 2) * (4 * q + 1) =
        2 * ((2 * q + 1) * (4 * q + 1)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 1) * (4 * q + 1)) (by norm_num : 0 < 2)
  have hpow_right : (4 * q + 1) * (4 * q + 1 - 1) / 2 + (4 * q + 1) =
      (2 * q + 1) * (4 * q + 1) := by
    have hmul : (4 * q + 1) * (4 * q + 1 - 1) =
        2 * ((4 * q + 1) * (2 * q)) := by
      have hsub : 4 * q + 1 - 1 = 4 * q := by omega
      rw [hsub]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((4 * q + 1) * (2 * q)) (by norm_num : 0 < 2)]
    ring
  rw [hpow_left, hpow_right]
  norm_num

private lemma two_pow_div_sub_one_mul_one_sub_inv (r : ℕ) (hr : 0 < r) :
    ((2 : ℝ) ^ r / ((2 : ℝ) ^ r - 1)) * (1 - ((2 : ℝ) ^ r)⁻¹) = 1 := by
  have hpow_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hpow_ne : (2 : ℝ) ^ r ≠ 0 := ne_of_gt hpow_pos
  have hsub_ne : (2 : ℝ) ^ r - 1 ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ r := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.ne_of_gt hr)
    linarith
  field_simp [hpow_ne, hsub_ne]


private lemma two_pow_div_add_one_mul_one_add_inv (r : ℕ) :
    ((2 : ℝ) ^ r / ((2 : ℝ) ^ r + 1)) * (1 + ((2 : ℝ) ^ r)⁻¹) = 1 := by
  have hpow_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hpow_ne : (2 : ℝ) ^ r ≠ 0 := ne_of_gt hpow_pos
  have hadd_ne : (2 : ℝ) ^ r + 1 ≠ 0 := by positivity
  field_simp [hpow_ne, hadd_ne]


private lemma two_pow_mul_sq_sub_one_div_sub_one_div_four_pow_eq_one_add_inv
    (r : ℕ) (hr : 0 < r) :
    (((2 : ℝ) ^ r * ((2 : ℝ) ^ (2 * r) - 1) / ((2 : ℝ) ^ r - 1)) /
        ((4 : ℝ) ^ r)) = 1 + ((2 : ℝ) ^ r)⁻¹ := by
  have hpow_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hpow_ne : (2 : ℝ) ^ r ≠ 0 := ne_of_gt hpow_pos
  have hsub_ne : (2 : ℝ) ^ r - 1 ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.ne_of_gt hr)
    linarith
  have hpow_two_mul : (2 : ℝ) ^ (2 * r) = ((2 : ℝ) ^ r) ^ 2 := by
    rw [show 2 * r = r * 2 by omega, pow_mul]
  have hfour : (4 : ℝ) ^ r = ((2 : ℝ) ^ r) ^ 2 := by
    calc
      (4 : ℝ) ^ r = ((2 : ℝ) ^ 2) ^ r := by norm_num
      _ = (2 : ℝ) ^ (2 * r) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (r * 2) := by congr 1; omega
      _ = ((2 : ℝ) ^ r) ^ 2 := by rw [pow_mul]
  rw [hpow_two_mul, hfour]
  field_simp [hpow_ne, hsub_ne]
  ring


private lemma two_pow_mul_sq_sub_one_div_add_one_div_four_pow_eq_one_sub_inv
    (r : ℕ) :
    (((2 : ℝ) ^ r * ((2 : ℝ) ^ (2 * r) - 1) / ((2 : ℝ) ^ r + 1)) /
        ((4 : ℝ) ^ r)) = 1 - ((2 : ℝ) ^ r)⁻¹ := by
  have hpow_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hpow_ne : (2 : ℝ) ^ r ≠ 0 := ne_of_gt hpow_pos
  have hadd_ne : (2 : ℝ) ^ r + 1 ≠ 0 := by positivity
  have hpow_two_mul : (2 : ℝ) ^ (2 * r) = ((2 : ℝ) ^ r) ^ 2 := by
    rw [show 2 * r = r * 2 by omega, pow_mul]
  have hfour : (4 : ℝ) ^ r = ((2 : ℝ) ^ r) ^ 2 := by
    calc
      (4 : ℝ) ^ r = ((2 : ℝ) ^ 2) ^ r := by norm_num
      _ = (2 : ℝ) ^ (2 * r) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (r * 2) := by congr 1; omega
      _ = ((2 : ℝ) ^ r) ^ 2 := by rw [pow_mul]
  rw [hpow_two_mul, hfour]
  field_simp [hpow_ne, hadd_ne]
  ring



private lemma factor_five (E r : ℕ) (hr : 1 < r) (P : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ r * (P * ((2 : ℝ) ^ (2 * r) - 1)) /
        (4 : ℝ) ^ (E + r) / ((2 : ℝ) ^ r - 1)) =
      (((4 : ℝ) * (2 : ℝ) ^ (r - 1) * P / (4 : ℝ) ^ E /
          ((2 : ℝ) ^ (r - 1) - 1)) *
        (2 * (((2 : ℝ) ^ (2 * r) - 1) * ((2 : ℝ) ^ (r - 1) - 1) /
          ((2 : ℝ) ^ r - 1)) / ((4 : ℝ) ^ r))) := by
  have h4E : (4 : ℝ) ^ E ≠ 0 := by positivity
  have h4r : (4 : ℝ) ^ r ≠ 0 := by positivity
  have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
  have h2pred : (2 : ℝ) ^ (r - 1) ≠ 0 := by positivity
  have hsubr : (2 : ℝ) ^ r - 1 ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ r := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.ne_of_gt (by omega : 0 < r))
    linarith
  have hsubpred : (2 : ℝ) ^ (r - 1) - 1 ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ (r - 1) := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega)
    linarith
  have hpowr : (2 : ℝ) ^ r = (2 : ℝ) ^ (r - 1) * 2 := by
    calc
      (2 : ℝ) ^ r = (2 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_succ]
  have hpow3 : (2 : ℝ) ^ (r * 3) = (2 : ℝ) ^ (r * 2) * (2 : ℝ) ^ (r - 1) * 2 := by
    calc
      (2 : ℝ) ^ (r * 3) = (2 : ℝ) ^ (r * 2 + (r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r * 2 + (r - 1)) * 2 := by rw [pow_succ]
      _ = (2 : ℝ) ^ (r * 2) * (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_add]
  rw [pow_add]
  field_simp [h4E, h4r, h2r, h2pred, hsubr, hsubpred]
  rw [hpowr]
  ring

private lemma factor_one (E r : ℕ) (hr : 1 < r) (P : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ r * (P * ((2 : ℝ) ^ (2 * r) - 1)) /
        (4 : ℝ) ^ (E + r) / ((2 : ℝ) ^ r + 1)) =
      (((4 : ℝ) * (2 : ℝ) ^ (r - 1) * P / (4 : ℝ) ^ E /
          ((2 : ℝ) ^ (r - 1) + 1)) *
        (2 * (((2 : ℝ) ^ (2 * r) - 1) * ((2 : ℝ) ^ (r - 1) + 1) /
          ((2 : ℝ) ^ r + 1)) / ((4 : ℝ) ^ r))) := by
  have h4E : (4 : ℝ) ^ E ≠ 0 := by positivity
  have h4r : (4 : ℝ) ^ r ≠ 0 := by positivity
  have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
  have h2pred : (2 : ℝ) ^ (r - 1) ≠ 0 := by positivity
  have haddr : (2 : ℝ) ^ r + 1 ≠ 0 := by positivity
  have haddpred : (2 : ℝ) ^ (r - 1) + 1 ≠ 0 := by positivity
  have hpowr : (2 : ℝ) ^ r = (2 : ℝ) ^ (r - 1) * 2 := by
    calc
      (2 : ℝ) ^ r = (2 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_succ]
  have hpow3 : (2 : ℝ) ^ (r * 3) = (2 : ℝ) ^ (r * 2) * (2 : ℝ) ^ (r - 1) * 2 := by
    calc
      (2 : ℝ) ^ (r * 3) = (2 : ℝ) ^ (r * 2 + (r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r * 2 + (r - 1)) * 2 := by rw [pow_succ]
      _ = (2 : ℝ) ^ (r * 2) * (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_add]
  rw [pow_add]
  field_simp [h4E, h4r, h2r, h2pred, haddr, haddpred]
  rw [hpowr]
  ring


private lemma ratio_helper_five (r : ℕ) (hr : 0 < r) :
    (2 * (((2 : ℝ) ^ (2 * r) - 1) * ((2 : ℝ) ^ (r - 1) - 1) /
          ((2 : ℝ) ^ r - 1)) / ((4 : ℝ) ^ r)) =
      1 - (((2 : ℝ) ^ (r - 1) + 1) * ((2 : ℝ) ^ (2 * r - 1))⁻¹) := by
  have hsub_ne : (2 : ℝ) ^ r - 1 ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ r := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.ne_of_gt hr)
    linarith
  have hpred_ne : (2 : ℝ) ^ (r - 1) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) := by
    calc
      (4 : ℝ) ^ r = ((2 : ℝ) ^ 2) ^ r := by norm_num
      _ = (2 : ℝ) ^ (2 * r) := by rw [pow_mul]
  have hpow2r : (2 : ℝ) ^ (2 * r) = ((2 : ℝ) ^ r) ^ 2 := by
    rw [show 2 * r = r * 2 by omega, pow_mul]
  have hpowr : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    calc
      (2 : ℝ) ^ r = (2 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (r - 1) := by ring
  have hsub_pred_ne : 2 * (2 : ℝ) ^ (r - 1) - 1 ≠ 0 := by
    rw [← hpowr]
    exact hsub_ne
  have hpow2rpred : (2 : ℝ) ^ (2 * r - 1) = (2 : ℝ) ^ r * (2 : ℝ) ^ (r - 1) := by
    have h : 2 * r - 1 = r + (r - 1) := by omega
    rw [h, pow_add]
  rw [hfour, hpow2r]
  rw [show ((2 : ℝ) ^ r) ^ 2 - 1 = ((2 : ℝ) ^ r - 1) * ((2 : ℝ) ^ r + 1) by ring]
  rw [hpowr, hpow2rpred]
  field_simp [hpred_ne, hsub_pred_ne]
  rw [hpowr]
  ring

private lemma ratio_helper_one (r : ℕ) (hr : 0 < r) :
    (2 * (((2 : ℝ) ^ (2 * r) - 1) * ((2 : ℝ) ^ (r - 1) + 1) /
          ((2 : ℝ) ^ r + 1)) / ((4 : ℝ) ^ r)) =
      1 + (((2 : ℝ) ^ (r - 1) - 1) * ((2 : ℝ) ^ (2 * r - 1))⁻¹) := by
  have hpred_ne : (2 : ℝ) ^ (r - 1) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) := by
    calc
      (4 : ℝ) ^ r = ((2 : ℝ) ^ 2) ^ r := by norm_num
      _ = (2 : ℝ) ^ (2 * r) := by rw [pow_mul]
  have hpow2r : (2 : ℝ) ^ (2 * r) = ((2 : ℝ) ^ r) ^ 2 := by
    rw [show 2 * r = r * 2 by omega, pow_mul]
  have hpowr : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    calc
      (2 : ℝ) ^ r = (2 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (r - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (r - 1) := by ring
  have hadd_pred_ne : 2 * (2 : ℝ) ^ (r - 1) + 1 ≠ 0 := by positivity
  have hpow2rpred : (2 : ℝ) ^ (2 * r - 1) = (2 : ℝ) ^ r * (2 : ℝ) ^ (r - 1) := by
    have h : 2 * r - 1 = r + (r - 1) := by omega
    rw [h, pow_add]
  rw [hfour, hpow2r]
  rw [show ((2 : ℝ) ^ r) ^ 2 - 1 = ((2 : ℝ) ^ r - 1) * ((2 : ℝ) ^ r + 1) by ring]
  rw [hpowr, hpow2rpred]
  field_simp [hpred_ne, hadd_pred_ne]
  rw [hpowr]
  ring


/-- Closed local-factor recurrence in the `2 mod 8` rank family.
The next odd-rank product extends by one factor, and that factor cancels with
the `3 mod 8` closed step normalization. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_two
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 3) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 2) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 3) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 1) + 1 = 8 * q + 3 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 1)]
  rw [← show 2 * (2 * (2 * q) + 1) = 8 * q + 2 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf (2 * q)]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (4 * q + 1) + 1) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 3) by
    congr 1
    omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_three
    (by omega : (8 * q + 3) % 8 = 3)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 1) + 1) = -1 := by
    rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_three]
    omega
  rw [hsignOdd]
  have hprod_even : 2 * (2 * q) + 1 - 1 = 4 * q := by omega
  rw [hprod_even]
  have hprod_odd_pred : 4 * q + 1 - 1 = 4 * q := by omega
  have hpow_left : (4 * q + 1) * (4 * q + 1 - 1) / 2 + (4 * q + 1) =
      (2 * q + 1) * (4 * q + 1) := by
    have hmul : (4 * q + 1) * (4 * q + 1 - 1) =
        2 * ((4 * q + 1) * (2 * q)) := by
      rw [hprod_odd_pred]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((4 * q + 1) * (2 * q)) (by norm_num : 0 < 2)]
    ring
  have hpow_even : (2 * (2 * q) + 1) * (4 * q) / 2 =
      (2 * q) * (4 * q + 1) := by
    have hmul : (2 * (2 * q) + 1) * (4 * q) =
        2 * ((2 * q) * (4 * q + 1)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q) * (4 * q + 1)) (by norm_num : 0 < 2)
  rw [hpow_left, hpow_even]
  have hstepPow : (8 * q + 3 - 1) / 2 = 4 * q + 1 := by omega
  rw [hstepPow]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ 4 * q + 1)]
  simp only [Rat.cast_add, Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_neg]
  have hden_real : (2 : ℝ) ^ (4 * q + 1) + -1 =
      (2 : ℝ) ^ (4 * q + 1) - 1 := by ring
  rw [hden_real]
  rw [show
      (4 * 2 ^ (4 * q + 1) * ((∏ k ∈ Finset.Icc 1 (4 * q), (2 ^ (2 * k) - 1)) *
          (2 ^ (2 * (4 * q + 1)) - 1))) /
            4 ^ ((2 * q + 1) * (4 * q + 1)) / ((2 : ℝ) ^ (4 * q + 1) - 1) =
        ((4 * ∏ k ∈ Finset.Icc 1 (4 * q), (2 ^ (2 * k) - 1)) /
            4 ^ (2 * q * (4 * q + 1))) *
          ((((2 : ℝ) ^ (4 * q + 1) * ((2 : ℝ) ^ (2 * (4 * q + 1)) - 1) /
              ((2 : ℝ) ^ (4 * q + 1) - 1)) / ((4 : ℝ) ^ (4 * q + 1)))) by
    ring]
  rw [two_pow_mul_sq_sub_one_div_sub_one_div_four_pow_eq_one_add_inv
    (4 * q + 1) (by omega)]


/-- Closed local-factor recurrence in the `4 mod 8` rank family.
The even-half branch advances to the next odd-rank branch by the `5 mod 8`
closed step; the proof isolates the endpoint product extension as a ratio. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_four
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 5) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 4) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 5) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 2) + 1 = 8 * q + 5 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 2)]
  rw [← show 2 * (4 * q + 2) = 8 * q + 4 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf
    (m := 4 * q + 2) ⟨2 * q + 1, by ring⟩]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (4 * q + 2) + 1) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 5) by
    congr 1
    omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_five
    (by omega : (8 * q + 5) % 8 = 5)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 2) + 1) = -1 := by
    rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_five]
    omega
  have hsignEven : typeIEvenRankSign (2 * (4 * q + 2)) = -1 := by
    rw [typeIEvenRankSign_eq_neg_one_of_mod_eight_eq_four]
    omega
  rw [hsignOdd, hsignEven]
  have hprod_even : 4 * q + 2 - 1 = 4 * q + 1 := by omega
  rw [hprod_even]
  have hpow_left : (4 * q + 2) * (4 * q + 1) / 2 + (4 * q + 2) =
      (2 * q + 1) * (4 * q + 1) + (4 * q + 2) := by
    have hmul : (4 * q + 2) * (4 * q + 1) =
        2 * ((2 * q + 1) * (4 * q + 1)) := by ring
    rw [hmul]
    rw [Nat.mul_div_right ((2 * q + 1) * (4 * q + 1)) (by norm_num : 0 < 2)]
  have hpow_right : (4 * q + 2) * (4 * q + 1) / 2 =
      (2 * q + 1) * (4 * q + 1) := by
    have hmul : (4 * q + 2) * (4 * q + 1) =
        2 * ((2 * q + 1) * (4 * q + 1)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 1) * (4 * q + 1)) (by norm_num : 0 < 2)
  rw [hpow_left, hpow_right]
  have hstep1 : (8 * q + 5 - 3) / 2 = 4 * q + 1 := by omega
  have hstep2 : 8 * q + 5 - 2 = 2 * (4 * q + 2) - 1 := by omega
  rw [hstep1, hstep2]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ 4 * q + 2)]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_neg]
  have htop : 4 * q + 1 + 1 = 4 * q + 2 := by omega
  rw [htop]
  have hden_even : (2 : ℝ) ^ (4 * q + 1) + -1 = (2 : ℝ) ^ (4 * q + 1) - 1 := by ring
  have hden_odd : (2 : ℝ) ^ (4 * q + 2) + -1 = (2 : ℝ) ^ (4 * q + 2) - 1 := by ring
  rw [hden_even, hden_odd]
  rw [factor_five ((2 * q + 1) * (4 * q + 1)) (4 * q + 2) (by omega)
    (∏ x ∈ Finset.Icc 1 (4 * q + 1), (2 ^ (2 * x) - 1))]
  have hrpred : 4 * q + 2 - 1 = 4 * q + 1 := by omega
  rw [show
      (2 * (((2 : ℝ) ^ (2 * (4 * q + 2)) - 1) * ((2 : ℝ) ^ (4 * q + 2 - 1) - 1) /
            ((2 : ℝ) ^ (4 * q + 2) - 1)) / ((4 : ℝ) ^ (4 * q + 2))) =
        1 - (((2 : ℝ) ^ (4 * q + 2 - 1) + 1) * ((2 : ℝ) ^ (2 * (4 * q + 2) - 1))⁻¹) by
    exact ratio_helper_five (4 * q + 2) (by omega)]
  rw [hrpred]


/-- Closed local-factor recurrence in the positive `1 mod 8` rank family.
The odd sign denominator cancels against the `2 mod 8` closed step, leaving the
following even-rank odd-half branch with matching product and exponent. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_nine
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 10) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 9) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 10) : ℚ) : ℝ) := by
  rw [← show 2 * (2 * (2 * q + 2) + 1) = 8 * q + 10 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf (2 * q + 2)]
  rw [← show 2 * (4 * q + 4) + 1 = 8 * q + 9 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 4)]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (2 * (2 * q + 2) + 1)) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 10) by congr; omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_two
    (by omega : (8 * q + 10) % 8 = 2)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 4) + 1) = 1 := by
    rw [typeIOddRankSign_eq_one_of_mod_eight_eq_one]
    omega
  rw [hsignOdd]
  have hprod : 2 * (2 * q + 2) + 1 - 1 = 4 * q + 4 := by omega
  rw [hprod]
  have hstepPow : (8 * q + 10) / 2 - 1 = 4 * q + 4 := by omega
  rw [hstepPow]
  have hpow_left : (2 * (2 * q + 2) + 1) * (4 * q + 4) / 2 =
      (2 * q + 2) * (4 * q + 5) := by
    have hmul : (2 * (2 * q + 2) + 1) * (4 * q + 4) =
        2 * ((2 * q + 2) * (4 * q + 5)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 2) * (4 * q + 5)) (by norm_num : 0 < 2)
  have hpow_right : (4 * q + 4) * (4 * q + 4 - 1) / 2 + (4 * q + 4) =
      (2 * q + 2) * (4 * q + 5) := by
    have hmul : (4 * q + 4) * (4 * q + 4 - 1) =
        2 * ((2 * q + 2) * (4 * q + 3)) := by
      have hsub : 4 * q + 4 - 1 = 4 * q + 3 := by omega
      rw [hsub]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((2 * q + 2) * (4 * q + 3)) (by norm_num : 0 < 2)]
    ring
  rw [hpow_left, hpow_right]
  simp only [Rat.cast_add, Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
  rw [show
      (4 * 2 ^ (4 * q + 4) * ∏ j ∈ Finset.Icc 1 (4 * q + 4), (2 ^ (2 * j) - 1)) /
            4 ^ ((2 * q + 2) * (4 * q + 5)) / ((2 : ℝ) ^ (4 * q + 4) + 1) *
          (1 + ((2 : ℝ) ^ (4 * q + 4))⁻¹) =
        ((4 * ∏ j ∈ Finset.Icc 1 (4 * q + 4), (2 ^ (2 * j) - 1)) /
            4 ^ ((2 * q + 2) * (4 * q + 5))) *
          (((2 : ℝ) ^ (4 * q + 4) / ((2 : ℝ) ^ (4 * q + 4) + 1)) *
            (1 + ((2 : ℝ) ^ (4 * q + 4))⁻¹)) by
    ring]
  rw [two_pow_div_add_one_mul_one_add_inv (4 * q + 4)]
  ring


/-- Closed local-factor recurrence in the `5 mod 8` rank family.
The odd sign denominator cancels against the `6 mod 8` closed step, leaving the
following even-rank odd-half branch with matching product and exponent. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_five
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 6) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 5) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 6) : ℚ) : ℝ) := by
  rw [← show 2 * (2 * (2 * q + 1) + 1) = 8 * q + 6 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf (2 * q + 1)]
  rw [← show 2 * (4 * q + 2) + 1 = 8 * q + 5 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 2)]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (2 * (2 * q + 1) + 1)) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 6) by congr; omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_six
    (by omega : (8 * q + 6) % 8 = 6)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 2) + 1) = -1 := by
    rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_five]
    omega
  rw [hsignOdd]
  have hprod : 2 * (2 * q + 1) + 1 - 1 = 4 * q + 2 := by omega
  rw [hprod]
  have hstepPow : (8 * q + 6) / 2 - 1 = 4 * q + 2 := by omega
  rw [hstepPow]
  have hpow_left : (2 * (2 * q + 1) + 1) * (4 * q + 2) / 2 =
      (2 * q + 1) * (4 * q + 3) := by
    have hmul : (2 * (2 * q + 1) + 1) * (4 * q + 2) =
        2 * ((2 * q + 1) * (4 * q + 3)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 1) * (4 * q + 3)) (by norm_num : 0 < 2)
  have hpow_right : (4 * q + 2) * (4 * q + 2 - 1) / 2 + (4 * q + 2) =
      (2 * q + 1) * (4 * q + 3) := by
    have hmul : (4 * q + 2) * (4 * q + 2 - 1) =
        2 * ((2 * q + 1) * (4 * q + 1)) := by
      have hsub : 4 * q + 2 - 1 = 4 * q + 1 := by omega
      rw [hsub]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((2 * q + 1) * (4 * q + 1)) (by norm_num : 0 < 2)]
    ring
  rw [hpow_left, hpow_right]
  simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
  have hden_cast : ((↑((2 : ℚ) ^ (4 * q + 2) + -1) : ℝ)) = (2 : ℝ) ^ (4 * q + 2) - 1 := by
    norm_num
    ring
  rw [hden_cast]
  rw [show
      (4 * 2 ^ (4 * q + 2) * ∏ j ∈ Finset.Icc 1 (4 * q + 2), (2 ^ (2 * j) - 1)) /
            4 ^ ((2 * q + 1) * (4 * q + 3)) / ((2 : ℝ) ^ (4 * q + 2) - 1) *
          (1 - ((2 : ℝ) ^ (4 * q + 2))⁻¹) =
        ((4 * ∏ j ∈ Finset.Icc 1 (4 * q + 2), (2 ^ (2 * j) - 1)) /
            4 ^ ((2 * q + 1) * (4 * q + 3))) *
          (((2 : ℝ) ^ (4 * q + 2) / ((2 : ℝ) ^ (4 * q + 2) - 1)) *
            (1 - ((2 : ℝ) ^ (4 * q + 2))⁻¹)) by
    ring]
  rw [two_pow_div_sub_one_mul_one_sub_inv (4 * q + 2) (by omega)]
  ring


/-- Closed local-factor recurrence in the `6 mod 8` rank family.
The next odd-rank product extends by one factor, and that factor cancels with
the `7 mod 8` closed step normalization. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_six
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 7) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 6) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 7) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 3) + 1 = 8 * q + 7 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 3)]
  rw [← show 2 * (2 * (2 * q + 1) + 1) = 8 * q + 6 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf (2 * q + 1)]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (4 * q + 3) + 1) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 7) by
    congr 1
    omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_seven
    (by omega : (8 * q + 7) % 8 = 7)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 3) + 1) = 1 := by
    rw [typeIOddRankSign_eq_one_of_mod_eight_eq_seven]
    omega
  rw [hsignOdd]
  have hprod_even : 2 * (2 * q + 1) + 1 - 1 = 4 * q + 2 := by omega
  rw [hprod_even]
  have hprod_odd_pred : 4 * q + 3 - 1 = 4 * q + 2 := by omega
  have hpow_left : (4 * q + 3) * (4 * q + 3 - 1) / 2 + (4 * q + 3) =
      (2 * q + 2) * (4 * q + 3) := by
    have hmul : (4 * q + 3) * (4 * q + 3 - 1) =
        2 * ((4 * q + 3) * (2 * q + 1)) := by
      rw [hprod_odd_pred]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((4 * q + 3) * (2 * q + 1)) (by norm_num : 0 < 2)]
    ring
  have hpow_even : (2 * (2 * q + 1) + 1) * (4 * q + 2) / 2 =
      (2 * q + 1) * (4 * q + 3) := by
    have hmul : (2 * (2 * q + 1) + 1) * (4 * q + 2) =
        2 * ((2 * q + 1) * (4 * q + 3)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 1) * (4 * q + 3)) (by norm_num : 0 < 2)
  rw [hpow_left, hpow_even]
  have hstepPow : (8 * q + 7 - 1) / 2 = 4 * q + 3 := by omega
  rw [hstepPow]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ 4 * q + 3)]
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
  have htop : 4 * q + 2 + 1 = 4 * q + 3 := by omega
  rw [htop]
  rw [show
      (4 * 2 ^ (4 * q + 3) * ((∏ k ∈ Finset.Icc 1 (4 * q + 2), (2 ^ (2 * k) - 1)) *
          (2 ^ (2 * (4 * q + 3)) - 1))) /
            4 ^ ((2 * q + 2) * (4 * q + 3)) / ((2 : ℝ) ^ (4 * q + 3) + 1) =
        ((4 * ∏ k ∈ Finset.Icc 1 (4 * q + 2), (2 ^ (2 * k) - 1)) /
            4 ^ ((2 * q + 1) * (4 * q + 3))) *
          ((((2 : ℝ) ^ (4 * q + 3) * ((2 : ℝ) ^ (2 * (4 * q + 3)) - 1) /
              ((2 : ℝ) ^ (4 * q + 3) + 1)) / ((4 : ℝ) ^ (4 * q + 3)))) by
    ring]
  rw [two_pow_mul_sq_sub_one_div_add_one_div_four_pow_eq_one_sub_inv (4 * q + 3)]


/-- Closed local-factor recurrence in the `7 mod 8` rank family.
Here the next closed step is `1`, and the odd-rank branch agrees with the
following even-rank even-half branch by exact product and exponent matching. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_seven
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 8) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 7) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 8) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 4) = 8 * q + 8 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf
    (m := 4 * q + 4) ⟨2 * q + 2, by ring⟩]
  rw [← show 2 * (4 * q + 3) + 1 = 8 * q + 7 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 3)]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_four_eq_zero
    (by omega : (2 * (4 * q + 4)) % 4 = 0)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 3) + 1) = 1 := by
    rw [typeIOddRankSign_eq_one_of_mod_eight_eq_seven]
    omega
  have hsignEven : typeIEvenRankSign (2 * (4 * q + 4)) = 1 := by
    rw [typeIEvenRankSign_eq_one_of_mod_eight_eq_zero]
    omega
  rw [hsignOdd, hsignEven]
  have hprod : (4 * q + 4 - 1) = 4 * q + 3 := by omega
  rw [hprod]
  have hpow_left : (4 * q + 4) * (4 * q + 3) / 2 =
      (2 * q + 2) * (4 * q + 3) := by
    have hmul : (4 * q + 4) * (4 * q + 3) =
        2 * ((2 * q + 2) * (4 * q + 3)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 2) * (4 * q + 3)) (by norm_num : 0 < 2)
  have hpow_right : (4 * q + 3) * (4 * q + 3 - 1) / 2 + (4 * q + 3) =
      (2 * q + 2) * (4 * q + 3) := by
    have hmul : (4 * q + 3) * (4 * q + 3 - 1) =
        2 * ((4 * q + 3) * (2 * q + 1)) := by
      have hsub : 4 * q + 3 - 1 = 4 * q + 2 := by omega
      rw [hsub]
      ring
    rw [hmul]
    rw [Nat.mul_div_right ((4 * q + 3) * (2 * q + 1)) (by norm_num : 0 < 2)]
    ring
  rw [hpow_left, hpow_right]
  norm_num

/-- Closed local-factor recurrence in the positive `0 mod 8` rank family.
The even-half branch advances to the next odd-rank branch by the `1 mod 8`
closed step; this is the positive-rank `0 mod 8` residue case. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_eight
    (q : ℕ) :
    identityLatticeTypeILocalFactorClosedForm (8 * q + 9) =
      identityLatticeTypeILocalFactorClosedForm (8 * q + 8) *
        ((identityQuadraticTypeILocalFactorStepClosed (8 * q + 9) : ℚ) : ℝ) := by
  rw [← show 2 * (4 * q + 4) + 1 = 8 * q + 9 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_oddRank (4 * q + 4)]
  rw [← show 2 * (4 * q + 4) = 8 * q + 8 by omega]
  rw [identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf
    (m := 4 * q + 4) ⟨2 * q + 2, by ring⟩]
  rw [show identityQuadraticTypeILocalFactorStepClosed (2 * (4 * q + 4) + 1) =
      identityQuadraticTypeILocalFactorStepClosed (8 * q + 9) by
    congr 1
    omega]
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_one
    (by omega : (8 * q + 9) % 8 = 1)]
  have hsignOdd : typeIOddRankSign (2 * (4 * q + 4) + 1) = 1 := by
    rw [typeIOddRankSign_eq_one_of_mod_eight_eq_one]
    omega
  have hsignEven : typeIEvenRankSign (2 * (4 * q + 4)) = 1 := by
    rw [typeIEvenRankSign_eq_one_of_mod_eight_eq_zero]
    omega
  rw [hsignOdd, hsignEven]
  have hprod_even : 4 * q + 4 - 1 = 4 * q + 3 := by omega
  rw [hprod_even]
  have hpow_left : (4 * q + 4) * (4 * q + 3) / 2 + (4 * q + 4) =
      (2 * q + 2) * (4 * q + 3) + (4 * q + 4) := by
    have hmul : (4 * q + 4) * (4 * q + 3) =
        2 * ((2 * q + 2) * (4 * q + 3)) := by ring
    rw [hmul]
    rw [Nat.mul_div_right ((2 * q + 2) * (4 * q + 3)) (by norm_num : 0 < 2)]
  have hpow_right : (4 * q + 4) * (4 * q + 3) / 2 =
      (2 * q + 2) * (4 * q + 3) := by
    have hmul : (4 * q + 4) * (4 * q + 3) =
        2 * ((2 * q + 2) * (4 * q + 3)) := by ring
    rw [hmul]
    exact Nat.mul_div_right ((2 * q + 2) * (4 * q + 3)) (by norm_num : 0 < 2)
  rw [hpow_left, hpow_right]
  have hstep1 : (8 * q + 9 - 3) / 2 = 4 * q + 3 := by omega
  have hstep2 : 8 * q + 9 - 2 = 2 * (4 * q + 4) - 1 := by omega
  rw [hstep1, hstep2]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ 4 * q + 4)]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_ofNat]
  have htop : 4 * q + 3 + 1 = 4 * q + 4 := by omega
  rw [htop]
  rw [factor_one ((2 * q + 2) * (4 * q + 3)) (4 * q + 4) (by omega)
    (∏ x ∈ Finset.Icc 1 (4 * q + 3), (2 ^ (2 * x) - 1))]
  have hrpred : 4 * q + 4 - 1 = 4 * q + 3 := by omega
  rw [show
      (2 * (((2 : ℝ) ^ (2 * (4 * q + 4)) - 1) * ((2 : ℝ) ^ (4 * q + 4 - 1) + 1) /
            ((2 : ℝ) ^ (4 * q + 4) + 1)) / ((4 : ℝ) ^ (4 * q + 4))) =
        1 + (((2 : ℝ) ^ (4 * q + 4 - 1) - 1) * ((2 : ℝ) ^ (2 * (4 * q + 4) - 1))⁻¹) by
    exact ratio_helper_one (4 * q + 4) (by omega)]
  rw [hrpred]



/-- The closed Type I local-factor formula satisfies the closed-step recurrence
in every rank `n ≥ 3`.  This packages the eight residue-family recurrence
branches. -/
theorem identityLatticeTypeILocalFactorClosedForm_step_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    identityLatticeTypeILocalFactorClosedForm (n + 1) =
      identityLatticeTypeILocalFactorClosedForm n *
        ((identityQuadraticTypeILocalFactorStepClosed (n + 1) : ℚ) : ℝ) := by
  have hmod : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
      n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hdecomp : n = 8 * (n / 8 - 1) + 8 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_eight (n / 8 - 1)
  · have hdecomp : n = 8 * (n / 8 - 1) + 9 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_nine (n / 8 - 1)
  · have hdecomp : n = 8 * (n / 8) + 2 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_two (n / 8)
  · have hdecomp : n = 8 * (n / 8) + 3 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_three (n / 8)
  · have hdecomp : n = 8 * (n / 8) + 4 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_four (n / 8)
  · have hdecomp : n = 8 * (n / 8) + 5 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_five (n / 8)
  · have hdecomp : n = 8 * (n / 8) + 6 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_six (n / 8)
  · have hdecomp : n = 8 * (n / 8) + 7 := by omega
    rw [hdecomp]
    exact identityLatticeTypeILocalFactorClosedForm_step_eight_mul_add_seven (n / 8)

/-- The native Type I identity-lattice dyadic local factor is the global closed
form in every rank `n ≥ 3`. -/
theorem identityLattice_massLocalFactor_two_eq_typeIClosedForm
    {n : ℕ} (hn : 3 ≤ n) :
    (identityLattice n).massLocalFactor 2 =
      identityLatticeTypeILocalFactorClosedForm n := by
  exact identityLattice_massLocalFactor_two_eq_of_same_closed_step
    identityLatticeTypeILocalFactorClosedForm
    identityLatticeTypeILocalFactorClosedForm_three
    (fun n hn => identityLatticeTypeILocalFactorClosedForm_step_of_three_le hn) hn

/-- Odd-rank closed Type I identity-lattice dyadic local-factor formula. -/
theorem identityLattice_massLocalFactor_two_oddRank_closed
    (r : ℕ) (hr : 1 ≤ r) :
    (identityLattice (2 * r + 1)).massLocalFactor 2 =
      ((4 : ℝ) * (2 : ℝ) ^ r *
        ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (r * (r - 1) / 2 + r) /
        (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ)) := by
  rw [identityLattice_massLocalFactor_two_eq_typeIClosedForm (by omega : 3 ≤ 2 * r + 1)]
  exact identityLatticeTypeILocalFactorClosedForm_oddRank r

/-- Even-rank, odd-half-rank closed Type I identity-lattice dyadic local-factor
formula. -/
theorem identityLattice_massLocalFactor_two_evenRank_oddHalf_closed
    (k : ℕ) (hk : k ≠ 0) :
    (identityLattice (2 * (2 * k + 1))).massLocalFactor 2 =
      ((4 : ℝ) *
        ((Finset.Icc 1 (2 * k + 1 - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) := by
  rw [identityLattice_massLocalFactor_two_eq_typeIClosedForm
    (by omega : 3 ≤ 2 * (2 * k + 1))]
  exact identityLatticeTypeILocalFactorClosedForm_evenRank_oddHalf k

/-- Even-rank, even-half-rank closed Type I identity-lattice dyadic local-factor
formula. -/
theorem identityLattice_massLocalFactor_two_evenRank_evenHalf_closed
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) :
    (identityLattice (2 * m)).massLocalFactor 2 =
      ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
        ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) /
        (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ)) := by
  rw [identityLattice_massLocalFactor_two_eq_typeIClosedForm (by omega : 3 ≤ 2 * m)]
  exact identityLatticeTypeILocalFactorClosedForm_evenRank_evenHalf hm_even

/-- Rank four gives the next Type I identity-lattice dyadic local factor after
the recursive finite count is placed in the simplified normalization. -/
theorem identityLattice_four_massLocalFactor_two_eq :
    (identityLattice 4).massLocalFactor 2 = 6 := by
  have hcount : identityQuadraticIsometryModFourCount 4 = 3072 := by
    decide
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow 4
    (by norm_num), hcount]
  norm_num

/-- Rank five is the first odd Type I identity-lattice value whose simplified
local factor has a nontrivial rational denominator. -/
theorem identityLattice_five_massLocalFactor_two_eq :
    (identityLattice 5).massLocalFactor 2 = (15 / 4 : ℝ) := by
  have hcount : identityQuadraticIsometryModFourCount 5 = 245760 := by
    decide
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow 5
    (by norm_num), hcount]
  norm_num

/-- Rank six is the first even-rank, odd half-rank Type I identity-lattice
sample in the simplified local-factor normalization. -/
theorem identityLattice_six_massLocalFactor_two_eq :
    (identityLattice 6).massLocalFactor 2 = (45 / 16 : ℝ) := by
  have hcount : identityQuadraticIsometryModFourCount 6 = 94371840 := by
    decide
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow 6
    (by norm_num), hcount]
  norm_num

/-- Rank seven is the next odd-rank Type I identity-lattice local-factor
sample. -/
theorem identityLattice_seven_massLocalFactor_two_eq :
    (identityLattice 7).massLocalFactor 2 = (315 / 128 : ℝ) := by
  have hcount : identityQuadraticIsometryModFourCount 7 = 169114337280 := by
    decide
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow 7
    (by norm_num), hcount]
  norm_num

/-- Rank eight is the first even-rank, even half-rank Type I identity-lattice
sample in the simplified local-factor normalization. -/
theorem identityLattice_eight_massLocalFactor_two_eq :
    (identityLattice 8).massLocalFactor 2 = (315 / 128 : ℝ) := by
  have hcount : identityQuadraticIsometryModFourCount 8 = 1385384650997760 := by
    decide
  rw [identityLattice_massLocalFactor_two_eq_isometryCount_div_pow 8
    (by norm_num), hcount]
  norm_num

/-- Rank nine is the first checked Type I identity-lattice local factor where
the characteristic all-odd norm-one columns are subtracted in the corrected
ordinary-column recurrence. -/
theorem identityLattice_nine_massLocalFactor_two_eq :
    (identityLattice 9).massLocalFactor 2 = (42525 / 16384 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 9 = 34560 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 8
    (by norm_num), identityLattice_eight_massLocalFactor_two_eq, hordinary]
  norm_num

/-- Rank ten is the next even-rank, odd half-rank Type I identity-lattice
local-factor sample from the normalized recurrence. -/
theorem identityLattice_ten_massLocalFactor_two_eq :
    (identityLattice 10).massLocalFactor 2 = (722925 / 262144 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 10 = 139264 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 9
    (by norm_num), identityLattice_nine_massLocalFactor_two_eq, hordinary]
  norm_num

/-- Rank eleven is the next odd-rank Type I identity-lattice local-factor sample
from the normalized recurrence. -/
theorem identityLattice_eleven_massLocalFactor_two_eq :
    (identityLattice 11).massLocalFactor 2 = (23856525 / 8388608 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 11 = 540672 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 10
    (by norm_num), identityLattice_ten_massLocalFactor_two_eq, hordinary]
  norm_num

/-- Rank twelve is the next even-rank, even half-rank Type I identity-lattice
local-factor sample from the normalized recurrence. -/
theorem identityLattice_twelve_massLocalFactor_two_eq :
    (identityLattice 12).massLocalFactor 2 = (23856525 / 8388608 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 12 = 2097152 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 11
    (by norm_num), identityLattice_eleven_massLocalFactor_two_eq, hordinary]
  norm_num

/-- Rank thirteen is the next odd-rank Type I identity-lattice local-factor
sample from the normalized recurrence. -/
theorem identityLattice_thirteen_massLocalFactor_two_eq :
    (identityLattice 13).massLocalFactor 2 =
      (48070897875 / 17179869184 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 13 = 8253440 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 12
    (by norm_num), identityLattice_twelve_massLocalFactor_two_eq, hordinary]
  norm_num

/-- Rank fourteen is the next even-rank, odd half-rank Type I identity-lattice
local-factor sample from the normalized recurrence. -/
theorem identityLattice_fourteen_massLocalFactor_two_eq :
    (identityLattice 14).massLocalFactor 2 =
      (3028466566125 / 1099511627776 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 14 = 33030144 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 13
    (by norm_num), identityLattice_thirteen_massLocalFactor_two_eq, hordinary]
  norm_num

set_option maxHeartbeats 800000 in
/-- Rank fifteen is the next odd-rank Type I identity-lattice local-factor
sample from the normalized recurrence. -/
theorem identityLattice_fifteen_massLocalFactor_two_eq :
    (identityLattice 15).massLocalFactor 2 =
      (384615253897875 / 140737488355328 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 15 = 133169152 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 14
    (by norm_num), identityLattice_fourteen_massLocalFactor_two_eq, hordinary]
  norm_num

set_option maxHeartbeats 800000 in
/-- Rank sixteen is the next even-rank, even half-rank Type I identity-lattice
local-factor sample from the normalized recurrence. -/
theorem identityLattice_sixteen_massLocalFactor_two_eq :
    (identityLattice 16).massLocalFactor 2 =
      (384615253897875 / 140737488355328 : ℝ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 16 = 536870912 := by
    decide
  rw [identityLattice_massLocalFactor_two_succ_eq_mul_ordinaryCount 15
    (by norm_num), identityLattice_fifteen_massLocalFactor_two_eq, hordinary]
  norm_num

/-- The normalized Type I local-factor step from rank two to rank three. -/
theorem identityQuadraticTypeILocalFactorStep_three :
    identityQuadraticTypeILocalFactorStep 3 = (3 / 2 : ℚ) := by
  have hordinary : identityQuadraticOrdinaryUnitVectorsModFourCount 3 = 12 := by
    decide
  norm_num [identityQuadraticTypeILocalFactorStep, hordinary]

/-- The normalized Type I local-factor step from rank three to rank four. -/
theorem identityQuadraticTypeILocalFactorStep_four :
    identityQuadraticTypeILocalFactorStep 4 = (1 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 3 (by norm_num)
  rw [identityLattice_four_massLocalFactor_two_eq,
    identityLattice_three_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 4 : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
    simpa using h
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank four to rank five. -/
theorem identityQuadraticTypeILocalFactorStep_five :
    identityQuadraticTypeILocalFactorStep 5 = (5 / 8 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 4 (by norm_num)
  rw [identityLattice_five_massLocalFactor_two_eq,
    identityLattice_four_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 5 : ℚ) : ℝ) = ((5 / 8 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank five to rank six. -/
theorem identityQuadraticTypeILocalFactorStep_six :
    identityQuadraticTypeILocalFactorStep 6 = (3 / 4 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 5 (by norm_num)
  rw [identityLattice_six_massLocalFactor_two_eq,
    identityLattice_five_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 6 : ℚ) : ℝ) = ((3 / 4 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank six to rank seven. -/
theorem identityQuadraticTypeILocalFactorStep_seven :
    identityQuadraticTypeILocalFactorStep 7 = (7 / 8 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 6 (by norm_num)
  rw [identityLattice_seven_massLocalFactor_two_eq,
    identityLattice_six_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 7 : ℚ) : ℝ) = ((7 / 8 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank seven to rank eight. -/
theorem identityQuadraticTypeILocalFactorStep_eight :
    identityQuadraticTypeILocalFactorStep 8 = (1 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 7 (by norm_num)
  rw [identityLattice_eight_massLocalFactor_two_eq,
    identityLattice_seven_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 8 : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
    simpa using h
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank eight to rank nine. -/
theorem identityQuadraticTypeILocalFactorStep_nine :
    identityQuadraticTypeILocalFactorStep 9 = (135 / 128 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 8 (by norm_num)
  rw [identityLattice_nine_massLocalFactor_two_eq,
    identityLattice_eight_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 9 : ℚ) : ℝ) = ((135 / 128 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank nine to rank ten. -/
theorem identityQuadraticTypeILocalFactorStep_ten :
    identityQuadraticTypeILocalFactorStep 10 = (17 / 16 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 9 (by norm_num)
  rw [identityLattice_ten_massLocalFactor_two_eq,
    identityLattice_nine_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 10 : ℚ) : ℝ) = ((17 / 16 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank ten to rank eleven. -/
theorem identityQuadraticTypeILocalFactorStep_eleven :
    identityQuadraticTypeILocalFactorStep 11 = (33 / 32 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 10 (by norm_num)
  rw [identityLattice_eleven_massLocalFactor_two_eq,
    identityLattice_ten_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 11 : ℚ) : ℝ) = ((33 / 32 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank eleven to rank twelve. -/
theorem identityQuadraticTypeILocalFactorStep_twelve :
    identityQuadraticTypeILocalFactorStep 12 = (1 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 11 (by norm_num)
  rw [identityLattice_twelve_massLocalFactor_two_eq,
    identityLattice_eleven_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 12 : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
    simpa using h
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank twelve to rank thirteen. -/
theorem identityQuadraticTypeILocalFactorStep_thirteen :
    identityQuadraticTypeILocalFactorStep 13 = (2015 / 2048 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 12 (by norm_num)
  rw [identityLattice_thirteen_massLocalFactor_two_eq,
    identityLattice_twelve_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 13 : ℚ) : ℝ) = ((2015 / 2048 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank thirteen to rank fourteen. -/
theorem identityQuadraticTypeILocalFactorStep_fourteen :
    identityQuadraticTypeILocalFactorStep 14 = (63 / 64 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 13 (by norm_num)
  rw [identityLattice_fourteen_massLocalFactor_two_eq,
    identityLattice_thirteen_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 14 : ℚ) : ℝ) = ((63 / 64 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank fourteen to rank fifteen. -/
theorem identityQuadraticTypeILocalFactorStep_fifteen :
    identityQuadraticTypeILocalFactorStep 15 = (127 / 128 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 14 (by norm_num)
  rw [identityLattice_fifteen_massLocalFactor_two_eq,
    identityLattice_fourteen_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 15 : ℚ) : ℝ) = ((127 / 128 : ℚ) : ℝ) := by
    nlinarith
  exact Rat.cast_injective hcast

/-- The normalized Type I local-factor step from rank fifteen to rank sixteen. -/
theorem identityQuadraticTypeILocalFactorStep_sixteen :
    identityQuadraticTypeILocalFactorStep 16 = (1 : ℚ) := by
  have h := identityLattice_massLocalFactor_two_succ_eq_mul_step 15 (by norm_num)
  rw [identityLattice_sixteen_massLocalFactor_two_eq,
    identityLattice_fifteen_massLocalFactor_two_eq] at h
  norm_num at h
  have hcast : ((identityQuadraticTypeILocalFactorStep 16 : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
    simpa using h
  exact Rat.cast_injective hcast

/-- The closed residue-class step candidate agrees with all currently verified
Type I identity-lattice step samples. -/
theorem identityQuadraticTypeILocalFactorStep_eq_closed_of_three_le_of_le_sixteen
    {m : ℕ} (h3 : 3 ≤ m) (h16 : m ≤ 16) :
    identityQuadraticTypeILocalFactorStep m =
      identityQuadraticTypeILocalFactorStepClosed m := by
  interval_cases m <;>
    norm_num [identityQuadraticTypeILocalFactorStepClosed,
      identityQuadraticTypeILocalFactorStep_three,
      identityQuadraticTypeILocalFactorStep_four,
      identityQuadraticTypeILocalFactorStep_five,
      identityQuadraticTypeILocalFactorStep_six,
      identityQuadraticTypeILocalFactorStep_seven,
      identityQuadraticTypeILocalFactorStep_eight,
      identityQuadraticTypeILocalFactorStep_nine,
      identityQuadraticTypeILocalFactorStep_ten,
      identityQuadraticTypeILocalFactorStep_eleven,
      identityQuadraticTypeILocalFactorStep_twelve,
      identityQuadraticTypeILocalFactorStep_thirteen,
      identityQuadraticTypeILocalFactorStep_fourteen,
      identityQuadraticTypeILocalFactorStep_fifteen,
      identityQuadraticTypeILocalFactorStep_sixteen]

end PositiveDefiniteIntegralLattice

end
