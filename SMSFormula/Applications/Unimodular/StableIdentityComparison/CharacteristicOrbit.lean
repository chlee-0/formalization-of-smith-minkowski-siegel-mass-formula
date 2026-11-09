import SMSFormula.Applications.Unimodular.DyadicTypeI
import SMSFormula.StandardAxiomsGuard

/-!
The finite characteristic orbit has a diagonal sign section, so its
transitivity needs neither Trojan's theorem nor a p-adic isometry lift.
All counts below use the existing Type I mixed mod-8/mod-4 matrix predicate.
-/
noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice
namespace StableIdentityComparison

abbrev R := ZMod 4
abbrev Vec (n : ℕ) := Fin n → R
abbrev Iso (n : ℕ) := identityQuadraticIsometryModFour n
abbrev OddVec (n : ℕ) := {v : Vec n // identityQuadraticAllOddModFour v}
def characteristic (n : ℕ) : Vec n := fun _ => 1
abbrev Fixed (n : ℕ) :=
  {X : Iso n // X.1.mulVec (characteristic n) = characteristic n}

set_option maxHeartbeats 800000 in
lemma twice_lift_injective :
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

/-- Preserve the full bilinear form modulo four, not just its parity. -/
lemma preserves_bilinear {n : ℕ} (X : Iso n) (v w : Vec n) :
    identityBilinearModFour (X.1.mulVec v) (X.1.mulVec w) =
      identityBilinearModFour v w := by
  apply twice_lift_injective
  have h := X.2 (v + w)
  rw [Matrix.mulVec_add, identityQuadraticModEight_add,
    identityQuadraticModEight_add, X.2 v, X.2 w] at h
  exact add_left_cancel h

lemma transpose_mul {n : ℕ} (X : Iso n) : X.1.transpose * X.1 = 1 := by
  ext i j
  have h := preserves_bilinear X
    (identityQuadraticBasisVectorModFour i) (identityQuadraticBasisVectorModFour j)
  rw [matrix_mulVec_identityQuadraticBasisVectorModFour,
    matrix_mulVec_identityQuadraticBasisVectorModFour,
    identityBilinearModFour_basis_right] at h
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, identityBilinearModFour,
      identityQuadraticBasisVectorModFour, Pi.single_apply, Matrix.one_apply] using h
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, identityBilinearModFour,
      identityQuadraticBasisVectorModFour, Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij] using h

lemma transpose_left_inverse {n : ℕ} (X : Iso n) :
    Function.LeftInverse X.1.transpose.mulVec X.1.mulVec := by
  intro x
  rw [Matrix.mulVec_mulVec, transpose_mul X]
  simp

/-- Finite injectivity supplies right-invertibility without a new matrix inverse API. -/
lemma mul_transpose {n : ℕ} (X : Iso n) : X.1 * X.1.transpose = 1 := by
  apply matrix_eq_of_mulVec_eq
  intro x
  have hs : Function.Surjective X.1.mulVec :=
    Finite.surjective_of_injective (transpose_left_inverse X).injective
  obtain ⟨y, rfl⟩ := hs x
  rw [← Matrix.mulVec_mulVec, transpose_left_inverse X y]
  simp

lemma bit_mul_self (a : ZMod 2) : a * a = a := by fin_cases a <;> decide

lemma odd_of_parity_one (a : R) (h : zmodFourToZModTwo a = 1) :
    a = 1 ∨ a = 3 := by
  fin_cases a
  · exfalso
    change (0 : ZMod 2) = 1 at h
    exact (by decide : (0 : ZMod 2) ≠ 1) h
  · left
    rfl
  · exfalso
    change (0 : ZMod 2) = 1 at h
    exact (by decide : (0 : ZMod 2) ≠ 1) h
  · right
    rfl

/-- Row norms modulo four force the image of the characteristic vector to be all-odd. -/
lemma image_characteristic_allOdd {n : ℕ} (X : Iso n) :
    identityQuadraticAllOddModFour (X.1.mulVec (characteristic n)) := by
  intro i
  apply odd_of_parity_one
  have h := congrFun (congrFun (mul_transpose X) i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have h2 := congrArg zmodFourToZModTwo h
  simp only [map_sum, map_mul, bit_mul_self] at h2
  simpa [Matrix.mulVec, dotProduct, characteristic, map_sum] using h2

def orbit {n : ℕ} (X : Iso n) : OddVec n :=
  ⟨X.1.mulVec (characteristic n), image_characteristic_allOdd X⟩

lemma odd_square (a : R) (ha : a = 1 ∨ a = 3) : a * a = 1 := by
  rcases ha with rfl | rfl <;> decide

lemma odd_lift_square (a : R) (ha : a = 1 ∨ a = 3) :
    zmodFourLiftToZModEight a ^ 2 = 1 := by
  rcases ha with rfl | rfl <;> decide

/-- Left multiplication by the diagonal sign section, written as row scaling. -/
def twist {n : ℕ} (v : OddVec n) (X : Iso n) : Iso n :=
  ⟨((fun i j => v.1 i * X.1 i j) : Matrix (Fin n) (Fin n) R), by
    intro x
    have hv : Matrix.mulVec (((fun i j => v.1 i * X.1 i j) : Matrix (Fin n) (Fin n) R)) x =
        fun i => v.1 i * X.1.mulVec x i := by
      funext i
      change ∑ j, v.1 i * X.1 i j * x j = v.1 i * ∑ j, X.1 i j * x j
      simp [Finset.mul_sum, mul_assoc]
    rw [hv]
    calc
      identityQuadraticModEight (fun i => v.1 i * X.1.mulVec x i) =
          identityQuadraticModEight (X.1.mulVec x) := by
        unfold identityQuadraticModEight
        apply Finset.sum_congr rfl
        intro i _
        rw [zmodFourLiftToZModEight_mul_sq, odd_lift_square _ (v.2 i), one_mul]
      _ = identityQuadraticModEight x := X.2 x⟩

lemma twist_mulVec {n : ℕ} (v : OddVec n) (X : Iso n) (x : Vec n) :
    (twist v X).1.mulVec x = fun i => v.1 i * X.1.mulVec x i := by
  funext i
  change ∑ j, v.1 i * X.1 i j * x j = v.1 i * ∑ j, X.1 i j * x j
  simp [Finset.mul_sum, mul_assoc]

lemma twist_involutive {n : ℕ} (v : OddVec n) (X : Iso n) :
    twist v (twist v X) = X := by
  apply Subtype.ext
  funext i j
  change v.1 i * (v.1 i * X.1 i j) = X.1 i j
  rw [← mul_assoc, odd_square _ (v.2 i), one_mul]

def normalize {n : ℕ} (X : Iso n) : Fixed n :=
  ⟨twist (orbit X) X, by
    rw [twist_mulVec]
    funext i
    change X.1.mulVec (characteristic n) i * X.1.mulVec (characteristic n) i = 1
    exact odd_square _ ((orbit X).2 i)⟩

lemma orbit_twist_fixed {n : ℕ} (v : OddVec n) (S : Fixed n) :
    orbit (twist v S.1) = v := by
  apply Subtype.ext
  change (twist v S.1).1.mulVec (characteristic n) = v.1
  rw [twist_mulVec, S.2]
  funext i
  simp [characteristic]

/-- Actual finite isometries = signs times the characteristic-vector stabilizer.
Valid in every rank, even when the characteristic vector does not have norm one.
Only the subsequent E8 stabilizer identification requires rank 8*k+1. -/
def characteristicOrbitEquiv (n : ℕ) : Iso n ≃ OddVec n × Fixed n where
  toFun X := (orbit X, normalize X)
  invFun p := twist p.1 p.2.1
  left_inv X := twist_involutive (orbit X) X
  right_inv p := by
    rcases p with ⟨v, S⟩
    apply Prod.ext
    · exact orbit_twist_fixed v S
    · apply Subtype.ext
      change twist (orbit (twist v S.1)) (twist v S.1) = S.1
      rw [orbit_twist_fixed, twist_involutive]

/-- The characteristic orbit cardinality is proved, not supplied as a hypothesis. -/
theorem native_identity_count_eq_signs_mul_fixed (n : ℕ) :
    Nat.card (Iso n) = 2 ^ n * Nat.card (Fixed n) := by
  rw [Nat.card_congr (characteristicOrbitEquiv n), Nat.card_prod]
  exact congrArg (fun t => t * Nat.card (Fixed n)) (identityQuadraticAllOddModFour_natCard n)

/-- The same identity for the associated-bilinear quotient count. -/
theorem native_quotient_count_eq_signs_mul_fixed (n : ℕ) :
    associatedBilinearDualQuotientCount (identityLattice n) 2 3 =
      2 ^ n * Nat.card (Fixed n) := by
  rw [identityLattice_associatedBilinearDualQuotientCount_two_three_eq_isometryCount,
    ← identityQuadraticIsometryModFour_natCard_eq_count]
  exact native_identity_count_eq_signs_mul_fixed n

/-- Transport the characteristic-orbit count across any explicit equivalence out of
the fixed-characteristic set.  Later seed-coordinate work supplies this equivalence
from fixed characteristic matrices to the native `typeIISeed k` finite target. -/
theorem native_identity_count_eq_signs_mul_of_fixed_equiv
    (n : ℕ) (α : Type*) [Fintype α] (e : Fixed n ≃ α) :
    Nat.card (Iso n) = 2 ^ n * Nat.card α := by
  rw [native_identity_count_eq_signs_mul_fixed]
  exact congrArg (fun c => 2 ^ n * c) (Nat.card_congr e)

/-- The same fixed-set transport for the associated-bilinear quotient count
of the identity lattice. -/
theorem native_quotient_count_eq_signs_mul_of_fixed_equiv
    (n : ℕ) (α : Type*) [Fintype α] (e : Fixed n ≃ α) :
    associatedBilinearDualQuotientCount (identityLattice n) 2 3 =
      2 ^ n * Nat.card α := by
  rw [native_quotient_count_eq_signs_mul_fixed]
  exact congrArg (fun c => 2 ^ n * c) (Nat.card_congr e)

/-
Not asserted in this file: an equivalence from `Fixed (8*k+1)` to a finite
solution type of `typeIISeed k`.  Given one, `Nat.card_congr` and the preceding
theorem supply the count input of `NativeAssembly`.  `CountAdapter`
(`stableNineFixedEquivE8Norm`, rank nine, from `A8Certificate`) and
`SeedNormAdapter` (`fixedEquivSeedNormOfStable`, from supplied stable coordinate
matrices) construct such equivalences to seed-norm isometry types.
-/
end StableIdentityComparison

#assert_standard_axioms StableIdentityComparison.preserves_bilinear
#assert_standard_axioms StableIdentityComparison.transpose_mul
#assert_standard_axioms StableIdentityComparison.mul_transpose
#assert_standard_axioms StableIdentityComparison.image_characteristic_allOdd
#assert_standard_axioms StableIdentityComparison.characteristicOrbitEquiv
#assert_standard_axioms StableIdentityComparison.native_identity_count_eq_signs_mul_fixed
#assert_standard_axioms StableIdentityComparison.native_quotient_count_eq_signs_mul_fixed
#assert_standard_axioms StableIdentityComparison.native_identity_count_eq_signs_mul_of_fixed_equiv
#assert_standard_axioms StableIdentityComparison.native_quotient_count_eq_signs_mul_of_fixed_equiv
