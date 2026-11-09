import SMSFormula.Applications.Unimodular.DyadicTypeI
import SMSFormula.Applications.Unimodular.DyadicE8CorrectionFiber
import SMSFormula.StandardAxiomsGuard

/-!
Finite certificates for the stable identity comparison (the finite
second-orbit argument of Voskresenskii, §17): an explicit 8×8 index-three
`A₈` certificate and mixed-modulus quadratic isometries.  No mass is
assumed here.
-/

open Matrix BigOperators PositiveDefiniteIntegralLattice
namespace StableIdentityComparisonCertificate

/-- Columns give an index-three A8 sublattice in the actual stored E8 matrix. -/
def a8Embedding : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 2;
    0, -1, -1, -1, -1, -1, -1, 3;
    0, 0, -1, -1, -1, -1, -1, 5;
    0, 0, 0, -1, -1, -1, -1, 4;
    0, 0, 0, 0, -1, -1, -1, 3;
    0, 0, 0, 0, 0, -1, -1, 2;
    0, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 0, 3]

/-- I + J, not the chain-basis Cartan matrix of A8. -/
def a8Gram : Matrix (Fin 8) (Fin 8) ℤ := fun i j => if i = j then 2 else 1

/-- Small exact matrix certificate; no lattice classification is invoked. -/
theorem a8Embedding_gram :
    a8Embedding.transpose * PositiveDefiniteIntegralLattice.e8CartanMatrix * a8Embedding = a8Gram := by
  decide

/-- An explicit inverse of the embedding modulo four; no determinant API is needed. -/
def a8InverseFour : Matrix (Fin 8) (Fin 8) (ZMod 4) :=
  !![1, 0, 0, 0, 0, 0, 0, 2;
    0, 3, 1, 0, 0, 0, 0, 2;
    0, 0, 3, 1, 0, 0, 0, 3;
    0, 0, 0, 3, 1, 0, 0, 3;
    0, 0, 0, 0, 3, 1, 0, 3;
    0, 0, 0, 0, 0, 3, 1, 3;
    0, 0, 0, 0, 0, 0, 3, 3;
    0, 0, 0, 0, 0, 0, 0, 3]

theorem a8Embedding_left_inverse_four :
    a8InverseFour * a8Embedding.map (Int.cast : ℤ → ZMod 4) = 1 := by decide

theorem a8Embedding_right_inverse_four :
    a8Embedding.map (Int.cast : ℤ → ZMod 4) * a8InverseFour = 1 := by decide

/-- Maps coordinates of <1> perpendicular E8 to coordinates of I9, modulo four.
The integral map need not be an integral lattice isometry over Z. -/
def stableNine : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 3, 1, 0, 0, 0, 0, 0, 2;
    1, 1, 0, 0, 0, 0, 0, 0, 2;
    1, 0, 3, 1, 0, 0, 0, 0, 2;
    1, 0, 0, 3, 1, 0, 0, 0, 3;
    1, 0, 0, 0, 3, 1, 0, 0, 3;
    1, 0, 0, 0, 0, 3, 1, 0, 3;
    1, 0, 0, 0, 0, 0, 3, 1, 3;
    1, 0, 0, 0, 0, 0, 0, 3, 3;
    1, 0, 0, 0, 0, 0, 0, 0, 3]

def stableNineInverse : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 1, 1, 1, 1, 1, 1, 1, 1;
    1, 2, 1, 1, 1, 1, 1, 1, 3;
    3, 3, 2, 2, 2, 2, 2, 2, 2;
    0, 0, 0, 3, 3, 3, 3, 3, 1;
    0, 0, 0, 0, 3, 3, 3, 3, 0;
    0, 0, 0, 0, 0, 3, 3, 3, 3;
    0, 0, 0, 0, 0, 0, 3, 3, 2;
    0, 0, 0, 0, 0, 0, 0, 3, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 0]

theorem stableNine_left_inverse_four :
    stableNineInverse.map (Int.cast : ℤ → ZMod 4) *
      stableNine.map (Int.cast : ℤ → ZMod 4) = 1 := by decide

theorem stableNine_right_inverse_four :
    stableNine.map (Int.cast : ℤ → ZMod 4) *
      stableNineInverse.map (Int.cast : ℤ → ZMod 4) = 1 := by decide

/-- The distinguished norm-one line goes to the characteristic vector. -/
theorem stableNine_first_column (i : Fin 9) : stableNine i 0 = 1 := by
  fin_cases i <;> rfl

theorem stableNineInverse_characteristic :
    (stableNineInverse.map (Int.cast : ℤ → ZMod 4)).mulVec (fun _ => 1) =
      Pi.single 0 1 := by decide

/-- Polynomial norm of the stored E8 Gram matrix, over any commutative ring. -/
def e8Norm {R : Type*} [CommRing R] (x : Fin 8 → R) : R :=
  ∑ i, x i * (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R)).mulVec x i

set_option maxHeartbeats 800000

/-- The quadratic congruence itself, not merely preservation of its polar form.
Expansion is a nine-variable polynomial identity over Z/8; the proof does not
use an exhaustive decision procedure over all vectors. -/
theorem stableNine_norm_eight (x : Fin 9 → ZMod 8) :
    (∑ i, ((stableNine.map (Int.cast : ℤ → ZMod 8)).mulVec x i) ^ 2) =
      x 0 ^ 2 + e8Norm (fun i : Fin 8 => x i.succ) := by
  simp [stableNine, e8Norm, PositiveDefiniteIntegralLattice.e8CartanMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring_nf
  rw [show (6 : ZMod 8) = -2 by decide, show (8 : ZMod 8) = 0 by decide,
    show (9 : ZMod 8) = 1 by decide, show (10 : ZMod 8) = 2 by decide,
    show (16 : ZMod 8) = 0 by decide, show (22 : ZMod 8) = -2 by decide,
    show (24 : ZMod 8) = 0 by decide, show (48 : ZMod 8) = 0 by decide,
    show (66 : ZMod 8) = 2 by decide]
  ring

theorem stableNineInverse_norm_eight (x : Fin 9 → ZMod 8) :
    let y := (stableNineInverse.map (Int.cast : ℤ → ZMod 8)).mulVec x
    y 0 ^ 2 + e8Norm (fun i : Fin 8 => y i.succ) = ∑ i, x i ^ 2 := by
  simp [stableNineInverse, e8Norm, PositiveDefiniteIntegralLattice.e8CartanMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring_nf
  rw [show (8 : ZMod 8) = 0 by decide, show (9 : ZMod 8) = 1 by decide,
    show (16 : ZMod 8) = 0 by decide, show (17 : ZMod 8) = 1 by decide,
    show (24 : ZMod 8) = 0 by decide, show (25 : ZMod 8) = 1 by decide,
    show (32 : ZMod 8) = 0 by decide]
  ring

/-- The rank-nine quadratic form obtained by adjoining a norm-one line to the
stored E8 quadratic form, expressed on `ZMod 4` coordinates and valued modulo
`8`.  This is the native fixed-line target used by the second-orbit count route. -/
def onePlusE8NormModEight (x : Fin 9 → ZMod 4) : ZMod 8 :=
  zmodFourLiftToZModEight (x 0) ^ 2 +
    e8Norm (fun i : Fin 8 => zmodFourLiftToZModEight (x i.succ))

/-- The stable-nine certificate identifies the diagonal rank-nine native
quadratic form with the norm-one-line plus stored-E8 form.  The proof uses the
polynomial mod-`8` certificate `stableNine_norm_eight`; it does not enumerate
all `4^9` vectors. -/
theorem stableNine_identityQuadraticModEight_eq_onePlusE8Norm
    (x : Fin 9 → ZMod 4) :
    identityQuadraticModEight ((stableNine.map (Int.cast : ℤ → ZMod 4)).mulVec x) =
      onePlusE8NormModEight x := by
  rw [show identityQuadraticModEight ((stableNine.map (Int.cast : ℤ → ZMod 4)).mulVec x) =
      (∑ i, ((stableNine.map (Int.cast : ℤ → ZMod 8)).mulVec
        (fun j => ((x j).val : ZMod 8)) i) ^ 2) by
    unfold identityQuadraticModEight
    apply Finset.sum_congr rfl
    intro i _
    rw [show (stableNine.map (Int.cast : ℤ → ZMod 4)).mulVec x i =
      ((∑ j, stableNine i j * (x j).val : ℤ) : ZMod 4) by
        simp [Matrix.mulVec, dotProduct]]
    rw [zmodFourLiftToZModEight_sq_intCast]
    congr 1
    simp [Matrix.mulVec, dotProduct]]
  rw [stableNine_norm_eight]
  simp [onePlusE8NormModEight, zmodFourLiftToZModEight]

/-- The distinguished line in the line-plus-E8 coordinates maps to the
characteristic vector for the diagonal rank-nine form. -/
theorem stableNine_modFour_mulVec_firstLine :
    (stableNine.map (Int.cast : ℤ → ZMod 4)).mulVec (Pi.single 0 1) =
      (fun _ : Fin 9 => (1 : ZMod 4)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, stableNine_first_column]

/-- Multiplication by two makes the canonical `ZMod 4` lift additive into `ZMod 8`. -/
theorem two_mul_zmodFourLiftToZModEight_add (a b : ZMod 4) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (a + b) =
      (2 : ZMod 8) * zmodFourLiftToZModEight a +
        (2 : ZMod 8) * zmodFourLiftToZModEight b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Multiplication by two makes the canonical `ZMod 4` lift compatible with negation into `ZMod 8`. -/
theorem two_mul_zmodFourLiftToZModEight_neg (a : ZMod 4) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (-a) =
      -((2 : ZMod 8) * zmodFourLiftToZModEight a) := by
  fin_cases a <;> decide

/-- Multiplication by two makes the canonical `ZMod 4` lift compatible with subtraction into `ZMod 8`. -/
theorem two_mul_zmodFourLiftToZModEight_sub (a b : ZMod 4) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (a - b) =
      (2 : ZMod 8) * zmodFourLiftToZModEight a -
        (2 : ZMod 8) * zmodFourLiftToZModEight b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Multiplication by two makes products of canonical `ZMod 4` lifts well-defined in `ZMod 8`. -/
theorem two_mul_zmodFourLiftToZModEight_mul (a b : ZMod 4) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (a * b) =
      (2 : ZMod 8) * zmodFourLiftToZModEight a * zmodFourLiftToZModEight b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Square-specialized product compatibility for the canonical `ZMod 4` lift. -/
theorem two_mul_zmodFourLiftToZModEight_pow_two (a : ZMod 4) :
    (2 : ZMod 8) * zmodFourLiftToZModEight (a ^ 2) =
      (2 : ZMod 8) * zmodFourLiftToZModEight a ^ 2 := by
  fin_cases a <;> decide

/-- The stored E8 quadratic form modulo `8` is twice the corrected polynomial `Q_E8` modulo `4`. -/
theorem e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial (v : Fin 8 → ZMod 4) :
    e8Norm (fun i : Fin 8 => zmodFourLiftToZModEight (v i)) =
      (2 : ZMod 8) * zmodFourLiftToZModEight (e8QuadraticPolynomial v) := by
  simp [e8Norm, e8QuadraticPolynomial, PositiveDefiniteIntegralLattice.e8CartanMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_eight,
    two_mul_zmodFourLiftToZModEight_add,
    two_mul_zmodFourLiftToZModEight_sub, two_mul_zmodFourLiftToZModEight_mul,
    two_mul_zmodFourLiftToZModEight_pow_two]
  ring

/-- E8 matrices preserving the stored E8 quadratic form modulo `8`, stated in the fixed-line tail language. -/
abbrev e8NormIsometryModFour : Type :=
  {X : Matrix (Fin 8) (Fin 8) (ZMod 4) //
    ∀ v : Fin 8 → ZMod 4,
      e8Norm (fun i : Fin 8 => zmodFourLiftToZModEight (X.mulVec v i)) =
        e8Norm (fun i : Fin 8 => zmodFourLiftToZModEight (v i))}

noncomputable instance : Fintype e8NormIsometryModFour := by
  unfold e8NormIsometryModFour
  infer_instance

/-- The map `a ↦ 2 * lift(a)` from `ZMod 4` to `ZMod 8` is injective. -/
theorem two_mul_zmodFourLiftToZModEight_injective :
    Function.Injective (fun a : ZMod 4 => (2 : ZMod 8) * zmodFourLiftToZModEight a) := by
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

/-- The fixed-line tail isometry target for stored E8 is the same finite type as the production
corrected `ZMod 4` E8 quadratic-isometry target. -/
def e8NormIsometryModFourEquivQuadraticIsometryModFour :
    e8NormIsometryModFour ≃ e8QuadraticIsometryModFour where
  toFun X := ⟨X.1, by
    intro v
    apply two_mul_zmodFourLiftToZModEight_injective
    change (2 : ZMod 8) * zmodFourLiftToZModEight (e8QuadraticPolynomial (X.1.mulVec v)) =
      (2 : ZMod 8) * zmodFourLiftToZModEight (e8QuadraticPolynomial v)
    rw [← e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial (X.1.mulVec v), X.2 v,
      e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial v]⟩
  invFun X := ⟨X.1, by
    intro v
    rw [e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial,
      e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial, X.2 v]⟩
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the stored-E8 tail target/production E8 target equivalence. -/
theorem e8NormIsometryModFour_natCard_eq_quadraticIsometryModFour :
    Nat.card e8NormIsometryModFour = Nat.card e8QuadraticIsometryModFour :=
  Nat.card_congr e8NormIsometryModFourEquivQuadraticIsometryModFour

/-- The stored-E8 tail target has the already evaluated E8 native count. -/
theorem e8NormIsometryModFour_natCard_eq_42525_mul_pow :
    Nat.card e8NormIsometryModFour = 42525 * 2 ^ 41 := by
  rw [e8NormIsometryModFour_natCard_eq_quadraticIsometryModFour,
    e8QuadraticIsometryModFour_natCard_eq_42525_mul_pow]

/-- General scalar identity behind the characteristic-line splitting. -/
theorem characteristic_line_identity
    (n : ℕ) (a s t : ℤ) :
    (a - s)^2 + (n*a^2 + 2*a*s + t) = (n+1)*a^2 + (t+s^2) := by ring

/-- General block shear: at 8 | n its error vanishes modulo eight.
This is an alternative to repeatedly applying the rank-nine certificate. -/
theorem a8_block_shear_identity
    (n : ℕ) (s t q r : ℤ) :
    (q - 2*t*s + n*t^2) + r + (s - n*t + t)^2 =
      (q+s^2) + (r+t^2) - 2*n*s*t + n*(n-1:ℤ)*t^2 := by ring

end StableIdentityComparisonCertificate

#assert_standard_axioms StableIdentityComparisonCertificate.a8Embedding_gram
#assert_standard_axioms StableIdentityComparisonCertificate.a8Embedding_left_inverse_four
#assert_standard_axioms StableIdentityComparisonCertificate.a8Embedding_right_inverse_four
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_left_inverse_four
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_right_inverse_four
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_norm_eight
#assert_standard_axioms StableIdentityComparisonCertificate.stableNineInverse_norm_eight
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_identityQuadraticModEight_eq_onePlusE8Norm
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_modFour_mulVec_firstLine
#assert_standard_axioms StableIdentityComparisonCertificate.e8Norm_zmodFourLift_eq_two_mul_e8QuadraticPolynomial
#assert_standard_axioms StableIdentityComparisonCertificate.e8NormIsometryModFourEquivQuadraticIsometryModFour
#assert_standard_axioms StableIdentityComparisonCertificate.e8NormIsometryModFour_natCard_eq_quadraticIsometryModFour
#assert_standard_axioms StableIdentityComparisonCertificate.e8NormIsometryModFour_natCard_eq_42525_mul_pow
#assert_standard_axioms StableIdentityComparisonCertificate.stableNine_first_column
#assert_standard_axioms StableIdentityComparisonCertificate.stableNineInverse_characteristic
