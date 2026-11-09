import SMSFormula.BinaryContent
import Mathlib.LinearAlgebra.Reflection

/-!
# Local normalization and reflections of the primitive binary polynomial

The polynomial is extended by its integer coefficients on the same coordinate
module. Exact content cancellation transports the actual local isometry matrix.
No inverse of 2 and no integral symmetric matrix for the divided form are used.
Unit-value reflections have determinant -1 and give proper local isometries.
-/

open Matrix

namespace QuadraticMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private def unitReflectionForm (Q : QuadraticForm R M) (v : M) (u : Rˣ) : Module.Dual R M :=
  (↑(u⁻¹) : R) • Q.polarBilin v

private lemma unitReflectionForm_self (Q : QuadraticForm R M) (v : M) (u : Rˣ)
    (hv : Q v = (u : R)) : unitReflectionForm Q v u v = 2 := by
  change (↑(u⁻¹) : R) * Q.polarBilin v v = 2
  rw [polarBilin_apply_apply, polar_self]
  simp [hv, two_smul, mul_add]
  ring

/-- A unit norm value defines an integral reflection without inverting 2. -/
noncomputable def unitValueReflection (Q : QuadraticForm R M) (v : M) (u : Rˣ)
    (hv : Q v = (u : R)) : Q.IsometryEquiv Q where
  toLinearEquiv := Module.reflection (unitReflectionForm_self Q v u hv)
  map_app' w := by
    change Q (Module.reflection (unitReflectionForm_self Q v u hv) w) = Q w
    rw [Module.reflection_apply]
    change Q (w - ((↑(u⁻¹) : R) * Q.polarBilin v w) • v) = Q w
    rw [sub_eq_add_neg, QuadraticMap.map_add Q]
    simp only [QuadraticMap.map_neg, QuadraticMap.map_smul,
      polar_neg_right, polar_smul_right, smul_eq_mul, polarBilin_apply_apply]
    rw [polar_comm Q w v, hv]
    have hinv : (↑(u⁻¹) : R) * (u : R) = 1 := by simp
    linear_combination ((↑(u⁻¹) : R) * (polar Q v w) ^ 2) * hinv

lemma unitValueReflection_apply (Q : QuadraticForm R M) (v : M) (u : Rˣ)
    (hv : Q v = (u : R)) (w : M) :
    unitValueReflection Q v u hv w = w - ((↑(u⁻¹) : R) * Q.polarBilin v w) • v := by
  change Module.reflection (unitReflectionForm_self Q v u hv) w = _
  rw [Module.reflection_apply]
  rfl

lemma unitValueReflection_apply_self (Q : QuadraticForm R M) (v : M) (u : Rˣ)
    (hv : Q v = (u : R)) : unitValueReflection Q v u hv v = -v := by
  change Module.reflection (unitReflectionForm_self Q v u hv) v = -v
  exact Module.reflection_apply_self _

lemma unitValueReflection_involutive (Q : QuadraticForm R M) (v : M) (u : Rˣ)
    (hv : Q v = (u : R)) : Function.Involutive (unitValueReflection Q v u hv) := by
  change Function.Involutive (Module.reflection (unitReflectionForm_self Q v u hv))
  exact Module.involutive_reflection _

/-- In binary coordinates the unit-value reflection has determinant -1 over
the original ring. There is no characteristic or invertibility assumption on 2. -/
lemma unitValueReflection_det_fin_two (Q : QuadraticForm R (Fin 2 → R))
    (v : Fin 2 → R) (u : Rˣ) (hv : Q v = (u : R)) :
    (LinearMap.toMatrix' (unitValueReflection Q v u hv).toLinearEquiv.toLinearMap).det = -1 := by
  let f := unitReflectionForm Q v u
  have hfv : f v = 2 := unitReflectionForm_self Q v u hv
  have hvec : v = v 0 • (Pi.single 0 (1 : R)) + v 1 • (Pi.single 1 (1 : R)) := by
    ext i
    fin_cases i <;> simp
  have hlin : v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1) = 2 := by
    have hh := congrArg f hvec
    rw [hfv] at hh
    simpa [map_add, map_smul, smul_eq_mul] using hh.symm
  have hmatrix : LinearMap.toMatrix' (unitValueReflection Q v u hv).toLinearEquiv.toLinearMap =
      !![1 - f (Pi.single 0 1) * v 0, -f (Pi.single 1 1) * v 0;
        -f (Pi.single 0 1) * v 1, 1 - f (Pi.single 1 1) * v 1] := by
    ext i j
    simp only [LinearMap.toMatrix'_apply]
    change (unitValueReflection Q v u hv (Pi.single j 1)) i = _
    rw [unitValueReflection_apply]
    fin_cases i <;> fin_cases j <;> simp [f, unitReflectionForm]
  rw [hmatrix, Matrix.det_fin_two]
  change (1 - f (Pi.single 0 1) * v 0) * (1 - f (Pi.single 1 1) * v 1) -
    (-f (Pi.single 1 1) * v 0) * (-f (Pi.single 0 1) * v 1) = -1
  linear_combination -hlin

end QuadraticMap

namespace PositiveDefiniteIntegralLattice

variable {R : Type*} [CommRing R]

/-- Coefficient extension of the proved primitive polynomial to a scalar ring. -/
def binaryPrimitivePolynomialOver (K : PositiveDefiniteIntegralLattice 2) (R : Type*) [CommRing R] :
    QuadraticForm R (Fin 2 → R) :=
  (!![((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) : R),
      (((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ) : ℤ) : R);
      0, ((K.pairingMatrix 1 1 / (K.binaryContent : ℤ) : ℤ) : R)] :
        Matrix (Fin 2) (Fin 2) R).toQuadraticForm'

lemma binaryPrimitivePolynomialOver_apply (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → R) :
    K.binaryPrimitivePolynomialOver R x =
      ((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) : R) * x 0 ^ 2 +
      (((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ) : ℤ) : R) * x 0 * x 1 +
      ((K.pairingMatrix 1 1 / (K.binaryContent : ℤ) : ℤ) : R) * x 1 ^ 2 := by
  simp only [binaryPrimitivePolynomialOver, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The coefficient extension agrees with the original polynomial on integer vectors. -/
lemma binaryPrimitivePolynomialOver_intCast (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → ℤ) :
    K.binaryPrimitivePolynomialOver R (fun i => (x i : R)) =
      (K.binaryPrimitivePolynomial x : R) := by
  simp [binaryPrimitivePolynomialOver_apply, binaryPrimitivePolynomial_apply]

/-- Extension back to Z is the existing primitive quadratic form itself. -/
lemma binaryPrimitivePolynomialOver_int (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryPrimitivePolynomialOver ℤ = K.binaryPrimitivePolynomial := by
  ext x
  simpa only [Int.cast_id] using K.binaryPrimitivePolynomialOver_intCast (R := ℤ) x

/-- The original scalar-extended norm is exactly g times the primitive polynomial. -/
lemma binary_norm_eq_content_mul_primitive_over (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → R) :
    dotProduct x ((K.pairingMatrix.map (Int.cast : ℤ → R)).mulVec x) =
      (K.binaryContent : R) * K.binaryPrimitivePolynomialOver R x := by
  have hd := (dvd_binaryContent_iff K K.binaryContent).mp (dvd_refl _)
  have ha : (K.pairingMatrix 0 0 : R) = (K.binaryContent : R) *
      ((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) : R) := by
    simpa using congrArg (Int.castRingHom R) (Int.mul_ediv_cancel' hd.1).symm
  have hb : 2 * (K.pairingMatrix 0 1 : R) = (K.binaryContent : R) *
      (((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ) : ℤ) : R) := by
    simpa using congrArg (Int.castRingHom R) (Int.mul_ediv_cancel' hd.2.1).symm
  have hc : (K.pairingMatrix 1 1 : R) = (K.binaryContent : R) *
      ((K.pairingMatrix 1 1 / (K.binaryContent : ℤ) : ℤ) : R) := by
    simpa using congrArg (Int.castRingHom R) (Int.mul_ediv_cancel' hd.2.2).symm
  have hs : (K.pairingMatrix.map (Int.cast : ℤ → R)).IsSymm := by
    ext i j
    simp only [transpose_apply, map_apply]
    rw [K.form_symm.apply i j]
  rw [binaryPrimitivePolynomialOver_apply]
  exact Matrix.dotProduct_mulVec_fin_two_eq_scalar_polynomial _ hs
    (K.binaryContent : R) _ _ _ ha hb hc x

private lemma binary_symm_matrix_eq_of_norm_eq [NoZeroDivisors R] [CharZero R]
    (F G : Matrix (Fin 2) (Fin 2) R) (hF : F.IsSymm) (hG : G.IsSymm)
    (h : ∀ x, dotProduct x (F.mulVec x) = dotProduct x (G.mulVec x)) : F = G := by
  have ha : F 0 0 = G 0 0 := by
    simpa [Matrix.dotProduct_mulVec_fin_two F hF,
      Matrix.dotProduct_mulVec_fin_two G hG] using h ![1, 0]
  have hc : F 1 1 = G 1 1 := by
    simpa [Matrix.dotProduct_mulVec_fin_two F hF,
      Matrix.dotProduct_mulVec_fin_two G hG] using h ![0, 1]
  have hs : F 0 0 + 2 * F 0 1 + F 1 1 = G 0 0 + 2 * G 0 1 + G 1 1 := by
    simpa [Matrix.dotProduct_mulVec_fin_two F hF,
      Matrix.dotProduct_mulVec_fin_two G hG] using h ![1, 1]
  have hb2 : 2 * F 0 1 = 2 * G 0 1 := by linear_combination hs - ha - hc
  have hb : F 0 1 = G 0 1 := mul_left_cancel₀ (two_ne_zero : (2 : R) ≠ 0) hb2
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact (hF.apply 0 1).trans (hb.trans (hG.apply 0 1).symm)
  · exact hc

/-- For equal actual contents, preserving the primitive polynomial is exactly
the original matrix congruence. The reverse direction cancels 2 in a domain. -/
lemma binaryPrimitivePolynomialOver_matrix_congruence_iff
    [NoZeroDivisors R] [CharZero R]
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent)
    (U : Matrix (Fin 2) (Fin 2) R) :
    (U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U =
      K.pairingMatrix.map (Int.cast : ℤ → R)) ↔
      ∀ x, L.binaryPrimitivePolynomialOver R (U.mulVec x) =
        K.binaryPrimitivePolynomialOver R x := by
  have hcongr (x : Fin 2 → R) :
      dotProduct x ((U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U).mulVec x) =
        dotProduct (U.mulVec x) ((L.pairingMatrix.map (Int.cast : ℤ → R)).mulVec (U.mulVec x)) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  constructor
  · intro hform x
    have hnorm := hcongr x
    rw [hform, binary_norm_eq_content_mul_primitive_over,
      binary_norm_eq_content_mul_primitive_over, ← hg] at hnorm
    have hgne : (K.binaryContent : R) ≠ 0 := by
      exact_mod_cast (ne_of_gt K.binaryContent_pos)
    exact (mul_left_cancel₀ hgne hnorm).symm
  · intro hpoly
    have hs (M : PositiveDefiniteIntegralLattice 2) : (M.pairingMatrix.map (Int.cast : ℤ → R)).IsSymm := by
      ext i j
      simp only [transpose_apply, map_apply]
      rw [M.form_symm.apply i j]
    have hsU : (U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U).IsSymm := by
      simp [Matrix.IsSymm, Matrix.transpose_mul, (hs L).eq, Matrix.mul_assoc]
    apply binary_symm_matrix_eq_of_norm_eq _ _ hsU (hs K)
    intro x
    rw [hcongr, binary_norm_eq_content_mul_primitive_over,
      binary_norm_eq_content_mul_primitive_over, hpoly x, hg]

/-- Same-content original matrix isometries transport to the primitive polynomial.
Only the common nonzero content is cancelled; 2 need not be invertible. -/
noncomputable def binaryPrimitivePolynomialOverIsometryEquivOfMatrix
    [NoZeroDivisors R] [CharZero R]
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent)
    (U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U)
    (hform : U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U =
      K.pairingMatrix.map (Int.cast : ℤ → R)) :
    (K.binaryPrimitivePolynomialOver R).IsometryEquiv (L.binaryPrimitivePolynomialOver R) where
  toLinearEquiv := Matrix.toLinearEquiv' U hU.invertible
  map_app' x := by
    have heq := (binaryPrimitivePolynomialOver_matrix_congruence_iff K L hg U).mp hform x
    simpa [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply] using heq

lemma binaryPrimitivePolynomialOverIsometryEquivOfMatrix_apply
    [NoZeroDivisors R] [CharZero R]
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent)
    (U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U)
    (hform : U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U =
      K.pairingMatrix.map (Int.cast : ℤ → R)) (x : Fin 2 → R) :
    binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L hg U hU hform x = U.mulVec x := by
  change Matrix.toLinearEquiv' U hU.invertible x = U.mulVec x
  rfl

lemma binaryPrimitivePolynomialOverIsometryEquivOfMatrix_toMatrix
    [NoZeroDivisors R] [CharZero R]
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent)
    (U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U)
    (hform : U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U =
      K.pairingMatrix.map (Int.cast : ℤ → R)) :
    LinearMap.toMatrix'
      (binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L hg U hU hform).toLinearEquiv.toLinearMap =
      U := by
  change LinearMap.toMatrix' (Matrix.toLin' U) = U
  exact LinearMap.toMatrix'_toLin' U

private lemma binary_isUnit_toMatrix (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) :
    IsUnit (LinearMap.toMatrix' e.toLinearMap) := by
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    ?_, ?_⟩, rfl⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp

/-- The original unit-matrix witness and the primitive polynomial isometry
witness are equivalent, over characteristic-zero domains. -/
lemma exists_matrix_iff_nonempty_binaryPrimitivePolynomialOver_isometry
    [NoZeroDivisors R] [CharZero R]
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent) :
    (∃ U : Matrix (Fin 2) (Fin 2) R, IsUnit U ∧
      U.transpose * L.pairingMatrix.map (Int.cast : ℤ → R) * U =
        K.pairingMatrix.map (Int.cast : ℤ → R)) ↔
      Nonempty ((K.binaryPrimitivePolynomialOver R).IsometryEquiv
        (L.binaryPrimitivePolynomialOver R)) := by
  constructor
  · rintro ⟨U, hU, hform⟩
    exact ⟨binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L hg U hU hform⟩
  · rintro ⟨e⟩
    refine ⟨LinearMap.toMatrix' e.toLinearEquiv.toLinearMap,
      binary_isUnit_toMatrix e.toLinearEquiv, ?_⟩
    apply (binaryPrimitivePolynomialOver_matrix_congruence_iff K L hg _).mpr
    intro x
    rw [LinearMap.toMatrix'_mulVec]
    exact e.map_app x

/-- At fixed content the original global integral isometry relation is exactly
the isometry relation of the primitive polynomials on the same integer carrier. -/
theorem isGlobalIsometry_iff_binaryPrimitivePolynomial_isometry_of_content_eq
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent) :
    K.IsGlobalIsometry L ↔
      Nonempty (K.binaryPrimitivePolynomial.IsometryEquiv L.binaryPrimitivePolynomial) := by
  have hi : (Int.cast : ℤ → ℤ) = id := by
    funext z
    exact Int.cast_id
  simpa only [IsGlobalIsometry, hi, Matrix.map_id, binaryPrimitivePolynomialOver_int] using
    exists_matrix_iff_nonempty_binaryPrimitivePolynomialOver_isometry (R := ℤ) K L hg

/-- Every actual finite-prime genus witness gives a primitive polynomial isometry. -/
theorem IsSameGenus.nonempty_binaryPrimitivePolynomialOver_padic_isometry
    {K L : PositiveDefiniteIntegralLattice 2} (h : K.IsSameGenus L)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty ((K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
      (L.binaryPrimitivePolynomialOver ℤ_[p])) := by
  obtain ⟨U, hU, hform⟩ := h.1 p
  exact ⟨binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L h.binaryContent_eq U hU hform⟩

/-- The same actual genus witness transports the primitive polynomial at infinity. -/
theorem IsSameGenus.nonempty_binaryPrimitivePolynomialOver_real_isometry
    {K L : PositiveDefiniteIntegralLattice 2} (h : K.IsSameGenus L) :
    Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
      (L.binaryPrimitivePolynomialOver ℝ)) := by
  obtain ⟨U, hU, hform⟩ := h.2
  exact ⟨binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L h.binaryContent_eq U hU hform⟩

/-- Exact local normalization of the actual genus. Equality of content and
primitive polynomial isometries at all places recover the original genus. -/
theorem isSameGenus_iff_binaryPrimitivePolynomialOver_local_isometries
    (K L : PositiveDefiniteIntegralLattice 2) :
    K.IsSameGenus L ↔ K.binaryContent = L.binaryContent ∧
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        Nonempty ((K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
          (L.binaryPrimitivePolynomialOver ℤ_[p]))) ∧
      Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
        (L.binaryPrimitivePolynomialOver ℝ)) := by
  constructor
  · intro h
    exact ⟨h.binaryContent_eq,
      h.nonempty_binaryPrimitivePolynomialOver_padic_isometry,
      h.nonempty_binaryPrimitivePolynomialOver_real_isometry⟩
  · rintro ⟨hg, hfinite, hinfty⟩
    constructor
    · intro p hp
      exact (exists_matrix_iff_nonempty_binaryPrimitivePolynomialOver_isometry K L hg).mpr
        (hfinite p)
    · exact (exists_matrix_iff_nonempty_binaryPrimitivePolynomialOver_isometry K L hg).mpr hinfty

/-- A primitive integral binary polynomial has a value not divisible by any given prime. -/
lemma exists_prime_not_dvd_binaryPrimitivePolynomial (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∃ x : Fin 2 → ℤ, ¬ (p : ℤ) ∣ K.binaryPrimitivePolynomial x := by
  by_contra hn
  push Not at hn
  let a := K.pairingMatrix 0 0 / (K.binaryContent : ℤ)
  let b := (2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)
  let c := K.pairingMatrix 1 1 / (K.binaryContent : ℤ)
  have ha : (p : ℤ) ∣ a := by
    simpa [binaryPrimitivePolynomial_apply, a] using hn ![1, 0]
  have hc : (p : ℤ) ∣ c := by
    simpa [binaryPrimitivePolynomial_apply, c] using hn ![0, 1]
  have habc : (p : ℤ) ∣ a + b + c := by
    simpa [binaryPrimitivePolynomial_apply, a, b, c] using hn ![1, 1]
  have hb : (p : ℤ) ∣ b := by simpa using dvd_sub (dvd_sub habc hc) ha
  have hbc : p ∣ Int.gcd b c := Int.dvd_gcd hb hc
  have hgcd : p ∣ Int.gcd a (Int.gcd b c : ℤ) :=
    Int.dvd_gcd ha (by exact_mod_cast hbc)
  have hprim : Int.gcd a (Int.gcd b c : ℤ) = 1 :=
    K.binaryPrimitivePolynomial_coefficients_gcd_eq_one
  rw [hprim] at hgcd
  exact hp.out.ne_one (Nat.dvd_one.mp hgcd)

/-- The scalar-extended primitive polynomial represents a p-adic unit, including at 2. -/
theorem binaryPrimitivePolynomialOver_padic_exists_unit (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ v : Fin 2 → ℤ_[p], IsUnit (K.binaryPrimitivePolynomialOver ℤ_[p] v) := by
  obtain ⟨x, hx⟩ := K.exists_prime_not_dvd_binaryPrimitivePolynomial p
  refine ⟨fun i => (x i : ℤ_[p]), ?_⟩
  rw [binaryPrimitivePolynomialOver_intCast]
  by_contra hu
  rw [PadicInt.not_isUnit_iff, PadicInt.norm_intCast_lt_one_iff] at hu
  exact hx hu

/-- Every actual primitive p-adic binary polynomial admits an integral,
involutive norm isometry of determinant -1, including at the dyadic prime. -/
theorem binaryPrimitivePolynomialOver_padic_exists_reflection (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (v : Fin 2 → ℤ_[p])
      (e : (K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
        (K.binaryPrimitivePolynomialOver ℤ_[p])),
      IsUnit (K.binaryPrimitivePolynomialOver ℤ_[p] v) ∧
      e v = -v ∧ Function.Involutive e ∧
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = -1 := by
  obtain ⟨v, hv⟩ := K.binaryPrimitivePolynomialOver_padic_exists_unit p
  obtain ⟨u, hu⟩ := hv
  refine ⟨v, QuadraticMap.unitValueReflection _ v u hu.symm, ⟨u, hu⟩, ?_, ?_, ?_⟩
  · exact QuadraticMap.unitValueReflection_apply_self _ v u hu.symm
  · exact QuadraticMap.unitValueReflection_involutive _ v u hu.symm
  · exact QuadraticMap.unitValueReflection_det_fin_two _ v u hu.symm

/-- The actual genus yields determinant-one primitive polynomial isometries
at every finite prime. A unit-value reflection corrects the negative sign. -/
theorem IsSameGenus.exists_binaryPrimitivePolynomialOver_padic_proper_isometry
    {K L : PositiveDefiniteIntegralLattice 2} (h : K.IsSameGenus L)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ e : (K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
      (L.binaryPrimitivePolynomialOver ℤ_[p]),
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = 1 := by
  obtain ⟨U, hU, hform⟩ := h.1 p
  let e := binaryPrimitivePolynomialOverIsometryEquivOfMatrix K L h.binaryContent_eq U hU hform
  have hmatrix : LinearMap.toMatrix' e.toLinearEquiv.toLinearMap = U :=
    binaryPrimitivePolynomialOverIsometryEquivOfMatrix_toMatrix K L h.binaryContent_eq U hU hform
  have hdet := pairingDeterminant_eq_det_sq_mul_of_local_isometry_matrix K L p U hform
  rw [← pairingDeterminant_eq_of_isSameGenus K L h] at hdet
  have hne : (K.pairingDeterminant : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (ne_of_gt K.pairingDeterminant_pos)
  have hsq : U.det ^ 2 = 1 := mul_right_cancel₀ hne (by simpa using hdet.symm)
  rcases sq_eq_one_iff.mp hsq with hpos | hneg
  · exact ⟨e, by rw [hmatrix, hpos]⟩
  · obtain ⟨v, r, _, _, _, hr⟩ := L.binaryPrimitivePolynomialOver_padic_exists_reflection p
    refine ⟨e.trans r, ?_⟩
    have hcomp : LinearMap.toMatrix' (e.trans r).toLinearEquiv.toLinearMap =
        LinearMap.toMatrix' r.toLinearEquiv.toLinearMap *
          LinearMap.toMatrix' e.toLinearEquiv.toLinearMap := by
      change LinearMap.toMatrix' (r.toLinearEquiv.toLinearMap.comp e.toLinearEquiv.toLinearMap) = _
      exact LinearMap.toMatrix'_comp _ _
    rw [hcomp, Matrix.det_mul, hr, hmatrix, hneg]
    ring

/-- The actual genus is exactly fixed content together with proper primitive
isometries at every finite prime and the original real-place condition. -/
theorem isSameGenus_iff_binaryPrimitivePolynomialOver_proper_local_isometries
    (K L : PositiveDefiniteIntegralLattice 2) :
    K.IsSameGenus L ↔ K.binaryContent = L.binaryContent ∧
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        ∃ e : (K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
          (L.binaryPrimitivePolynomialOver ℤ_[p]),
          (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = 1) ∧
      Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
        (L.binaryPrimitivePolynomialOver ℝ)) := by
  constructor
  · intro h
    exact ⟨h.binaryContent_eq,
      h.exists_binaryPrimitivePolynomialOver_padic_proper_isometry,
      h.nonempty_binaryPrimitivePolynomialOver_real_isometry⟩
  · rintro ⟨hg, hfinite, hinfty⟩
    apply (isSameGenus_iff_binaryPrimitivePolynomialOver_local_isometries K L).mpr
    refine ⟨hg, ?_, hinfty⟩
    intro p hp
    obtain ⟨e, _⟩ := hfinite p
    exact ⟨e⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms QuadraticMap.unitValueReflection
#assert_standard_axioms QuadraticMap.unitValueReflection_apply
#assert_standard_axioms QuadraticMap.unitValueReflection_apply_self
#assert_standard_axioms QuadraticMap.unitValueReflection_involutive
#assert_standard_axioms QuadraticMap.unitValueReflection_det_fin_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_apply
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_intCast
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_int
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_norm_eq_content_mul_primitive_over
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_matrix_congruence_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOverIsometryEquivOfMatrix
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOverIsometryEquivOfMatrix_apply
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOverIsometryEquivOfMatrix_toMatrix
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_matrix_iff_nonempty_binaryPrimitivePolynomialOver_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.isGlobalIsometry_iff_binaryPrimitivePolynomial_isometry_of_content_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsSameGenus.nonempty_binaryPrimitivePolynomialOver_padic_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsSameGenus.nonempty_binaryPrimitivePolynomialOver_real_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryPrimitivePolynomialOver_local_isometries
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_prime_not_dvd_binaryPrimitivePolynomial
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_padic_exists_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_padic_exists_reflection
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsSameGenus.exists_binaryPrimitivePolynomialOver_padic_proper_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryPrimitivePolynomialOver_proper_local_isometries
