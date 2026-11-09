import SMSFormula.Genus
import SMSFormula.GenusDeterminantInvariants
import SMSFormula.StandardAxiomsGuard
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Binary value divisibility and exact polynomial scaling

These lemmas work with the norm polynomial of a symmetric integral matrix.
The middle coefficient is twice the off-diagonal entry. After scalar division,
the polynomial can have an odd middle coefficient; no integral symmetric matrix
for the divided polynomial is assumed. The ring statements also apply at 2.
-/

open Matrix

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The three coefficients of the binary norm polynomial of a symmetric matrix. -/
lemma dotProduct_mulVec_fin_two (F : Matrix (Fin 2) (Fin 2) R)
    (hF : F.IsSymm) (x : Fin 2 → R) :
    dotProduct x (F.mulVec x) =
      F 0 0 * x 0 ^ 2 + (2 * F 0 1) * x 0 * x 1 + F 1 1 * x 1 ^ 2 := by
  have h10 : F 1 0 = F 0 1 := hF.apply 0 1
  simp only [dotProduct, mulVec, Fin.sum_univ_two]
  rw [h10]
  ring

/-- Value divisibility is exactly coefficient divisibility, over any commutative ring. -/
lemma forall_dvd_dotProduct_mulVec_fin_two_iff
    (F : Matrix (Fin 2) (Fin 2) R) (hF : F.IsSymm) (d : R) :
    (∀ x : Fin 2 → R, d ∣ dotProduct x (F.mulVec x)) ↔
      d ∣ F 0 0 ∧ d ∣ 2 * F 0 1 ∧ d ∣ F 1 1 := by
  simp_rw [dotProduct_mulVec_fin_two F hF]
  constructor
  · intro h
    have ha : d ∣ F 0 0 := by simpa using h ![1, 0]
    have hc : d ∣ F 1 1 := by simpa using h ![0, 1]
    have habc : d ∣ F 0 0 + 2 * F 0 1 + F 1 1 := by simpa using h ![1, 1]
    have hb : d ∣ 2 * F 0 1 := by
      simpa using dvd_sub (dvd_sub habc hc) ha
    exact ⟨ha, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩ x
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left hb _) _)) (dvd_mul_of_dvd_left hc _)

/-- Polynomial scaling uses the mixed coefficient itself, without halving it. -/
lemma dotProduct_mulVec_fin_two_eq_scalar_polynomial
    (F : Matrix (Fin 2) (Fin 2) R) (hF : F.IsSymm)
    (g a b c : R) (ha : F 0 0 = g * a) (hb : 2 * F 0 1 = g * b)
    (hc : F 1 1 = g * c) (x : Fin 2 → R) :
    dotProduct x (F.mulVec x) =
      g * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) := by
  rw [dotProduct_mulVec_fin_two F hF, ha, hb, hc]
  ring

private lemma binary_norm_matrix_congr
    (G U : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    dotProduct (U.mulVec x) (G.mulVec (U.mulVec x)) =
      dotProduct x ((U.transpose * G * U).mulVec x) := by
  simp only [dotProduct, mulVec, mul_apply, transpose_apply, Fin.sum_univ_two]
  ring

/-- An actual invertible matrix congruence preserves divisibility of all norm values. -/
lemma forall_dvd_dotProduct_mulVec_fin_two_congr
    (F G U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U)
    (h : U.transpose * G * U = F) (d : R) :
    (∀ x, d ∣ dotProduct x (F.mulVec x)) ↔
      (∀ x, d ∣ dotProduct x (G.mulVec x)) := by
  rcases hU with ⟨u, rfl⟩
  let T : Matrix (Fin 2) (Fin 2) R := ↑u
  let V : Matrix (Fin 2) (Fin 2) R := ↑(u⁻¹)
  have hTV : T * V = 1 := by simp [T, V]
  have hform : T.transpose * G * T = F := h
  have hinv : V.transpose * F * V = G := by
    calc
      _ = (T * V).transpose * G * (T * V) := by
        rw [← hform]
        simp only [transpose_mul, mul_assoc]
      _ = G := by rw [hTV]; simp
  constructor
  · intro hf x
    have heq := binary_norm_matrix_congr F V x
    rw [hinv] at heq
    exact heq ▸ hf (V.mulVec x)
  · intro hg x
    have heq := binary_norm_matrix_congr G T x
    rw [hform] at heq
    exact heq ▸ hg (T.mulVec x)

end Matrix

namespace PositiveDefiniteIntegralLattice

/-- The coefficient content test for the original integral lattice, not its polar form. -/
lemma forall_dvd_quadForm_rank_two_iff (K : PositiveDefiniteIntegralLattice 2) (d : ℤ) :
    (∀ x, d ∣ K.quadForm x) ↔
      d ∣ K.pairingMatrix 0 0 ∧ d ∣ 2 * K.pairingMatrix 0 1 ∧ d ∣ K.pairingMatrix 1 1 := by
  simp_rw [quadForm_eq_dotProduct]
  exact Matrix.forall_dvd_dotProduct_mulVec_fin_two_iff K.pairingMatrix K.form_symm d

/-- The same value-ideal test over the actual p-adic carrier, including p = 2. -/
lemma forall_dvd_padic_quadForm_rank_two_iff (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] (d : ℤ_[p]) :
    (∀ x, d ∣ dotProduct x ((K.pairingMatrix_padic p).mulVec x)) ↔
      d ∣ (K.pairingMatrix 0 0 : ℤ_[p]) ∧
      d ∣ 2 * (K.pairingMatrix 0 1 : ℤ_[p]) ∧
      d ∣ (K.pairingMatrix 1 1 : ℤ_[p]) := by
  have hs : (K.pairingMatrix_padic p).IsSymm := by
    ext i j
    simp only [transpose_apply, pairingMatrix_padic, map_apply]
    rw [K.form_symm.apply i j]
  exact Matrix.forall_dvd_dotProduct_mulVec_fin_two_iff (K.pairingMatrix_padic p) hs d

/-- Local isometry preserves the coefficient-content divisibility test on the
actual p-adic carrier. There is no restriction on the prime or on the divisor. -/
lemma IsLocallyIsometricAt.binary_coefficient_dvd_iff
    {K L : PositiveDefiniteIntegralLattice 2} {p : ℕ} [Fact (Nat.Prime p)]
    (h : K.IsLocallyIsometricAt L p) (d : ℤ_[p]) :
    (d ∣ (K.pairingMatrix 0 0 : ℤ_[p]) ∧
      d ∣ 2 * (K.pairingMatrix 0 1 : ℤ_[p]) ∧ d ∣ (K.pairingMatrix 1 1 : ℤ_[p])) ↔
    (d ∣ (L.pairingMatrix 0 0 : ℤ_[p]) ∧
      d ∣ 2 * (L.pairingMatrix 0 1 : ℤ_[p]) ∧ d ∣ (L.pairingMatrix 1 1 : ℤ_[p])) := by
  rw [← forall_dvd_padic_quadForm_rank_two_iff K p d,
    ← forall_dvd_padic_quadForm_rank_two_iff L p d]
  obtain ⟨U, hU, hform⟩ := h
  exact Matrix.forall_dvd_dotProduct_mulVec_fin_two_congr
    (K.pairingMatrix_padic p) (L.pairingMatrix_padic p) U hU hform d

/-- Positive coefficient content of the actual binary norm polynomial. -/
def binaryContent (K : PositiveDefiniteIntegralLattice 2) : ℕ :=
  Int.gcd (K.pairingMatrix 0 0)
    (Int.gcd (2 * K.pairingMatrix 0 1) (K.pairingMatrix 1 1) : ℤ)

/-- The integer gcd represents exactly the three coefficient divisibility tests. -/
lemma dvd_binaryContent_iff (K : PositiveDefiniteIntegralLattice 2) (d : ℕ) :
    d ∣ K.binaryContent ↔
      (d : ℤ) ∣ K.pairingMatrix 0 0 ∧
      (d : ℤ) ∣ 2 * K.pairingMatrix 0 1 ∧ (d : ℤ) ∣ K.pairingMatrix 1 1 := by
  unfold binaryContent
  constructor
  · intro hd
    obtain ⟨ha, hbc⟩ := Int.dvd_gcd_iff.mp hd
    have hbc' : d ∣ Int.gcd (2 * K.pairingMatrix 0 1) (K.pairingMatrix 1 1) := by
      exact_mod_cast hbc
    exact ⟨ha, Int.dvd_gcd_iff.mp hbc'⟩
  · rintro ⟨ha, hb, hc⟩
    apply Int.dvd_gcd ha
    exact_mod_cast (Int.dvd_gcd hb hc)

/-- Positive definiteness makes coefficient content strictly positive. -/
lemma binaryContent_pos (K : PositiveDefiniteIntegralLattice 2) : 0 < K.binaryContent := by
  have ha := K.quadForm_pos (x := ![1, 0]) (by decide)
  rw [quadForm_eq_dotProduct, Matrix.dotProduct_mulVec_fin_two _ K.form_symm] at ha
  have ha' : 0 < K.pairingMatrix 0 0 := by simpa using ha
  exact Int.gcd_pos_of_ne_zero_left _ (ne_of_gt ha')

/-- Actual local isometry preserves the integer content's prime-power profile. -/
lemma IsLocallyIsometricAt.binaryContent_prime_pow_dvd_iff
    {K L : PositiveDefiniteIntegralLattice 2} {p : ℕ} [Fact (Nat.Prime p)]
    (h : K.IsLocallyIsometricAt L p) (k : ℕ) :
    p ^ k ∣ K.binaryContent ↔ p ^ k ∣ L.binaryContent := by
  rw [dvd_binaryContent_iff, dvd_binaryContent_iff]
  have hh := h.binary_coefficient_dvd_iff ((p : ℤ_[p]) ^ k)
  have hm (z : ℤ) : 2 * (z : ℤ_[p]) = ((2 * z : ℤ) : ℤ_[p]) := by simp
  rw [hm, hm] at hh
  simpa only [PadicInt.pow_p_dvd_int_iff, Nat.cast_pow] using hh

/-- The coefficient gcd is constant across the actual genus, at all primes. -/
theorem IsSameGenus.binaryContent_eq {K L : PositiveDefiniteIntegralLattice 2}
    (h : K.IsSameGenus L) : K.binaryContent = L.binaryContent := by
  have hK : (K.binaryContent : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt K.binaryContent_pos)
  have hL : (L.binaryContent : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.binaryContent_pos)
  have hpow : ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ),
      (p ^ k : ℤ) ∣ (K.binaryContent : ℤ) ↔
        (p ^ k : ℤ) ∣ (L.binaryContent : ℤ) := by
    intro p hp k
    exact_mod_cast (h.1 p).binaryContent_prime_pow_dvd_iff k
  simpa only [Int.natAbs_natCast] using
    int_natAbs_eq_of_prime_pow_dvd_iff _ _ hK hL hpow

/-- The primitive polynomial on the same integer coordinate module. Its upper
coefficient matrix need not be symmetric, so its mixed coefficient may be odd. -/
def binaryPrimitivePolynomial (K : PositiveDefiniteIntegralLattice 2) :
    QuadraticForm ℤ (Fin 2 → ℤ) :=
  (!![K.pairingMatrix 0 0 / (K.binaryContent : ℤ),
      (2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ);
      0, K.pairingMatrix 1 1 / (K.binaryContent : ℤ)] :
        Matrix (Fin 2) (Fin 2) ℤ).toQuadraticForm'

lemma binaryPrimitivePolynomial_apply (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → ℤ) :
    K.binaryPrimitivePolynomial x =
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) * x 0 ^ 2 +
      ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)) * x 0 * x 1 +
      (K.pairingMatrix 1 1 / (K.binaryContent : ℤ)) * x 1 ^ 2 := by
  simp only [binaryPrimitivePolynomial, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Exact division by the proved content, without changing the integer carrier. -/
theorem quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial
    (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → ℤ) :
    K.quadForm x = (K.binaryContent : ℤ) * K.binaryPrimitivePolynomial x := by
  have hd := (dvd_binaryContent_iff K K.binaryContent).mp (dvd_refl _)
  rw [quadForm_eq_dotProduct, binaryPrimitivePolynomial_apply]
  exact Matrix.dotProduct_mulVec_fin_two_eq_scalar_polynomial K.pairingMatrix K.form_symm
    (K.binaryContent : ℤ) _ _ _
    (Int.mul_ediv_cancel' hd.1).symm
    (Int.mul_ediv_cancel' hd.2.1).symm
    (Int.mul_ediv_cancel' hd.2.2).symm x

/-- The three divided polynomial coefficients have gcd one. -/
theorem binaryPrimitivePolynomial_coefficients_gcd_eq_one (K : PositiveDefiniteIntegralLattice 2) :
    Int.gcd (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
      (Int.gcd ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
        (K.pairingMatrix 1 1 / (K.binaryContent : ℤ)) : ℤ) = 1 := by
  let g := K.binaryContent
  let a := K.pairingMatrix 0 0 / (g : ℤ)
  let b := (2 * K.pairingMatrix 0 1) / (g : ℤ)
  let c := K.pairingMatrix 1 1 / (g : ℤ)
  have hd := (dvd_binaryContent_iff K g).mp (dvd_refl _)
  have ha : K.pairingMatrix 0 0 = (g : ℤ) * a := (Int.mul_ediv_cancel' hd.1).symm
  have hb : 2 * K.pairingMatrix 0 1 = (g : ℤ) * b := (Int.mul_ediv_cancel' hd.2.1).symm
  have hc : K.pairingMatrix 1 1 = (g : ℤ) * c := (Int.mul_ediv_cancel' hd.2.2).symm
  have hbc : (Int.gcd (2 * K.pairingMatrix 0 1) (K.pairingMatrix 1 1) : ℤ) =
      (g : ℤ) * (Int.gcd b c : ℤ) := by
    rw [hb, hc, Int.gcd_mul_left]
    simp
  have hg : g = g * Int.gcd a (Int.gcd b c : ℤ) := by
    calc
      g = Int.gcd (K.pairingMatrix 0 0)
          (Int.gcd (2 * K.pairingMatrix 0 1) (K.pairingMatrix 1 1) : ℤ) := rfl
      _ = Int.gcd ((g : ℤ) * a) ((g : ℤ) * (Int.gcd b c : ℤ)) := by rw [ha, hbc]
      _ = g * Int.gcd a (Int.gcd b c : ℤ) := by rw [Int.gcd_mul_left]; simp
  change Int.gcd a (Int.gcd b c : ℤ) = 1
  exact Nat.eq_of_mul_eq_mul_left K.binaryContent_pos (by simpa using hg.symm)

/-- Content division gives a positive definite integral polynomial. -/
theorem binaryPrimitivePolynomial_posDef (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryPrimitivePolynomial.PosDef := by
  intro x hx
  have hpos := K.quadForm_pos hx
  rw [quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial] at hpos
  have hg : (0 : ℤ) < K.binaryContent := by exact_mod_cast K.binaryContent_pos
  exact (mul_pos_iff_of_pos_left hg).mp hpos

/-- An actual global integral isometry induces a Mathlib isometry of the
primitive polynomials, using the same coordinate matrix. -/
noncomputable def binaryPrimitivePolynomialIsometryEquivOfMatrix
    (K L : PositiveDefiniteIntegralLattice 2) (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U) (hform : U.transpose * L.pairingMatrix * U = K.pairingMatrix) :
    K.binaryPrimitivePolynomial.IsometryEquiv L.binaryPrimitivePolynomial where
  toLinearEquiv := Matrix.toLinearEquiv' U hU.invertible
  map_app' x := by
    have hg : K.binaryContent = L.binaryContent :=
      (isSameGenus_of_isGlobalIsometry ⟨U, hU, hform⟩).binaryContent_eq
    have hval : L.quadForm (U.mulVec x) = K.quadForm x := by
      rw [quadForm_eq_dotProduct, quadForm_eq_dotProduct]
      have heq := Matrix.binary_norm_matrix_congr L.pairingMatrix U x
      rwa [hform] at heq
    rw [quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial,
      quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial, ← hg] at hval
    have hgne : (K.binaryContent : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt K.binaryContent_pos)
    have hprimitive := mul_left_cancel₀ hgne hval
    simpa [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply] using hprimitive

/-- Content division preserves the coordinate action of the original isometry. -/
lemma binaryPrimitivePolynomialIsometryEquivOfMatrix_apply
    (K L : PositiveDefiniteIntegralLattice 2) (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : IsUnit U) (hform : U.transpose * L.pairingMatrix * U = K.pairingMatrix)
    (x : Fin 2 → ℤ) :
    binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hform x = U.mulVec x := by
  change Matrix.toLinearEquiv' U hU.invertible x = U.mulVec x
  rfl

end PositiveDefiniteIntegralLattice

#assert_standard_axioms Matrix.dotProduct_mulVec_fin_two
#assert_standard_axioms Matrix.forall_dvd_dotProduct_mulVec_fin_two_iff
#assert_standard_axioms Matrix.dotProduct_mulVec_fin_two_eq_scalar_polynomial
#assert_standard_axioms Matrix.forall_dvd_dotProduct_mulVec_fin_two_congr
#assert_standard_axioms PositiveDefiniteIntegralLattice.forall_dvd_quadForm_rank_two_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.forall_dvd_padic_quadForm_rank_two_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsLocallyIsometricAt.binary_coefficient_dvd_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryContent
#assert_standard_axioms PositiveDefiniteIntegralLattice.dvd_binaryContent_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryContent_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsLocallyIsometricAt.binaryContent_prime_pow_dvd_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsSameGenus.binaryContent_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomial
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomial_apply
#assert_standard_axioms PositiveDefiniteIntegralLattice.quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomial_coefficients_gcd_eq_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomial_posDef
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialIsometryEquivOfMatrix
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialIsometryEquivOfMatrix_apply
