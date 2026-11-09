import SMSFormula.BinaryPrimeIdealFactorization

/-!
# Coprime multiplicativity of the actual ideal-norm coefficients

Multiplication is a bijection of the actual ideal fibers. The scalar
norm bounds and coprimality force the two factors to have the exact norms.
-/

namespace BinaryNormIdeal

section NormFibers

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
  [Module.Free ℤ B] [Module.Finite ℤ B] [CharZero B]

omit [Module.Finite ℤ B] in
/-- Coprime actual norms force the original ideals to be coprime. -/
theorem ideal_isCoprime_of_absNorm_coprime {P Q : Ideal B}
    (h : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) : IsCoprime P Q := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.absNorm_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes h
    (Ideal.absNorm_dvd_absNorm_of_le le_sup_left)
    (Ideal.absNorm_dvd_absNorm_of_le le_sup_right)

omit [Module.Finite ℤ B] in
/-- The actual factors of a coprime-norm product are unique. -/
theorem ideal_norm_coprime_product_injective (m n : ℕ) (hm : m ≠ 0)
    (hn : n ≠ 0) (hc : m.Coprime n) {P Q R S : Ideal B}
    (hP : Ideal.absNorm P=m) (hQ : Ideal.absNorm Q=n)
    (hR : Ideal.absNorm R=m) (hS : Ideal.absNorm S=n)
    (hprod : P*Q=R*S) : P=R ∧ Q=S := by
  have hpS : IsCoprime P S := ideal_isCoprime_of_absNorm_coprime (by rwa [hP,hS])
  have hd : P ∣ R := hpS.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right P Q)
  have hPR := (ideal_eq_of_dvd_of_absNorm_eq hd (hP.trans hR.symm) (hR ▸ hm)).symm
  have hQR : IsCoprime Q R := ideal_isCoprime_of_absNorm_coprime (by rw [hQ,hR]; exact hc.symm)
  have hdQ : Q ∣ S := hQR.dvd_of_dvd_mul_left (hprod ▸ dvd_mul_left Q P)
  exact ⟨hPR,(ideal_eq_of_dvd_of_absNorm_eq hdQ (hQ.trans hS.symm) (hS ▸ hn)).symm⟩

/-- Scalar divisibility splits any actual norm-mn ideal into factors
with the exact norms m,n. No prime-ideal splitting premise is supplied. -/
theorem exists_ideal_norm_coprime_product (e : Module.Basis (Fin 2) ℤ B)
    (m n : ℕ) (hc : m.Coprime n) {J : Ideal B} (hJ : Ideal.absNorm J=m*n) :
    ∃ P Q : Ideal B, Ideal.absNorm P=m ∧ Ideal.absNorm Q=n ∧ J=P*Q := by
  have hd := normPrimeIdeal_dvd_span (m*n) hJ
  rw [Nat.cast_mul,← Ideal.span_singleton_mul_span_singleton] at hd
  obtain ⟨P,Q,hP,hQ,hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have hm := map_dvd Ideal.absNorm hP
  have hn := map_dvd Ideal.absNorm hQ
  rw [absNorm_span_nat_rank_two e] at hm hn
  have heq := congrArg Ideal.absNorm hprod
  rw [hJ,map_mul] at heq
  have hPn : (Ideal.absNorm P).Coprime n := (hc.pow_left 2).coprime_dvd_left hm
  have hQm : (Ideal.absNorm Q).Coprime m := (hc.symm.pow_left 2).coprime_dvd_left hn
  have hmQ : m.Coprime (Ideal.absNorm Q) := (hc.pow_right 2).coprime_dvd_right hn
  have hnP : n.Coprime (Ideal.absNorm P) := (hc.symm.pow_right 2).coprime_dvd_right hm
  have hdP : Ideal.absNorm P ∣ m := hPn.dvd_of_dvd_mul_right ⟨Ideal.absNorm Q,heq⟩
  have hdQ : Ideal.absNorm Q ∣ n := hQm.dvd_of_dvd_mul_left ⟨Ideal.absNorm P,
    by rw [mul_comm (Ideal.absNorm Q)]; exact heq⟩
  have hdM : m ∣ Ideal.absNorm P := hmQ.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right m n)
  have hdN : n ∣ Ideal.absNorm Q := hnP.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left n m)
  exact ⟨P,Q,dvd_antisymm hdP hdM,dvd_antisymm hdQ hdN,hprod⟩

/-- Multiplication gives a bijection between the actual coprime norm
fibers and the norm-product fiber. -/
noncomputable def coprimeNormIdealsEquiv (e : Module.Basis (Fin 2) ℤ B)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hc : m.Coprime n) :
    ({P : Ideal B // Ideal.absNorm P=m} × {Q : Ideal B // Ideal.absNorm Q=n}) ≃
      {J : Ideal B // Ideal.absNorm J=m*n} := by
  let f : ({P : Ideal B // Ideal.absNorm P=m} × {Q : Ideal B // Ideal.absNorm Q=n}) →
      {J : Ideal B // Ideal.absNorm J=m*n} := fun x =>
    ⟨x.1.val*x.2.val,by rw [map_mul,x.1.prop,x.2.prop]⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    obtain ⟨hP,hQ⟩ := ideal_norm_coprime_product_injective m n hm hn hc
      x.1.prop x.2.prop y.1.prop y.2.prop (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext hP) (Subtype.ext hQ)
  · intro J
    obtain ⟨P,Q,hP,hQ,hprod⟩ := exists_ideal_norm_coprime_product e m n hc J.prop
    exact ⟨(⟨P,hP⟩,⟨Q,hQ⟩),Subtype.ext hprod.symm⟩

/-- Literal norm-ideal counts multiply for coprime nonzero norms. -/
theorem card_normIdeals_mul_of_coprime (e : Module.Basis (Fin 2) ℤ B)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hc : m.Coprime n) :
    Nat.card {J : Ideal B // Ideal.absNorm J=m*n} =
      Nat.card {P : Ideal B // Ideal.absNorm P=m} *
        Nat.card {Q : Ideal B // Ideal.absNorm Q=n} := by
  rw [← Nat.card_congr (coprimeNormIdealsEquiv e m n hm hn hc),Nat.card_prod]

omit [Module.Finite ℤ B] in
/-- The actual coefficient at one is the unit ideal singleton. -/
theorem card_normIdeals_one : Nat.card {J : Ideal B // Ideal.absNorm J=1}=1 := by
  simp only [Ideal.absNorm_eq_one_iff]
  exact Nat.card_unique

/-- The all-ideal sequence has coefficient one at zero, from the zero
ideal. It must be normalized before an arithmetic-function comparison. -/
theorem card_normIdeals_zero : Nat.card {J : Ideal B // Ideal.absNorm J=0}=1 := by
  simp only [Ideal.absNorm_eq_zero_iff]
  exact Nat.card_unique

end NormFibers

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- Coprime multiplicativity of the same field's actual Dedekind-zeta
coefficient sequence. The input norms are explicitly nonzero. -/
theorem card_maximalNormIdeals_mul_of_coprime (hD : b^2-4*a*c<0)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hc : m.Coprime n) :
    letI := fractionNumberField a b c hD
    Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=m*n} =
      Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
        Ideal.absNorm J=m} *
      Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
        Ideal.absNorm J=n} := by
  letI := fractionNumberField a b c hD
  exact card_normIdeals_mul_of_coprime (maximalOrderBasisOne a b c hD) m n hm hn hc

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.ideal_isCoprime_of_absNorm_coprime
#assert_standard_axioms BinaryNormIdeal.ideal_norm_coprime_product_injective
#assert_standard_axioms BinaryNormIdeal.exists_ideal_norm_coprime_product
#assert_standard_axioms BinaryNormIdeal.coprimeNormIdealsEquiv
#assert_standard_axioms BinaryNormIdeal.card_normIdeals_mul_of_coprime
#assert_standard_axioms BinaryNormIdeal.card_maximalNormIdeals_mul_of_coprime

#assert_standard_axioms BinaryNormIdeal.card_normIdeals_one
#assert_standard_axioms BinaryNormIdeal.card_normIdeals_zero
