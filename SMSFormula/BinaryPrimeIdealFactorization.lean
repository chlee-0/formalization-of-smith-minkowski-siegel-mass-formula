import SMSFormula.BinaryPrimeNormIdeals

/-!
# Literal factorization of a rational prime in the actual maximal order

The norm of pB is p^2. Its actual norm-p ideals determine the three
factorizations. No splitting type or ramification certificate is assumed.
-/

namespace BinaryNormIdeal

section IdealNorms

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
  [Module.Free ℤ B] [Module.Finite ℤ B] [CharZero B]

omit [Module.Finite ℤ B] in
/-- A divisor with the same nonzero absolute norm is the original ideal. -/
theorem ideal_eq_of_dvd_of_absNorm_eq {I J : Ideal B} (hd : J ∣ I)
    (hn : Ideal.absNorm J=Ideal.absNorm I) (hI : Ideal.absNorm I ≠ 0) : I=J := by
  obtain ⟨L,hL⟩ := hd
  have hJ : Ideal.absNorm J ≠ 0 := hn.trans_ne hI
  have hnorm : Ideal.absNorm J=Ideal.absNorm J*Ideal.absNorm L := by
    simpa only [hL,map_mul] using hn
  have hunit : Ideal.absNorm L=1 := by
    apply mul_left_cancel₀ hJ
    simpa only [mul_one] using hnorm.symm
  rw [Ideal.absNorm_eq_one_iff] at hunit
  simpa only [hunit,Ideal.mul_top] using hL

/-- The original rank-two integer basis computes the scalar ideal norm. -/
theorem absNorm_span_nat_rank_two (e : Module.Basis (Fin 2) ℤ B) (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : B)})=n^2 := by
  rw [Ideal.absNorm_span_natCast,Module.finrank_eq_card_basis e,Fintype.card_fin]

omit [Module.Finite ℤ B] in
/-- Every actual ideal of norm p divides the literal scalar ideal pB. -/
theorem normPrimeIdeal_dvd_span (p : ℕ) {P : Ideal B} (hP : Ideal.absNorm P=p) :
    P ∣ Ideal.span {(p : B)} := by
  rw [Ideal.dvd_iff_le]
  simpa only [hP] using Ideal.span_singleton_absNorm_le P

/-- A norm-p ideal leaves an actual second norm-p factor of pB. -/
theorem exists_normPrime_factor_pair (e : Module.Basis (Fin 2) ℤ B)
    (p : ℕ) [Fact p.Prime] {P : Ideal B} (hP : Ideal.absNorm P=p) :
    ∃ Q : Ideal B, Ideal.absNorm Q=p ∧ Ideal.span {(p : B)}=P*Q := by
  obtain ⟨Q,hQ⟩ := normPrimeIdeal_dvd_span p hP
  refine ⟨Q,?_,hQ⟩
  have h := congrArg Ideal.absNorm hQ
  rw [absNorm_span_nat_rank_two e,map_mul,hP,pow_two] at h
  exact mul_left_cancel₀ (Fact.out : p.Prime).ne_zero h.symm

/-- Norms of nonzero prime factors of pB are p or p^2. This is actual
norm divisibility, not a residue-degree premise. -/
theorem absNorm_prime_factor_span (e : Module.Basis (Fin 2) ℤ B)
    (p : ℕ) [Fact p.Prime] {P : Ideal B} (hP : Prime P)
    (hd : P ∣ Ideal.span {(p : B)}) : Ideal.absNorm P=p ∨ Ideal.absNorm P=p^2 := by
  have hdiv := map_dvd Ideal.absNorm hd
  rw [absNorm_span_nat_rank_two e] at hdiv
  obtain ⟨k,hk,heq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdiv
  have hone : Ideal.absNorm P ≠ 1 := by
    intro h
    exact hP.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  interval_cases k <;> simp_all

/-- If there are no actual norm-p ideals, the literal pB is prime. -/
theorem span_prime_of_no_normPrimeIdeal (e : Module.Basis (Fin 2) ℤ B)
    (p : ℕ) [Fact p.Prime] (hno : ∀ P : Ideal B, Ideal.absNorm P ≠ p) :
    Prime (Ideal.span {(p : B)}) := by
  have hn : Ideal.absNorm (Ideal.span {(p : B)})=p^2 := absNorm_span_nat_rank_two e p
  have hzero : Ideal.span {(p : B)} ≠ 0 := by
    intro hz
    have h := congrArg Ideal.absNorm hz
    rw [hn,map_zero] at h
    exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero h
  have hunit : ¬IsUnit (Ideal.span {(p : B)}) := by
    intro hu
    rw [Ideal.isUnit_iff] at hu
    have h := congrArg Ideal.absNorm hu
    rw [hn,Ideal.absNorm_top] at h
    nlinarith [(Fact.out : p.Prime).two_le]
  obtain ⟨P,hP,hd⟩ := WfDvdMonoid.exists_irreducible_factor hunit hzero
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hP
  have hnorm := (absNorm_prime_factor_span e p hp hd).resolve_left (hno P)
  have heq := ideal_eq_of_dvd_of_absNorm_eq hd (hnorm.trans hn.symm)
    (by rw [hn]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  rwa [heq]

/-- If the actual norm-p carrier is a singleton, pB is its ideal squared. -/
theorem span_prime_square_of_card_one (e : Module.Basis (Fin 2) ℤ B)
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card {P : Ideal B // Ideal.absNorm P=p}=1) :
    ∃ P : Ideal B, Ideal.absNorm P=p ∧ Ideal.span {(p : B)}=P^2 := by
  obtain ⟨P,hP⟩ := Nat.card_eq_one_iff_exists.mp hcard
  obtain ⟨Q,hQ,hprod⟩ := exists_normPrime_factor_pair e p P.prop
  have heq : Q=P.val := congrArg Subtype.val (hP ⟨Q,hQ⟩)
  exact ⟨P.val,P.prop,by simpa only [heq,pow_two] using hprod⟩

omit [Module.Finite ℤ B] in
/-- Any norm-p ideal is one of the displayed norm-p factors of pB. -/
theorem normPrimeIdeal_eq_factor (p : ℕ) [Fact p.Prime]
    {P Q R : Ideal B} (hP : Ideal.absNorm P=p) (hQ : Ideal.absNorm Q=p)
    (hR : Ideal.absNorm R=p) (hprod : Ideal.span {(p : B)}=P*Q) : R=P ∨ R=Q := by
  have hmax := idealCardPrime_isMaximal p R hR
  have hr : Prime R := Ideal.prime_of_isPrime
    (by
      intro h
      apply (Fact.out : p.Prime).ne_zero
      exact hR.symm.trans (by rw [h,Ideal.absNorm_bot]))
    hmax.isPrime
  have hd := normPrimeIdeal_dvd_span p hR
  rw [hprod] at hd
  exact (hr.dvd_or_dvd hd).imp
    (fun h => (ideal_eq_of_dvd_of_absNorm_eq h (hR.trans hP.symm)
      (hP ▸ (Fact.out : p.Prime).ne_zero)).symm)
    (fun h => (ideal_eq_of_dvd_of_absNorm_eq h (hR.trans hQ.symm)
      (hQ ▸ (Fact.out : p.Prime).ne_zero)).symm)

/-- If there are exactly two norm-p ideals, pB is their product and
they are distinct. The complete actual carrier determines the factors. -/
theorem span_prime_split_of_card_two (e : Module.Basis (Fin 2) ℤ B)
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card {P : Ideal B // Ideal.absNorm P=p}=2) :
    ∃ P Q : Ideal B, Ideal.absNorm P=p ∧ Ideal.absNorm Q=p ∧ P ≠ Q ∧
      Ideal.span {(p : B)}=P*Q := by
  obtain ⟨P,R,hne,-⟩ := Nat.card_eq_two_iff.mp hcard
  obtain ⟨Q,hQ,hprod⟩ := exists_normPrime_factor_pair e p P.prop
  have hrp : R.val ≠ P.val := fun h => hne (Subtype.ext h.symm)
  have hrq := (normPrimeIdeal_eq_factor p P.prop hQ R.prop hprod).resolve_left hrp
  exact ⟨P.val,Q,P.prop,hQ,by simpa only [← hrq] using hrp.symm,hprod⟩

omit [Module.Finite ℤ B] in
/-- The norm condition forces divisibility by the literal scalar power. -/
theorem normPrimePowerIdeal_dvd_span_pow (p k : ℕ) {J : Ideal B}
    (hJ : Ideal.absNorm J=p^k) : J ∣ (Ideal.span {(p : B)})^k := by
  have h := normPrimeIdeal_dvd_span (p^k) hJ
  simpa only [Nat.cast_pow,Ideal.span_singleton_pow] using h

omit [Module.Free ℤ B] [Module.Finite ℤ B] [CharZero B] in
/-- Divisors of an actual prime ideal power are literal ideal powers,
since ideal association is equality. -/
theorem ideal_dvd_prime_pow_iff {P J : Ideal B} (hP : Prime P) (k : ℕ) :
    J ∣ P^k ↔ ∃ i ≤ k, J=P^i := by
  simpa only [associated_iff_eq] using dvd_prime_pow hP k

omit [Module.Finite ℤ B] in
/-- An ideal of norm p is prime in the ideal monoid. -/
theorem normPrimeIdeal_prime (p : ℕ) [Fact p.Prime] {P : Ideal B}
    (hP : Ideal.absNorm P=p) : Prime P := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  apply Ideal.irreducible_of_irreducible_absNorm
  rw [hP]
  exact (Nat.irreducible_iff_nat_prime _).mpr Fact.out

omit [Module.Finite ℤ B] in
/-- In the ramified factorization, every norm-p^k ideal is P^k. -/
theorem normPrimePowerIdeal_eq_ramified (p k : ℕ) [Fact p.Prime]
    {P J : Ideal B} (hP : Ideal.absNorm P=p)
    (hspan : Ideal.span {(p : B)}=P^2) (hJ : Ideal.absNorm J=p^k) : J=P^k := by
  have hd := normPrimePowerIdeal_dvd_span_pow p k hJ
  rw [hspan,← pow_mul] at hd
  obtain ⟨i,-,hi⟩ := (ideal_dvd_prime_pow_iff (normPrimeIdeal_prime p hP) (2*k)).mp hd
  have heq := congrArg Ideal.absNorm hi
  rw [hJ,map_pow,hP] at heq
  have hik := (Nat.pow_right_injective (Fact.out : p.Prime).two_le) heq
  simpa only [← hik] using hi

omit [Module.Finite ℤ B] in
/-- The ramified actual ideal-norm coefficient is one at every exponent. -/
theorem card_normPrimePowerIdeals_ramified (p k : ℕ) [Fact p.Prime]
    {P : Ideal B} (hP : Ideal.absNorm P=p) (hspan : Ideal.span {(p : B)}=P^2) :
    Nat.card {J : Ideal B // Ideal.absNorm J=p^k}=1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨P^k,by rw [map_pow,hP]⟩,?_⟩
  intro J
  exact Subtype.ext (normPrimePowerIdeal_eq_ramified p k hP hspan J.prop)

/-- Inert prime powers have an actual ideal exactly when the exponent
is even; that ideal is a scalar prime ideal power. -/
theorem normPrimePowerIdeal_eq_inert (e : Module.Basis (Fin 2) ℤ B)
    (p k : ℕ) [Fact p.Prime] (hpB : Prime (Ideal.span {(p : B)}))
    {J : Ideal B} (hJ : Ideal.absNorm J=p^k) :
    ∃ i : ℕ, J=(Ideal.span {(p : B)})^i ∧ k=2*i := by
  obtain ⟨i,-,hi⟩ := (ideal_dvd_prime_pow_iff hpB k).mp
    (normPrimePowerIdeal_dvd_span_pow p k hJ)
  refine ⟨i,hi,?_⟩
  have h := congrArg Ideal.absNorm hi
  rw [hJ,map_pow,absNorm_span_nat_rank_two e,← pow_mul] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le) h

/-- The inert coefficient is one for even exponents and zero for odd
exponents. The constant coefficient k=0 is included. -/
theorem card_normPrimePowerIdeals_inert (e : Module.Basis (Fin 2) ℤ B)
    (p k : ℕ) [Fact p.Prime] (hpB : Prime (Ideal.span {(p : B)})) :
    Nat.card {J : Ideal B // Ideal.absNorm J=p^k}=if Even k then 1 else 0 := by
  classical
  split_ifs with hk
  · obtain ⟨i,hi⟩ := hk
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨(Ideal.span {(p : B)})^i,?_⟩,?_⟩
    · rw [map_pow,absNorm_span_nat_rank_two e,← pow_mul]
      congr 1
      omega
    · intro J
      obtain ⟨j,hj,hk⟩ := normPrimePowerIdeal_eq_inert e p k hpB J.prop
      apply Subtype.ext
      have : j=i := by omega
      simpa only [this] using hj
  · letI : IsEmpty {J : Ideal B // Ideal.absNorm J=p^k} := ⟨fun J => by
      obtain ⟨j,-,hj⟩ := normPrimePowerIdeal_eq_inert e p k hpB J.prop
      exact hk ⟨j,by omega⟩⟩
    simp

omit [Module.Finite ℤ B] in
/-- In the split factorization, every norm-p^k ideal is P^i*Q^j
with i+j=k. This is an actual factorization of the original ideal. -/
theorem normPrimePowerIdeal_eq_split (p k : ℕ) [Fact p.Prime]
    {P Q J : Ideal B} (hP : Ideal.absNorm P=p) (hQ : Ideal.absNorm Q=p)
    (hspan : Ideal.span {(p : B)}=P*Q) (hJ : Ideal.absNorm J=p^k) :
    ∃ i j : ℕ, i+j=k ∧ J=P^i*Q^j := by
  have hd := normPrimePowerIdeal_dvd_span_pow p k hJ
  rw [hspan,mul_pow] at hd
  obtain ⟨I₁,I₂,h₁,h₂,hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨i,-,hi⟩ := (ideal_dvd_prime_pow_iff (normPrimeIdeal_prime p hP) k).mp h₁
  obtain ⟨j,-,hj⟩ := (ideal_dvd_prime_pow_iff (normPrimeIdeal_prime p hQ) k).mp h₂
  refine ⟨i,j,?_,by simpa only [hi,hj] using hprod⟩
  have h := congrArg Ideal.absNorm hprod
  rw [hJ,map_mul,hi,hj,map_pow,map_pow,hP,hQ,← pow_add] at h
  exact ((Nat.pow_right_injective (Fact.out : p.Prime).two_le) h).symm

omit [Module.Finite ℤ B] in
/-- Distinct norm-p factors give unique exponents in their products. -/
theorem split_prime_powers_exponent_injective (p : ℕ) [Fact p.Prime]
    {P Q : Ideal B} (hP : Ideal.absNorm P=p) (hQ : Ideal.absNorm Q=p) (hne : P ≠ Q)
    {i j i' j' : ℕ} (h : P^i*Q^j=P^i'*Q^j') : i=i' := by
  have hp := normPrimeIdeal_prime p hP
  have hnot : ¬P ∣ Q := by
    intro hd
    exact hne (ideal_eq_of_dvd_of_absNorm_eq hd (hP.trans hQ.symm)
      (hQ ▸ (Fact.out : p.Prime).ne_zero)).symm
  have hn (l : ℕ) : ¬P ∣ Q^l := fun hd => hnot (hp.dvd_of_dvd_pow hd)
  apply le_antisymm
  · apply (pow_dvd_pow_iff hp.ne_zero hp.not_unit).mp
    apply hp.pow_dvd_of_dvd_mul_right i (hn j')
    rw [← h]
    exact dvd_mul_right _ _
  · apply (pow_dvd_pow_iff hp.ne_zero hp.not_unit).mp
    apply hp.pow_dvd_of_dvd_mul_right i' (hn j)
    rw [h]
    exact dvd_mul_right _ _

omit [Module.Finite ℤ B] in
/-- The literal split norm-p^k ideals are in bijection with 0,...,k. -/
noncomputable def splitNormPrimePowerIdealsEquiv (p k : ℕ) [Fact p.Prime]
    {P Q : Ideal B} (hP : Ideal.absNorm P=p) (hQ : Ideal.absNorm Q=p) (hne : P ≠ Q)
    (hspan : Ideal.span {(p : B)}=P*Q) :
    Fin (k+1) ≃ {J : Ideal B // Ideal.absNorm J=p^k} := by
  let f : Fin (k+1) → {J : Ideal B // Ideal.absNorm J=p^k} := fun i =>
    ⟨P^i.val*Q^(k-i.val),by
      rw [map_mul,map_pow,map_pow,hP,hQ,← pow_add,Nat.add_sub_of_le (by omega)]⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Fin.ext
    exact split_prime_powers_exponent_injective p hP hQ hne (congrArg Subtype.val hij)
  · intro J
    obtain ⟨i,j,hij,hJ⟩ := normPrimePowerIdeal_eq_split p k hP hQ hspan J.prop
    refine ⟨⟨i,by omega⟩,?_⟩
    apply Subtype.ext
    dsimp only [f]
    have : k-i=j := by omega
    simpa only [this] using hJ.symm

omit [Module.Finite ℤ B] in
/-- The split actual ideal-norm coefficient is k+1, including k=0. -/
theorem card_normPrimePowerIdeals_split (p k : ℕ) [Fact p.Prime]
    {P Q : Ideal B} (hP : Ideal.absNorm P=p) (hQ : Ideal.absNorm Q=p) (hne : P ≠ Q)
    (hspan : Ideal.span {(p : B)}=P*Q) :
    Nat.card {J : Ideal B // Ideal.absNorm J=p^k}=k+1 := by
  rw [← Nat.card_congr (splitNormPrimePowerIdealsEquiv p k hP hQ hne hspan),Nat.card_fin]

end IdealNorms

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The literal scalar prime ideal in the same maximal order has norm p^2. -/
theorem maximalOrder_absNorm_span_prime (hD : b^2-4*a*c<0) (p : ℕ) :
    letI := fractionNumberField a b c hD
    Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers
      (FractionRing (CoefficientOrder a b c)))})=p^2 := by
  letI := fractionNumberField a b c hD
  exact absNorm_span_nat_rank_two (maximalOrderBasisOne a b c hD) p

/-- A negative same field prime sign makes the actual pB prime.
This includes the dyadic irreducible case. -/
theorem maximalOrder_span_prime_inert (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p = -1 →
    Prime (Ideal.span {(p : NumberField.RingOfIntegers
      (FractionRing (CoefficientOrder a b c)))}) := by
  letI := fractionNumberField a b c hD
  intro hs
  have hcard := card_maximalNormPrimeIdeals a b c hD p
  rw [hs] at hcard
  apply span_prime_of_no_normPrimeIdeal (maximalOrderBasisOne a b c hD) p
  intro P hP
  letI := finite_maximalNormPrimeIdeals a b c hD p
  letI : Nonempty {J : Ideal (NumberField.RingOfIntegers
    (FractionRing (CoefficientOrder a b c))) // Ideal.absNorm J=p} := ⟨⟨P,hP⟩⟩
  have := Nat.card_pos (α := {J : Ideal (NumberField.RingOfIntegers
    (FractionRing (CoefficientOrder a b c))) // Ideal.absNorm J=p})
  omega

/-- A zero same field sign gives the square of one actual maximal
norm-p ideal. No odd-prime or original-order-maximality premise occurs. -/
theorem maximalOrder_span_prime_ramified (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p = 0 →
    ∃ P : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))),
      Ideal.absNorm P=p ∧ P.IsMaximal ∧ Ideal.span {(p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))}=P^2 := by
  letI := fractionNumberField a b c hD
  intro hs
  have hcard := card_maximalNormPrimeIdeals a b c hD p
  rw [hs,add_zero] at hcard
  have hc : Nat.card {J : Ideal (NumberField.RingOfIntegers
    (FractionRing (CoefficientOrder a b c))) // Ideal.absNorm J=p}=1 := by exact_mod_cast hcard
  obtain ⟨P,hP,hprod⟩ := span_prime_square_of_card_one (maximalOrderBasisOne a b c hD) p hc
  exact ⟨P,hP,idealCardPrime_isMaximal p P hP,hprod⟩

/-- A positive same field sign gives two distinct actual maximal
norm-p ideals with product pB. These exhaust its norm-p ideal carrier. -/
theorem maximalOrder_span_prime_split (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p = 1 →
    ∃ P Q : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))),
      Ideal.absNorm P=p ∧ Ideal.absNorm Q=p ∧ P.IsMaximal ∧ Q.IsMaximal ∧ P ≠ Q ∧
        Ideal.span {(p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))}=P*Q ∧ ∀ R, Ideal.absNorm R=p → R=P ∨ R=Q := by
  letI := fractionNumberField a b c hD
  intro hs
  have hcard := card_maximalNormPrimeIdeals a b c hD p
  rw [hs] at hcard
  have hc : Nat.card {J : Ideal (NumberField.RingOfIntegers
    (FractionRing (CoefficientOrder a b c))) // Ideal.absNorm J=p}=2 := by
    exact_mod_cast hcard
  obtain ⟨P,Q,hP,hQ,hne,hprod⟩ := span_prime_split_of_card_two (maximalOrderBasisOne a b c hD) p hc
  exact ⟨P,Q,hP,hQ,idealCardPrime_isMaximal p P hP,idealCardPrime_isMaximal p Q hQ,
    hne,hprod,fun R hR => normPrimeIdeal_eq_factor p hP hQ hR hprod⟩

/-- At a prime the finite conductor helper has the three actual field
values. This asserts no total Dirichlet-character structure. -/
theorem conductorPrimeSign_trichotomy (d : ℤ) (p : ℕ) [Fact p.Prime] :
    conductorPrimeSign d p = -1 ∨ conductorPrimeSign d p = 0 ∨
      conductorPrimeSign d p = 1 := by
  rw [conductorPrimeSign_eq]
  split_ifs with hp
  · exact (by decide : ∀ x : ZMod 8, ZMod.χ₈ x = -1 ∨ ZMod.χ₈ x = 0 ∨
      ZMod.χ₈ x = 1) d
  · by_cases hd : (d : ZMod p)=0
    · exact Or.inr (Or.inl ((legendreSym.eq_zero_iff p d).mpr hd))
    · rcases legendreSym.eq_one_or_neg_one p hd with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

/-- The complete actual prime-power coefficient, on the same maximal
order and field discriminant, including exponent zero and p=2. -/
theorem card_maximalNormPrimePowerIdeals (hD : b^2-4*a*c<0)
    (p k : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    (Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=p^k} : ℤ) =
        ∑ j ∈ Finset.range (k+1),
          conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p ^ j := by
  letI := fractionNumberField a b c hD
  have hn (l : ℕ) : (∑ j ∈ Finset.range (l+1),(-1 : ℤ)^j)=if Even l then 1 else 0 := by
    induction l with
    | zero => norm_num
    | succ l ih =>
      rw [Finset.sum_range_succ,ih,neg_one_pow_eq_ite]
      have he : Even (l+1) ↔ ¬Even l := by
        simp only [Nat.even_add_one]
      by_cases hl : Even l <;> simp [he,hl]
  have hz (l : ℕ) : (∑ j ∈ Finset.range (l+1),(0 : ℤ)^j)=1 := by
    induction l with
    | zero => norm_num
    | succ l ih => simp only [Finset.sum_range_succ,ih,zero_pow (Nat.succ_ne_zero l),add_zero]
  rcases conductorPrimeSign_trichotomy
    (NumberField.discr (FractionRing (CoefficientOrder a b c))) p with hs | hs | hs
  · have h := card_normPrimePowerIdeals_inert (maximalOrderBasisOne a b c hD) p k
      (maximalOrder_span_prime_inert a b c hD p hs)
    rw [h,hs,hn]
    split_ifs <;> rfl
  · obtain ⟨P,hP,-,hspan⟩ := maximalOrder_span_prime_ramified a b c hD p hs
    rw [card_normPrimePowerIdeals_ramified p k hP hspan,hs,hz]
    rfl
  · obtain ⟨P,Q,hP,hQ,-,-,hne,hspan,-⟩ := maximalOrder_span_prime_split a b c hD p hs
    rw [card_normPrimePowerIdeals_split p k hP hQ hne hspan,hs]
    simp

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.ideal_eq_of_dvd_of_absNorm_eq
#assert_standard_axioms BinaryNormIdeal.absNorm_span_nat_rank_two
#assert_standard_axioms BinaryNormIdeal.normPrimeIdeal_dvd_span
#assert_standard_axioms BinaryNormIdeal.exists_normPrime_factor_pair
#assert_standard_axioms BinaryNormIdeal.absNorm_prime_factor_span
#assert_standard_axioms BinaryNormIdeal.span_prime_of_no_normPrimeIdeal
#assert_standard_axioms BinaryNormIdeal.span_prime_square_of_card_one
#assert_standard_axioms BinaryNormIdeal.normPrimeIdeal_eq_factor
#assert_standard_axioms BinaryNormIdeal.span_prime_split_of_card_two

#assert_standard_axioms BinaryNormIdeal.maximalOrder_absNorm_span_prime
#assert_standard_axioms BinaryNormIdeal.maximalOrder_span_prime_inert
#assert_standard_axioms BinaryNormIdeal.maximalOrder_span_prime_ramified
#assert_standard_axioms BinaryNormIdeal.maximalOrder_span_prime_split

#assert_standard_axioms BinaryNormIdeal.normPrimePowerIdeal_dvd_span_pow
#assert_standard_axioms BinaryNormIdeal.ideal_dvd_prime_pow_iff
#assert_standard_axioms BinaryNormIdeal.normPrimeIdeal_prime
#assert_standard_axioms BinaryNormIdeal.normPrimePowerIdeal_eq_ramified
#assert_standard_axioms BinaryNormIdeal.card_normPrimePowerIdeals_ramified
#assert_standard_axioms BinaryNormIdeal.normPrimePowerIdeal_eq_inert
#assert_standard_axioms BinaryNormIdeal.card_normPrimePowerIdeals_inert
#assert_standard_axioms BinaryNormIdeal.normPrimePowerIdeal_eq_split
#assert_standard_axioms BinaryNormIdeal.split_prime_powers_exponent_injective
#assert_standard_axioms BinaryNormIdeal.splitNormPrimePowerIdealsEquiv
#assert_standard_axioms BinaryNormIdeal.card_normPrimePowerIdeals_split

#assert_standard_axioms BinaryNormIdeal.conductorPrimeSign_trichotomy
#assert_standard_axioms BinaryNormIdeal.card_maximalNormPrimePowerIdeals
