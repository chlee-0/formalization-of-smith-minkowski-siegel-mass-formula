import SMSFormula.BinarySplitPrimeForms
import SMSFormula.BinaryOrderUnitCounts

/-!
# Odd-prime characters on the original order-unit norm quotient

The character of a scalar unit is its quadratic residue character raised
to the valuation of the original primitive discriminant. Original order-unit
norms lie in its kernel. No field-norm quotient replaces the original carrier.
-/

noncomputable section

namespace BinaryNormIdeal

/-- A ramified discriminant algebra has square norms over a field of odd
characteristic. This includes the nonmaximal and repeated-root cases. -/
theorem isSquare_discriminantAlgebra_norm_of_discriminant_zero
    {F : Type*} [Field F] (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (h2 : (2 : F)≠0) (hzero : (D : F)=0) (z : DiscriminantAlgebra F D) :
    IsSquare z.norm := by
  have hd := congrArg (fun n : ℤ => (n : F))
    (discriminantAlgebra_parameter_discriminant D hD)
  push_cast at hd
  rw [hzero] at hd
  refine ⟨z.re+((D%2 : ℤ) : F)*z.im/2,?_⟩
  simp only [QuadraticAlgebra.norm_def]
  push_cast
  field_simp
  linear_combination -z.im^2*hd

/-- At a ramified odd prime, the literal reduction of an original
order-unit norm is a square. -/
theorem isSquare_toZMod_orderUnitNorm_of_dvd (p : ℕ) [Fact p.Prime]
    (hp : p≠2) (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hpD : (p : ℤ)∣D)
    (z : (DiscriminantAlgebra ℤ_[p] D)ˣ) :
    IsSquare (PadicInt.toZMod ((orderUnitNorm ℤ_[p] D z : ℤ_[p]ˣ) : ℤ_[p])) := by
  have h2 : (2 : ZMod p)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp h
  have hs := isSquare_discriminantAlgebra_norm_of_discriminant_zero D hD h2
    ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpD)
    (discriminantAlgebraMap (PadicInt.toZMod (p := p)) D z.val)
  rw [← discriminantAlgebraMap_norm] at hs
  exact hs

/-- At a ramified odd prime, original order-unit norms are exactly scalar
squares. The reverse implication uses actual integral scalar units. -/
theorem mem_orderUnitNormSubgroup_iff_isSquare_of_odd_dvd (p : ℕ) [Fact p.Prime]
    (hp : p≠2) (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hpD : (p : ℤ)∣D)
    (u : ℤ_[p]ˣ) : u ∈ orderUnitNormSubgroup ℤ_[p] D ↔ IsSquare (u : ℤ_[p]) := by
  constructor
  · rintro ⟨z,rfl⟩
    exact (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hp
      (orderUnitNorm ℤ_[p] D z).isUnit).mpr
      (isSquare_toZMod_orderUnitNorm_of_dvd p hp D hD hpD z)
  · exact mem_orderUnitNormSubgroup_of_isSquare ℤ_[p] D u

/-- The actual odd Hilbert-symbol formula on scalar units, before descent. -/
def oddUnitHilbertCharacter (p : ℕ) [Fact p.Prime] (D : ℤ) : ℤ_[p]ˣ →* ℤˣ :=
  ((quadraticChar (ZMod p)).toUnitHom.comp
    (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)) ^ padicValInt p D

theorem oddUnitHilbertCharacter_apply (p : ℕ) [Fact p.Prime] (D : ℤ)
    (u : ℤ_[p]ˣ) :
    (oddUnitHilbertCharacter p D u : ℤ)=
      quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) ^ padicValInt p D := by
  rfl

/-- Every original order-unit norm is annihilated. The valuation-zero branch
is essential: unramified scalar norms need not have square residue. -/
theorem oddUnitHilbertCharacter_orderUnitNorm (p : ℕ) [Fact p.Prime]
    (hp : p≠2) (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (z : (DiscriminantAlgebra ℤ_[p] D)ˣ) :
    oddUnitHilbertCharacter p D (orderUnitNorm ℤ_[p] D z)=1 := by
  apply Units.ext
  rw [oddUnitHilbertCharacter_apply]
  change quadraticChar (ZMod p) (PadicInt.toZMod z.val.norm) ^ padicValInt p D=1
  by_cases hpD : (p : ℤ) ∣ D
  · have hs := isSquare_toZMod_orderUnitNorm_of_dvd p hp D hD hpD z
    have hn : PadicInt.toZMod (z.val.norm)≠0 := by
      exact (Units.map (PadicInt.toZMod (p := p)).toMonoidHom
        (orderUnitNorm ℤ_[p] D z)).ne_zero
    have hc := (quadraticChar_one_iff_isSquare hn).mpr hs
    change quadraticChar (ZMod p) (PadicInt.toZMod z.val.norm) ^ padicValInt p D=1
    rw [hc,one_pow]
  · rw [padicValInt.eq_zero_of_not_dvd hpD,pow_zero]

theorem orderUnitNormSubgroup_le_oddUnitHilbertCharacter_ker (p : ℕ) [Fact p.Prime]
    (hp : p≠2) (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    orderUnitNormSubgroup ℤ_[p] D ≤ (oddUnitHilbertCharacter p D).ker := by
  rintro u ⟨z,rfl⟩
  exact oddUnitHilbertCharacter_orderUnitNorm p hp D hD z

/-- Descent on the original order-unit norm quotient. -/
def oddOrderNormCharacter (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) : OrderUnitNormQuotient ℤ_[p] D →* ℤˣ :=
  QuotientGroup.lift (orderUnitNormSubgroup ℤ_[p] D) (oddUnitHilbertCharacter p D)
    (orderUnitNormSubgroup_le_oddUnitHilbertCharacter_ker p hp D hD)

theorem oddOrderNormCharacter_quotientMap (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (u : ℤ_[p]ˣ) :
    oddOrderNormCharacter p hp D hD (orderUnitNormQuotientMap ℤ_[p] D u)=
      oddUnitHilbertCharacter p D u := rfl

/-- Evaluation on a literal scalar uses the original discriminant valuation. -/
theorem oddOrderNormCharacter_natCast (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (a : ℕ) (u : ℤ_[p]ˣ)
    (hu : (u : ℤ_[p])=(a : ℤ_[p])) :
    (oddOrderNormCharacter p hp D hD (orderUnitNormQuotientMap ℤ_[p] D u) : ℤ)=
      legendreSym p a ^ padicValInt p D := by
  rw [oddOrderNormCharacter_quotientMap,oddUnitHilbertCharacter_apply,hu,map_natCast]
  simp only [legendreSym,Int.cast_natCast]

/-- A good odd prime contributes the trivial character, even if it lies
in the original `Bad` set because of content alone. -/
theorem oddOrderNormCharacter_eq_one_of_not_dvd (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hpD : ¬(p : ℤ)∣D)
    (q : OrderUnitNormQuotient ℤ_[p] D) : oddOrderNormCharacter p hp D hD q=1 := by
  induction q using QuotientGroup.induction_on with
  | H u =>
    apply Units.ext
    change quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) ^ padicValInt p D=1
    rw [padicValInt.eq_zero_of_not_dvd hpD,pow_zero]

/-- A quadratic nonsquare scalar gives a negative value at every odd
discriminant valuation. This does not classify the original norm quotient. -/
theorem exists_oddOrderNormCharacter_eq_neg_one (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (ha : Odd (padicValInt p D)) :
    ∃ q : OrderUnitNormQuotient ℤ_[p] D, oddOrderNormCharacter p hp D hD q = -1 := by
  obtain ⟨v,hv⟩ := quadraticChar_exists_neg_one' (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hm : normResidueModulus p=p := if_neg hp
  let w : (ZMod (normResidueModulus p))ˣ :=
    Units.map (ZMod.ringEquivCongr hm).symm.toRingHom.toMonoidHom v
  obtain ⟨u,hu⟩ := normResidueUnits_surjective p w
  have he : PadicInt.toZMod (u : ℤ_[p])=v.val := by
    have h := congrArg (fun t : (ZMod (normResidueModulus p))ˣ =>
      ZMod.ringEquivCongr hm t.val) hu
    simpa [normResidueUnits,normResidueHom,hp,w] using h
  refine ⟨orderUnitNormQuotientMap ℤ_[p] D u,?_⟩
  apply Units.ext
  change quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) ^ padicValInt p D = -1
  rw [he,hv,ha.neg_one_pow]

/-- The descended odd-prime character is onto both integer units whenever
the original discriminant valuation is odd. -/
theorem oddOrderNormCharacter_surjective (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (ha : Odd (padicValInt p D)) :
    Function.Surjective (oddOrderNormCharacter p hp D hD) := by
  intro t
  rcases Int.units_eq_one_or t with ht | ht
  · exact ⟨1,(map_one _).trans ht.symm⟩
  · obtain ⟨q,hq⟩ := exists_oddOrderNormCharacter_eq_neg_one p hp D hD ha
    exact ⟨q,hq.trans ht.symm⟩

/-- Even discriminant valuation gives the trivial odd-prime character.
The original order-unit norm quotient itself can still be nontrivial. -/
theorem oddOrderNormCharacter_eq_one_of_even (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (ha : Even (padicValInt p D))
    (q : OrderUnitNormQuotient ℤ_[p] D) : oddOrderNormCharacter p hp D hD q=1 := by
  induction q using QuotientGroup.induction_on with
  | H u =>
    apply Units.ext
    change quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) ^ padicValInt p D=1
    have hn : PadicInt.toZMod (u : ℤ_[p])≠0 :=
      (Units.map (PadicInt.toZMod (p := p)).toMonoidHom u).ne_zero
    rcases quadraticChar_dichotomy hn with h | h
    · rw [h,one_pow]
    · rw [h,ha.neg_one_pow]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The odd part of the character on the whole original `Bad` tuple.
The dyadic coordinate stays in the domain and contributes one here. -/
def binaryOddNormCharacter (K : PositiveDefiniteIntegralLattice 2) : K.BinaryBadNormProduct →* ℤˣ where
  toFun x := ∏ p : ↥(massBadPrimeSet K),
    if hp : p.val.val=2 then 1 else
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      oddOrderNormCharacter p.val.val hp K.binaryPrimitiveDiscriminant
        K.binaryPrimitiveDiscriminant_mod_four (x p)
  map_one' := by simp
  map_mul' x y := by
    classical
    simp only [Pi.mul_apply]
    calc
      _ = ∏ p : ↥(massBadPrimeSet K),
        (if hp : p.val.val=2 then 1 else
          letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
          oddOrderNormCharacter p.val.val hp K.binaryPrimitiveDiscriminant
            K.binaryPrimitiveDiscriminant_mod_four (x p)) *
        (if hp : p.val.val=2 then 1 else
          letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
          oddOrderNormCharacter p.val.val hp K.binaryPrimitiveDiscriminant
            K.binaryPrimitiveDiscriminant_mod_four (y p)) := by
          apply Finset.prod_congr rfl
          intro p _
          split_ifs <;> simp [map_mul]
      _ = _ := Finset.prod_mul_distrib

/-- Evaluation on one scalar carrying the entire original tuple. This is
the odd part of the scalar identity needed after CRT and Dirichlet. -/
theorem binaryOddNormCharacter_scalar (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (a : ℕ)
    (ha : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(a : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=x p) :
    (K.binaryOddNormCharacter x : ℤ)=
      ∏ p : ↥(massBadPrimeSet K), if p.val.val=2 then 1 else
        letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
        legendreSym p.val.val a ^ padicValInt p.val.val K.binaryPrimitiveDiscriminant := by
  change (Units.coeHom ℤ) (∏ p : ↥(massBadPrimeSet K), _)=_
  rw [map_prod (Units.coeHom ℤ)]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p.val.val=2
  · simp [hp]
  · letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    obtain ⟨u,hu,hq⟩ := ha p
    simp only [dif_neg hp,if_neg hp]
    rw [← hq]
    exact oddOrderNormCharacter_natCast p.val.val hp K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four a u hu

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.isSquare_discriminantAlgebra_norm_of_discriminant_zero
#assert_standard_axioms BinaryNormIdeal.isSquare_toZMod_orderUnitNorm_of_dvd
#assert_standard_axioms BinaryNormIdeal.mem_orderUnitNormSubgroup_iff_isSquare_of_odd_dvd
#assert_standard_axioms BinaryNormIdeal.oddUnitHilbertCharacter
#assert_standard_axioms BinaryNormIdeal.oddUnitHilbertCharacter_apply
#assert_standard_axioms BinaryNormIdeal.oddUnitHilbertCharacter_orderUnitNorm
#assert_standard_axioms BinaryNormIdeal.orderUnitNormSubgroup_le_oddUnitHilbertCharacter_ker
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_quotientMap
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_natCast
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_eq_one_of_not_dvd
#assert_standard_axioms BinaryNormIdeal.exists_oddOrderNormCharacter_eq_neg_one
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_surjective
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_eq_one_of_even

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOddNormCharacter
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOddNormCharacter_scalar
