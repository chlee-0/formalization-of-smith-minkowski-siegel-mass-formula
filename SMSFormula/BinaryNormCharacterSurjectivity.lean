import SMSFormula.BinaryDyadicNormCharacter

/-!
# Surjectivity of the full binary norm character

The witness is the tuple of scalar-unit classes of negative one.
Prime factorization of natural numbers keeps every original bad coordinate.
Reciprocity and equality with the Picard image are not proved here.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Prime factorization mapped through chi4, before passing to any real field. -/
theorem primeSet_prod_chiFour (m : ℕ) (hm : m≠0)
    (S : Finset {p : ℕ // p.Prime})
    (hs : ∀ p : {p : ℕ // p.Prime}, p.val∣m → p∈S) :
    (∏ p ∈ S, ZMod.χ₄ (p.val : ZMod 4)^padicValNat p.val m)=
      ZMod.χ₄ (m : ZMod 4) := by
  let N := S.image Subtype.val
  have hn : m.primeFactors⊆N := by
    intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    exact Finset.mem_image.mpr ⟨⟨p,hh.1⟩,hs ⟨p,hh.1⟩ hh.2.1,rfl⟩
  have he : (∏ p ∈ N, p^(m.factorization p))=m := by
    rw [← Finset.prod_subset hn (by
      intro p _ hp
      have hz : m.factorization p=0 := Finsupp.notMem_support_iff.mp hp
      rw [hz,pow_zero])]
    have hh := Nat.prod_factorization_pow_eq_self hm
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hh
    exact hh
  have hc := congrArg (fun n : ℕ => ZMod.χ₄ (n : ZMod 4)) he
  push_cast at hc
  simp only [map_prod,map_pow] at hc
  have hmap : (∏ p ∈ N, ZMod.χ₄ (p : ZMod 4)^m.factorization p)=
      ∏ p ∈ S, ZMod.χ₄ (p.val : ZMod 4)^m.factorization p.val :=
    Finset.prod_image Subtype.val_injective.injOn
  rw [hmap] at hc
  simpa only [Nat.factorization_def _ (Subtype.property _)] using hc

/-- Negativity of the native signed odd part follows from the same D. -/
theorem dyadicOddPart_neg (D : ℤ) (hD : D<0) : dyadicOddPart D<0 := by
  have he := dyadicOddPart_decomposition D
  have hp : 0<(2 : ℤ)^padicValInt 2 D := by positivity
  nlinarith

/-- Removing the power of two preserves every odd-prime valuation. -/
theorem padicValInt_dyadicOddPart (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D≠0) : padicValInt p D=padicValNat p (dyadicOddPart D).natAbs := by
  have he := congrArg Int.natAbs (dyadicOddPart_decomposition D)
  simp only [Int.natAbs_mul,Int.natAbs_pow] at he
  change D.natAbs=2^padicValInt 2 D*(dyadicOddPart D).natAbs at he
  have hd0 : dyadicOddPart D≠0 := by
    intro hz
    apply hD
    rw [dyadicOddPart_decomposition D,hz,mul_zero]
  change padicValNat p D.natAbs=_
  rw [he,padicValNat.mul (by positivity)
    (Int.natAbs_ne_zero.mpr hd0)]
  rw [padicValNat_prime_prime_pow _ hp,zero_add]

/-- An actual negative-one class is evaluated directly as a unit, not as a
natural scalar. The original discriminant valuation remains in the exponent. -/
theorem oddOrderNormCharacter_neg_one (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    (oddOrderNormCharacter p hp D hD
      (orderUnitNormQuotientMap ℤ_[p] D (-1 : ℤ_[p]ˣ)) : ℤ)=
        ZMod.χ₄ (p : ZMod 4)^padicValInt p D := by
  rw [oddOrderNormCharacter_quotientMap,oddUnitHilbertCharacter_apply]
  have h : PadicInt.toZMod ((-1 : ℤ_[p]ˣ) : ℤ_[p])=(-1 : ZMod p) := by
    simp only [Units.val_neg,Units.val_one,map_neg,map_one]
  rw [h]
  simpa only [legendreSym,Int.cast_neg,Int.cast_one] using
    congrArg (fun t : ℤ => t^padicValInt p D) (legendreSym.at_neg_one hp)

private theorem chiFour_negative_one : ∀ d : ZMod 4, IsUnit d →
    (if d=1 then 1 else ZMod.χ₄ (-1 : ZMod 4))=ZMod.χ₄ d := by decide

private theorem odd_unit_mod_four : ∀ t : ZMod 4, IsUnit (2*t+1) := by decide

private theorem chiFour_opposite : ∀ d : ZMod 4, IsUnit d →
    ZMod.χ₄ (-d)*ZMod.χ₄ d=-1 := by decide

private theorem odd_int_unit_mod_four (d : ℤ) (hd : Odd d) : IsUnit (d : ZMod 4) := by
  obtain ⟨t,ht⟩ := hd
  have he : (d : ZMod 4)=2*(t : ZMod 4)+1 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_one] using
      congrArg (fun n : ℤ => (n : ZMod 4)) ht
  rw [he]
  exact odd_unit_mod_four _

/-- The dyadic negative-one value is chi4 of the signed native odd part. -/
theorem dyadicOrderNormCharacter_neg_one (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (hzero : D≠0) :
    (dyadicOrderNormCharacter D hD hzero
      (orderUnitNormQuotientMap ℤ_[2] D (-1 : ℤ_[2]ˣ)) : ℤ)=
        ZMod.χ₄ (dyadicOddPart D : ZMod 4) := by
  rw [dyadicOrderNormCharacter_quotientMap]
  change (dyadicResidueCharacter (padicValInt 2 D) (dyadicOddPart D)
    (normResidueUnits 2 (-1 : ℤ_[2]ˣ)) : ℤ)=_
  rw [dyadicResidueCharacter_apply]
  have he : (normResidueUnits 2 (-1 : ℤ_[2]ˣ)).val=(-1 : ZMod 8) := by
    change normResidueHom 2 ((-1 : ℤ_[2]ˣ) : ℤ_[2])=(-1 : ZMod 8)
    simp only [Units.val_neg,Units.val_one,map_neg,map_one]
    rfl
  rw [he]
  have h4 : (ZMod.cast (-1 : ZMod 8) : ZMod 4)=-1 := by decide
  have h8 : ZMod.χ₈ (-1 : ZMod 8)=1 := by decide
  rw [h4,h8,one_pow,mul_one]
  exact chiFour_negative_one _ (odd_int_unit_mod_four _ (dyadicOddPart_odd D hzero))

/-- The signed odd part and its positive magnitude have opposite chi4 signs. -/
theorem chiFour_natAbs_mul_of_neg_odd (d : ℤ) (hd : Odd d) (hneg : d<0) :
    ZMod.χ₄ (d.natAbs : ZMod 4)*ZMod.χ₄ (d : ZMod 4)=-1 := by
  have he : (d.natAbs : ℤ)=-d := by rw [Int.natCast_natAbs,abs_of_neg hneg]
  have hc : (d.natAbs : ZMod 4)=-(d : ZMod 4) := by
    simpa only [Int.cast_natCast,Int.cast_neg] using
      congrArg (fun n : ℤ => (n : ZMod 4)) he
  rw [hc]
  exact chiFour_opposite _ (odd_int_unit_mod_four d hd)

end BinaryNormIdeal


namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual original quotient tuple represented by scalar unit -1 at
Every original Bad prime. No Picard-image membership is assumed. -/
def binaryNegativeOneNormTuple (K : PositiveDefiniteIntegralLattice 2) : K.BinaryBadNormProduct :=
  fun p =>
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant (-1 : ℤ_[p.val.val]ˣ)

/-- Prime factorization evaluates the odd character of the original
negative-one tuple, with all content-only coordinates kept. -/
theorem binaryOddNormCharacter_negativeOneTuple (K : PositiveDefiniteIntegralLattice 2) :
    (K.binaryOddNormCharacter K.binaryNegativeOneNormTuple : ℤ)=
      ZMod.χ₄ ((dyadicOddPart K.binaryPrimitiveDiscriminant).natAbs : ZMod 4) := by
  classical
  let D := K.binaryPrimitiveDiscriminant
  let m := (dyadicOddPart D).natAbs
  have hzero : D≠0 := ne_of_lt K.binaryPrimitiveDiscriminant_neg
  have hm : m≠0 := Int.natAbs_ne_zero.mpr (ne_of_lt (dyadicOddPart_neg D K.binaryPrimitiveDiscriminant_neg))
  have he := congrArg Int.natAbs (dyadicOddPart_decomposition D)
  simp only [Int.natAbs_mul,Int.natAbs_pow] at he
  change D.natAbs=2^padicValInt 2 D*m at he
  have hs : ∀ p : {p : ℕ // p.Prime}, p.val∣m → p∈massBadPrimeSet K := by
    intro p hp
    apply K.binary_mem_bad_of_dvd_primitive
    change p.val∣D.natAbs
    rw [he]
    exact hp.trans (dvd_mul_left _ _)
  have hv2 : padicValNat 2 m=0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    obtain ⟨t,ht⟩ := (dyadicOddPart_odd D hzero).natAbs
    obtain ⟨s,hs⟩ := hd
    change m=2*t+1 at ht
    omega
  calc
    _=∏ p : ↥(massBadPrimeSet K), ZMod.χ₄ (p.val.val : ZMod 4)^padicValNat p.val.val m := by
      change (Units.coeHom ℤ) (∏ p : ↥(massBadPrimeSet K), _)=_
      rw [map_prod (Units.coeHom ℤ)]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p.val.val=2
      · simp [hp,hv2]
      · letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
        simp only [dif_neg hp,binaryNegativeOneNormTuple]
        change (oddOrderNormCharacter p.val.val hp D K.binaryPrimitiveDiscriminant_mod_four
          (orderUnitNormQuotientMap ℤ_[p.val.val] D (-1 : ℤ_[p.val.val]ˣ)) : ℤ)=_
        rw [oddOrderNormCharacter_neg_one,padicValInt_dyadicOddPart p.val.val hp D hzero]
    _=∏ p ∈ massBadPrimeSet K, ZMod.χ₄ (p.val : ZMod 4)^padicValNat p.val m := by
      exact Finset.prod_coe_sort (massBadPrimeSet K)
        (fun p => ZMod.χ₄ (p.val : ZMod 4)^padicValNat p.val m)
    _=ZMod.χ₄ (m : ZMod 4) := primeSet_prod_chiFour m hm (massBadPrimeSet K) hs

/-- The full character takes value -1 on one explicit tuple of actual
original classes, for every rank-two lattice and original content. -/
theorem binaryNormProductCharacter_negativeOneTuple (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryNormProductCharacter K.binaryNegativeOneNormTuple=-1 := by
  apply Units.ext
  change (K.binaryOddNormCharacter K.binaryNegativeOneNormTuple : ℤ) *
    (dyadicOrderNormCharacter K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg)
      (K.binaryNegativeOneNormTuple K.binaryDyadicBadPrime) : ℤ)=(-1 : ℤ)
  rw [K.binaryOddNormCharacter_negativeOneTuple]
  change ZMod.χ₄ ((dyadicOddPart K.binaryPrimitiveDiscriminant).natAbs : ZMod 4) *
    (dyadicOrderNormCharacter K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg)
      (orderUnitNormQuotientMap ℤ_[2] K.binaryPrimitiveDiscriminant (-1 : ℤ_[2]ˣ)) : ℤ)=-1
  rw [dyadicOrderNormCharacter_neg_one]
  exact chiFour_natAbs_mul_of_neg_odd _
    (dyadicOddPart_odd _ (ne_of_lt K.binaryPrimitiveDiscriminant_neg))
    (dyadicOddPart_neg _ K.binaryPrimitiveDiscriminant_neg)

/-- Surjectivity of the full character on the whole original Bad product.
This does not identify its kernel with the actual Picard image. -/
theorem binaryNormProductCharacter_surjective (K : PositiveDefiniteIntegralLattice 2) :
    Function.Surjective K.binaryNormProductCharacter := by
  intro t
  rcases Int.units_eq_one_or t with ht | ht
  · exact ⟨1,(map_one _).trans ht.symm⟩
  · exact ⟨K.binaryNegativeOneNormTuple,K.binaryNormProductCharacter_negativeOneTuple.trans ht.symm⟩

/-- The character kernel has index two. Equality with the Picard
image is a separate global statement, not proved here. -/
theorem binaryNormProductCharacter_ker_index (K : PositiveDefiniteIntegralLattice 2) :
    (MonoidHom.ker (G := K.BinaryBadNormProduct) K.binaryNormProductCharacter).index=2 := by
  have hc : Nat.card ℤˣ=2 := by
    rw [Nat.card_eq_two_iff' (1 : ℤˣ)]
    refine ⟨-1,by decide,?_⟩
    intro y hy
    rcases Int.units_eq_one_or y with h | h
    · exact False.elim (hy h)
    · exact h
  have hr : MonoidHom.range (G := K.BinaryBadNormProduct) K.binaryNormProductCharacter=
      (⊤ : Subgroup ℤˣ) :=
    MonoidHom.range_eq_top_of_surjective (G := K.BinaryBadNormProduct)
      K.binaryNormProductCharacter K.binaryNormProductCharacter_surjective
  rw [Subgroup.index_ker,hr,Subgroup.card_top,hc]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.primeSet_prod_chiFour
#assert_standard_axioms BinaryNormIdeal.dyadicOddPart_neg
#assert_standard_axioms BinaryNormIdeal.padicValInt_dyadicOddPart
#assert_standard_axioms BinaryNormIdeal.oddOrderNormCharacter_neg_one
#assert_standard_axioms BinaryNormIdeal.dyadicOrderNormCharacter_neg_one
#assert_standard_axioms BinaryNormIdeal.chiFour_natAbs_mul_of_neg_odd
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNegativeOneNormTuple
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOddNormCharacter_negativeOneTuple
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_negativeOneTuple
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_surjective
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_ker_index
