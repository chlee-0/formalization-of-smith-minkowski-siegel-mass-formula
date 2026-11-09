import SMSFormula.BinaryNormCharacterSurjectivity

/-!
# The full original tuple character and the same-field prime sign

Jacobi reciprocity identifies the character of any original tuple carried
by a good prime scalar with that same field's prime sign. The
prime-form bridge then realizes every character-kernel tuple in the
Picard image. The opposite inclusion is not proved here.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Jacobi evaluation over any prime set containing the natural support.
Additional primes contribute exponent zero, including two for odd m. -/
theorem primeSet_prod_jacobi (b : ℤ) (m : ℕ) (hm : m≠0)
    (S : Finset {p : ℕ // p.Prime})
    (hs : ∀ p : {p : ℕ // p.Prime}, p.val∣m → p∈S) :
    (∏ p ∈ S, jacobiSym b p.val^padicValNat p.val m)=jacobiSym b m := by
  classical
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
  have hmap (T : Finset ℕ) (ht : ∀ p∈T, p≠0) :
      jacobiSym b (∏ p∈T, p^(m.factorization p))=
        ∏ p∈T, jacobiSym b p^m.factorization p := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
      rw [Finset.prod_insert hp,Finset.prod_insert hp,
        jacobiSym.mul_right' b (pow_ne_zero _ (ht p (Finset.mem_insert_self _ _)))
          (Finset.prod_ne_zero_iff.mpr (by
            intro q hq
            exact pow_ne_zero _ (ht q (Finset.mem_insert_of_mem hq)))),
        jacobiSym.pow_right,ih (by intro q hq; exact ht q (Finset.mem_insert_of_mem hq))]
  have ht : ∀ p∈N, p≠0 := by
    intro p hp
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact q.prop.ne_zero
  have hh := (hmap N ht).symm
  rw [he] at hh
  have hp : (∏ p∈N, jacobiSym b p^m.factorization p)=
      ∏ p∈S, jacobiSym b p.val^m.factorization p.val :=
    Finset.prod_image Subtype.val_injective.injOn
  rw [hp] at hh
  simpa only [Nat.factorization_def _ (Subtype.property _)] using hh

/-- Quadratic reciprocity with the native SIGNED odd part of negative D.
No fundamental-discriminant, coprimality or field certificate is required. -/
theorem jacobiSym_eq_signed_oddPart (D : ℤ) (hD : D<0)
    (l : ℕ) (hlodd : Odd l) :
    jacobiSym D l=jacobiSym l (dyadicOddPart D).natAbs *
      ((if (dyadicOddPart D : ZMod 4)=1 then 1 else ZMod.χ₄ (l : ZMod 4)) *
        ZMod.χ₈ (l : ZMod 8)^padicValInt 2 D) := by
  let d := dyadicOddPart D
  let m := d.natAbs
  have hodd : Odd m := (dyadicOddPart_odd D (ne_of_lt hD)).natAbs
  have hdneg : d<0 := dyadicOddPart_neg D hD
  have hdm : d=-(m : ℤ) := by
    have h : (d.natAbs : ℤ)=-d := by rw [Int.natCast_natAbs,abs_of_neg hdneg]
    omega
  have hdmod : (d : ZMod 4)=-(m : ZMod 4) := by
    simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod 4)) hdm
  have he : jacobiSym D l=ZMod.χ₈ (l : ZMod 8)^padicValInt 2 D *
      (ZMod.χ₄ (l : ZMod 4)*jacobiSym m l) := by
    nth_rw 1 [dyadicOddPart_decomposition D]
    change jacobiSym ((2 : ℤ)^padicValInt 2 D*d) l=_
    rw [hdm,jacobiSym.mul_left,jacobiSym.pow_left,jacobiSym.neg _ hlodd,
      jacobiSym.at_two hlodd]
  have hrec := jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hlodd) (Nat.odd_iff.mp hodd)
  have hmcases := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd)
  have hlcases := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hlodd)
  have hchi1 : ∀ n : ℕ, n%4=1 → ZMod.χ₄ (n : ZMod 4)=1 := by
    intro n hn
    exact ZMod.χ₄_nat_one_mod_four hn
  have hchi3 : ∀ n : ℕ, n%4=3 → ZMod.χ₄ (n : ZMod 4)=-1 := by
    intro n hn
    exact ZMod.χ₄_nat_three_mod_four hn
  rw [he]
  change _=jacobiSym l m*((if (d : ZMod 4)=1 then 1 else ZMod.χ₄ (l : ZMod 4))*_)
  rw [hdmod]
  rcases hmcases with hm | hm <;> rcases hlcases with hl4 | hl4
  all_goals
    have hmcast : (m : ZMod 4)=((m%4 : ℕ) : ZMod 4) := (ZMod.natCast_mod m 4).symm
    rw [hm] at hmcast
    simp [hm,hl4] at hrec
  · have hb : (if -(m : ZMod 4)=1 then (1 : ℤ) else ZMod.χ₄ (l : ZMod 4))=ZMod.χ₄ (l : ZMod 4) := by
      rw [hmcast]
      exact if_neg (by decide)
    rw [hb,hchi1 l hl4,← hrec]
    ring
  · have hb : (if -(m : ZMod 4)=1 then (1 : ℤ) else ZMod.χ₄ (l : ZMod 4))=ZMod.χ₄ (l : ZMod 4) := by
      rw [hmcast]
      exact if_neg (by decide)
    rw [hb,hchi3 l hl4,← hrec]
    ring
  · have hb : (if -(m : ZMod 4)=1 then (1 : ℤ) else ZMod.χ₄ (l : ZMod 4))=1 := by
      rw [hmcast]
      exact if_pos (by decide)
    rw [hb,hchi1 l hl4,← hrec]
    ring
  · have hb : (if -(m : ZMod 4)=1 then (1 : ℤ) else ZMod.χ₄ (l : ZMod 4))=1 := by
      rw [hmcast]
      exact if_pos (by decide)
    rw [hb,hchi3 l hl4,← hrec]
    ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The original odd Bad product is the Jacobi denominator product of the
native odd-part magnitude. All original Bad coordinates remain present. -/
theorem binaryBad_odd_prime_product_eq_jacobi (K : PositiveDefiniteIntegralLattice 2) (b : ℤ) :
    (∏ p : ↥(massBadPrimeSet K), if p.val.val=2 then 1 else
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      legendreSym p.val.val b^padicValInt p.val.val K.binaryPrimitiveDiscriminant)=
      jacobiSym b (dyadicOddPart K.binaryPrimitiveDiscriminant).natAbs := by
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
    _=∏ p : ↥(massBadPrimeSet K), jacobiSym b p.val.val^padicValNat p.val.val m := by
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p.val.val=2
      · simp [hp,hv2]
      · letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
        simp only [if_neg hp]
        rw [padicValInt_dyadicOddPart p.val.val hp D hzero,
          jacobiSym.legendreSym.to_jacobiSym]
    _=∏ p ∈ massBadPrimeSet K, jacobiSym b p.val^padicValNat p.val m :=
      Finset.prod_coe_sort (massBadPrimeSet K) (fun p => jacobiSym b p.val^padicValNat p.val m)
    _=jacobiSym b m := primeSet_prod_jacobi b m hm (massBadPrimeSet K) hs

/-- The same good prime carrying the whole original tuple has the same
field sign as the proved full character. No splitting certificate is supplied. -/
theorem binaryNormProductCharacter_scalar_eq_fieldSign (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (l : {p : ℕ // p.Prime}) (hl : l∉massBadPrimeSet K)
    (hx : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(l.val : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=x p) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (K.binaryNormProductCharacter x : ℤ)=
      conductorPrimeSign (NumberField.discr
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : Fact l.val.Prime := ⟨l.prop⟩
  have htwo : l.val≠2 := not_mem_massBadPrimeSet_ne_two K hl
  rw [← K.binaryPrimitivePrimeSign_eq_fieldSign_of_good l hl,
    conductorPrimeSign_eq,if_neg htwo,K.binaryNormProductCharacter_scalar x l.val hx,
    K.binaryBad_odd_prime_product_eq_jacobi,
    jacobiSym.legendreSym.to_jacobiSym l.val,
    ← jacobiSym_eq_signed_oddPart K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_neg l.val (l.prop.eq_two_or_odd'.resolve_left htwo)]

/-- Every original scalar progression has exactly the full-character field
sign at every sufficiently large prime in that same progression. -/
theorem exists_progression_binaryFieldSign_eq_normCharacter
    (K : PositiveDefiniteIntegralLattice 2) (x : K.BinaryBadNormProduct) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    ∃ a : ℕ, 0<a ∧ a.Coprime K.binaryBadNormResidueModulus ∧
      ∀ l : {p : ℕ // p.Prime}, K.binaryBadNormResidueModulus<l.val →
        l.val ≡ a [MOD K.binaryBadNormResidueModulus] →
        conductorPrimeSign (NumberField.discr
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l.val=
          (K.binaryNormProductCharacter x : ℤ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  obtain ⟨a,ha,hcop,hclasses⟩ := K.exists_progression_binaryBadNormProduct x
  refine ⟨a,ha,hcop,?_⟩
  intro l hlarge hmod
  have hgood : l∉massBadPrimeSet K := by
    intro hmem
    have hd := K.prime_dvd_binaryBadNormResidueModulus ⟨l,hmem⟩
    exact (not_lt_of_ge (Nat.le_of_dvd K.binaryBadNormResidueModulus_pos hd)) hlarge
  exact (K.binaryNormProductCharacter_scalar_eq_fieldSign x l hgood (hclasses l.val hmod)).symm

/-- Every full-character kernel tuple is in the actual Picard image.
Native prime scalars and same-field splitting supply the original prime form. -/
theorem binaryNormCharacter_ker_le_badLocalNormImage (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    MonoidHom.ker (G := K.BinaryBadNormProduct) K.binaryNormProductCharacter ≤
      K.binaryBadLocalNormImage := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  intro x hx
  have hx1 : K.binaryNormProductCharacter x=1 := hx
  obtain ⟨l,hl,_,hgood,hclasses⟩ := K.exists_prime_scalar_binaryBadNormProduct x 0
  let p : {p : ℕ // p.Prime} := ⟨l,hl⟩
  have hs : conductorPrimeSign (NumberField.discr
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l=1 := by
    rw [← K.binaryNormProductCharacter_scalar_eq_fieldSign x p hgood hclasses,hx1]
    rfl
  exact K.mem_binaryBadLocalNormImage_of_field_split_prime x p hgood hs hclasses

/-- The actual image index divides two. Reciprocity must still rule out
index one; the opposite subgroup inclusion is not assumed or concluded. -/
theorem binaryBadLocalNormImage_index_dvd_two (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormImage.index∣2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  have h := Subgroup.index_dvd_of_le K.binaryNormCharacter_ker_le_badLocalNormImage
  rwa [K.binaryNormProductCharacter_ker_index] at h

/-- Exact remaining index alternatives on the actual original image. -/
theorem binaryBadLocalNormImage_index_one_or_two (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormImage.index=1 ∨ K.binaryBadLocalNormImage.index=2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact (Nat.dvd_prime Nat.prime_two).mp K.binaryBadLocalNormImage_index_dvd_two

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.primeSet_prod_jacobi
#assert_standard_axioms BinaryNormIdeal.jacobiSym_eq_signed_oddPart
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBad_odd_prime_product_eq_jacobi
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_scalar_eq_fieldSign
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_progression_binaryFieldSign_eq_normCharacter
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormCharacter_ker_le_badLocalNormImage
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage_index_dvd_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage_index_one_or_two
