import SMSFormula.BinaryOddNormCharacter

/-!
# The dyadic character on order-unit norm classes

The signed odd part of the discriminant is used, with its sign. The character
uses its residue modulo four, so no negative exponent is lost through toNat.
The norm premise below is IsUnit modulo eight, not merely nonzero.
-/

noncomputable section

namespace BinaryNormIdeal

/-- The signed odd part uses the native valuation of the same integer D. -/
def dyadicOddPart (D : ℤ) : ℤ := D / (2 : ℤ)^padicValInt 2 D

theorem dyadicOddPart_decomposition (D : ℤ) :
    D=(2 : ℤ)^padicValInt 2 D*dyadicOddPart D :=
  (Int.mul_ediv_cancel' (padicValInt_dvd (p := 2) D)).symm

theorem dyadicOddPart_odd (D : ℤ) (hD : D≠0) : Odd (dyadicOddPart D) := by
  apply Int.not_even_iff_odd.mp
  intro he
  obtain ⟨t,ht⟩ := even_iff_two_dvd.mp he
  have hd : (2 : ℤ)^(padicValInt 2 D+1)∣D := by
    refine ⟨t,?_⟩
    calc
      D=2^padicValInt 2 D*dyadicOddPart D := dyadicOddPart_decomposition D
      _=2^(padicValInt 2 D+1)*t := by rw [ht,pow_succ]; ring
  have h := (padicValInt_dvd_iff (p := 2) (padicValInt 2 D+1) D).mp hd
  rcases h with h | h
  · exact hD h
  · omega

/-- Pullback of chi4 from the unit residues modulo eight. -/
def dyadicChiFour : (ZMod 8)ˣ →* ℤˣ :=
  ZMod.χ₄.toUnitHom.comp
    (Units.map (ZMod.castHom (by decide : 4∣8) (ZMod 4)).toMonoidHom)

/-- Signed-safe dyadic formula. For odd d, the chi4 exponent is odd exactly
when d is three modulo four. The chi8 exponent is the native valuation. -/
def dyadicResidueCharacter (a : ℕ) (d : ℤ) : (ZMod 8)ˣ →* ℤˣ :=
  (if (d : ZMod 4)=1 then 1 else dyadicChiFour) * ZMod.χ₈.toUnitHom^a

theorem dyadicResidueCharacter_apply (a : ℕ) (d : ℤ) (u : (ZMod 8)ˣ) :
    (dyadicResidueCharacter a d u : ℤ)=
      (if (d : ZMod 4)=1 then 1 else ZMod.χ₄ (ZMod.cast (u : ZMod 8))) *
        ZMod.χ₈ (u : ZMod 8)^a := by
  unfold dyadicResidueCharacter
  split_ifs <;> rfl

private theorem odd_residue_unit : ∀ t : ZMod 8, IsUnit (2*t+1) := by decide

private theorem unit_square_mod_eight : ∀ x : ZMod 8, IsUnit (x^2) → x^2=1 := by decide

private theorem finite_dyadic_norm_cases :
    ∀ (k : Fin 3) (d x y : ZMod 8), IsUnit d →
      IsUnit (x^2-2^k.val*d*y^2) →
      (if (ZMod.cast d : ZMod 4)=1 then 1 else
        ZMod.χ₄ (ZMod.cast (x^2-2^k.val*d*y^2))) *
        ZMod.χ₈ (x^2-2^k.val*d*y^2)^(k.val+2)=1 := by decide

/-- The literal even-discriminant norm, with integer division completed
before extension to any commutative scalar ring. -/
theorem discriminantAlgebra_norm_of_two_pow (D d : ℤ) (a : ℕ)
    (hD : D=(2 : ℤ)^a*d) (ha : 2≤a)
    {R : Type*} [CommRing R] (z : DiscriminantAlgebra R D) :
    z.norm=z.re^2-(2 : R)^(a-2)*(d : R)*z.im^2 := by
  have hp : (2 : ℤ)^a=4*2^(a-2) := by
    have he : a=(a-2)+2 := by omega
    nth_rw 1 [he]
    rw [pow_add]
    ring
  have he : D=4*(2^(a-2)*d) := by rw [hD,hp]; ring
  have hr : D%2=0 := by omega
  have hc : -(((D%2)^2-D)/4)=2^(a-2)*d := by
    rw [hr,zero_pow (by decide : (2 : ℕ)≠0),zero_sub,he]
    omega
  have hcast : ((-(((D%2)^2-D)/4) : ℤ) : R)=(2 : R)^(a-2)*(d : R) := by
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using
      congrArg (fun n : ℤ => (n : R)) hc
  have hn (x y : R) : x*x+((D%2 : ℤ) : R)*x*y-
      ((-(((D%2)^2-D)/4) : ℤ) : R)*y*y=x^2-(2 : R)^(a-2)*(d : R)*y^2 := by
    rw [hcast,hr,Int.cast_zero]
    ring
  simp only [QuadraticAlgebra.norm_def]
  simpa only [Int.cast_one,neg_one_mul,← Int.cast_neg] using hn z.re z.im

/-- Odd signed integers give unit residues modulo eight. -/
theorem isUnit_intCast_mod_eight_of_odd (d : ℤ) (hd : Odd d) :
    IsUnit (d : ZMod 8) := by
  obtain ⟨t,ht⟩ := hd
  have he : (d : ZMod 8)=2*(t : ZMod 8)+1 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_one] using
      congrArg (fun n : ℤ => (n : ZMod 8)) ht
  rw [he]
  exact odd_residue_unit _

/-- The dyadic finite character annihilates every original finite order-unit
norm, for every valid nonzero decomposition. No norm-one lifting occurs. -/
theorem dyadicResidueCharacter_orderUnitNorm (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (a : ℕ) (d : ℤ) (hdecomp : D=(2 : ℤ)^a*d) (hd : Odd d)
    (z : (DiscriminantAlgebra (ZMod 8) D)ˣ) :
    dyadicResidueCharacter a d (orderUnitNorm (ZMod 8) D z)=1 := by
  by_cases ha0 : a=0
  · subst a
    have he : D=d := by simpa using hdecomp
    have hd2 := Int.odd_iff.mp hd
    have hd4 : d%4=1 := by rcases hD with h | h <;> omega
    have hc4 : (d : ZMod 4)=1 := by
      calc
        _=((d%4 : ℤ) : ZMod 4) := (ZMod.intCast_mod d 4).symm
        _=1 := by rw [hd4]; rfl
    simp [dyadicResidueCharacter,hc4]
  by_cases ha1 : a=1
  · subst a
    norm_num only [pow_one] at hdecomp
    have hd2 := Int.odd_iff.mp hd
    rcases hD with h | h <;> omega
  have ha : 2≤a := by omega
  have hn := discriminantAlgebra_norm_of_two_pow D d a hdecomp ha z.val
  have hu := (orderUnitNorm (ZMod 8) D z).isUnit
  change IsUnit z.val.norm at hu
  rw [hn] at hu
  by_cases hsmall : a≤4
  · let k : Fin 3 := ⟨a-2,by omega⟩
    have hf := finite_dyadic_norm_cases k (d : ZMod 8) z.val.re z.val.im
      (isUnit_intCast_mod_eight_of_odd d hd) hu
    have hc4 : (ZMod.cast (d : ZMod 8) : ZMod 4)=(d : ZMod 4) :=
      map_intCast (ZMod.castHom (by decide : 4∣8) (ZMod 4)) d
    have he : k.val+2=a := by dsimp [k]; omega
    rw [hc4,he] at hf
    apply Units.ext
    rw [dyadicResidueCharacter_apply]
    change (if (d : ZMod 4)=1 then 1 else ZMod.χ₄ (ZMod.cast z.val.norm)) *
      ZMod.χ₈ z.val.norm^a=1
    rw [hn]
    exact hf
  · have he : a-2=3+(a-5) := by omega
    have hp3 : (2 : ZMod 8)^3=0 := by decide
    have hp : (2 : ZMod 8)^(a-2)=0 := by rw [he,pow_add,hp3,zero_mul]
    rw [hp,zero_mul,zero_mul,sub_zero] at hu
    have hs := unit_square_mod_eight z.val.re hu
    have hz : orderUnitNorm (ZMod 8) D z=1 := by
      apply Units.ext
      change z.val.norm=1
      rw [hn,hp,zero_mul,zero_mul,sub_zero,hs]
    rw [hz,map_one]

/-- The scalar dyadic character uses the same D and actual native odd part. -/
def dyadicUnitHilbertCharacter (D : ℤ) : ℤ_[2]ˣ →* ℤˣ :=
  (dyadicResidueCharacter (padicValInt 2 D) (dyadicOddPart D)).comp (normResidueUnits 2)

theorem dyadicUnitHilbertCharacter_orderUnitNorm (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (hzero : D≠0) (z : (DiscriminantAlgebra ℤ_[2] D)ˣ) :
    dyadicUnitHilbertCharacter D (orderUnitNorm ℤ_[2] D z)=1 := by
  change dyadicResidueCharacter (padicValInt 2 D) (dyadicOddPart D)
    (normResidueUnits 2 (orderUnitNorm ℤ_[2] D z))=1
  rw [normResidueUnits_orderUnitNorm]
  exact dyadicResidueCharacter_orderUnitNorm D hD (padicValInt 2 D) (dyadicOddPart D)
    (dyadicOddPart_decomposition D) (dyadicOddPart_odd D hzero) (orderNormResidueUnits 2 D z)

theorem orderUnitNormSubgroup_le_dyadicUnitHilbertCharacter_ker (D : ℤ)
    (hD : D%4=0 ∨ D%4=1) (hzero : D≠0) :
    orderUnitNormSubgroup ℤ_[2] D ≤ (dyadicUnitHilbertCharacter D).ker := by
  rintro u ⟨z,rfl⟩
  exact dyadicUnitHilbertCharacter_orderUnitNorm D hD hzero z

/-- Descent through original order-unit norms, with no norm-one lift or
caller kernel certificate. The original quotient need not have order two. -/
def dyadicOrderNormCharacter (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hzero : D≠0) :
    OrderUnitNormQuotient ℤ_[2] D →* ℤˣ :=
  QuotientGroup.lift (orderUnitNormSubgroup ℤ_[2] D) (dyadicUnitHilbertCharacter D)
    (orderUnitNormSubgroup_le_dyadicUnitHilbertCharacter_ker D hD hzero)

theorem dyadicOrderNormCharacter_quotientMap (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (hzero : D≠0) (u : ℤ_[2]ˣ) :
    dyadicOrderNormCharacter D hD hzero (orderUnitNormQuotientMap ℤ_[2] D u)=
      dyadicUnitHilbertCharacter D u := rfl

/-- Evaluation at a natural-number scalar, with the parity of a negative odd part taken
into account. -/
theorem dyadicOrderNormCharacter_natCast (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (hzero : D≠0) (a : ℕ) (u : ℤ_[2]ˣ) (hu : (u : ℤ_[2])=(a : ℤ_[2])) :
    (dyadicOrderNormCharacter D hD hzero (orderUnitNormQuotientMap ℤ_[2] D u) : ℤ)=
      (if (dyadicOddPart D : ZMod 4)=1 then 1 else ZMod.χ₄ (a : ZMod 4)) *
        ZMod.χ₈ (a : ZMod 8)^padicValInt 2 D := by
  rw [dyadicOrderNormCharacter_quotientMap]
  change (dyadicResidueCharacter (padicValInt 2 D) (dyadicOddPart D)
    (normResidueUnits 2 u) : ℤ)=_
  rw [dyadicResidueCharacter_apply]
  have h8 : (normResidueUnits 2 u).val=(a : ZMod 8) := by
    change normResidueHom 2 (u : ℤ_[2])=(a : ZMod 8)
    rw [hu,map_natCast]
    rfl
  have h4 : (ZMod.cast (a : ZMod 8) : ZMod 4)=(a : ZMod 4) :=
    map_natCast (ZMod.castHom (by decide : 4∣8) (ZMod 4)) a
  rw [h8,h4]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- Two is an actual coordinate in the original Bad product. -/
def binaryDyadicBadPrime (K : PositiveDefiniteIntegralLattice 2) : ↥(massBadPrimeSet K) :=
  ⟨⟨2,Nat.prime_two⟩,(mem_massBadPrimeSet_iff K _).mpr (Or.inl rfl)⟩

/-- The full product character on the unchanged original order-unit tuple.
This construction alone proves neither surjectivity nor reciprocity. -/
def binaryNormProductCharacter (K : PositiveDefiniteIntegralLattice 2) : K.BinaryBadNormProduct →* ℤˣ where
  toFun x := K.binaryOddNormCharacter x *
    dyadicOrderNormCharacter K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg)
      (x K.binaryDyadicBadPrime)
  map_one' := by
    dsimp only [Pi.one_apply,binaryDyadicBadPrime]
    rw [map_one K.binaryOddNormCharacter,one_mul]
    exact map_one (dyadicOrderNormCharacter K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg))
  map_mul' x y := by
    dsimp only [Pi.mul_apply,binaryDyadicBadPrime]
    rw [map_mul,map_mul]
    ac_rfl

/-- The same literal scalar representing the whole original tuple evaluates
the full character as the actual odd product times the dyadic factor. -/
theorem binaryNormProductCharacter_scalar (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (a : ℕ)
    (ha : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(a : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=x p) :
    (K.binaryNormProductCharacter x : ℤ)=
      (∏ p : ↥(massBadPrimeSet K), if p.val.val=2 then 1 else
        letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
        legendreSym p.val.val a ^ padicValInt p.val.val K.binaryPrimitiveDiscriminant) *
      ((if (dyadicOddPart K.binaryPrimitiveDiscriminant : ZMod 4)=1 then 1 else
        ZMod.χ₄ (a : ZMod 4)) * ZMod.χ₈ (a : ZMod 8)^padicValInt 2 K.binaryPrimitiveDiscriminant) := by
  change (K.binaryOddNormCharacter x : ℤ) *
    (dyadicOrderNormCharacter K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg)
      (x K.binaryDyadicBadPrime) : ℤ)=_
  rw [K.binaryOddNormCharacter_scalar x a ha]
  congr 1
  have ht := ha K.binaryDyadicBadPrime
  change ∃ u : ℤ_[2]ˣ, (u : ℤ_[2])=(a : ℤ_[2]) ∧
    orderUnitNormQuotientMap ℤ_[2] K.binaryPrimitiveDiscriminant u=x K.binaryDyadicBadPrime at ht
  obtain ⟨u,hu,hq⟩ := ht
  rw [← hq]
  exact dyadicOrderNormCharacter_natCast _ _ _ a u hu

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.dyadicOddPart
#assert_standard_axioms BinaryNormIdeal.dyadicOddPart_decomposition
#assert_standard_axioms BinaryNormIdeal.dyadicOddPart_odd
#assert_standard_axioms BinaryNormIdeal.dyadicChiFour
#assert_standard_axioms BinaryNormIdeal.dyadicResidueCharacter
#assert_standard_axioms BinaryNormIdeal.dyadicResidueCharacter_apply
#assert_standard_axioms BinaryNormIdeal.discriminantAlgebra_norm_of_two_pow
#assert_standard_axioms BinaryNormIdeal.isUnit_intCast_mod_eight_of_odd
#assert_standard_axioms BinaryNormIdeal.dyadicResidueCharacter_orderUnitNorm
#assert_standard_axioms BinaryNormIdeal.dyadicUnitHilbertCharacter
#assert_standard_axioms BinaryNormIdeal.dyadicUnitHilbertCharacter_orderUnitNorm
#assert_standard_axioms BinaryNormIdeal.orderUnitNormSubgroup_le_dyadicUnitHilbertCharacter_ker
#assert_standard_axioms BinaryNormIdeal.dyadicOrderNormCharacter
#assert_standard_axioms BinaryNormIdeal.dyadicOrderNormCharacter_quotientMap
#assert_standard_axioms BinaryNormIdeal.dyadicOrderNormCharacter_natCast
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDyadicBadPrime
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_scalar
