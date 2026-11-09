import SMSFormula.BinaryCharacterFieldSigns

/-!
# Actual ideals of prime absolute norm

The quotient-cardinality carrier is classified by actual ring maps to F_p.
The original integral basis then identifies these maps with quadratic roots.
No splitting or fundamental-discriminant certificate is assumed.
-/

namespace BinaryNormIdeal

section PrimeQuotients

variable {R : Type*} [CommRing R]

/-- Every unital ring map to Z/p is onto, by integer residues. -/
theorem ringHomToZMod_surjective (p : ℕ) (f : R →+* ZMod p) : Function.Surjective f := by
  intro y
  obtain ⟨z,hz⟩ := ZMod.intCast_surjective y
  exact ⟨(z : R),(map_intCast f z).trans hz⟩

/-- Such maps are determined by their actual kernels, since every target
element is an integer residue. -/
theorem ringHomToZMod_kernel_injective (p : ℕ) :
    Function.Injective (fun f : R →+* ZMod p => (RingHom.ker f)) := by
  intro f g h
  dsimp only at h
  ext x
  obtain ⟨z,hz⟩ := ZMod.intCast_surjective (f x)
  have hx : x-(z : R) ∈ (RingHom.ker f) := by
    change f (x-(z : R))=0
    rw [map_sub,map_intCast,hz,sub_self]
  rw [h] at hx
  change g (x-(z : R))=0 at hx
  rw [map_sub,map_intCast] at hx
  exact hz.symm.trans (sub_eq_zero.mp hx).symm

/-- The kernel of an actual map to F_p has exactly p quotient classes. -/
theorem card_quotient_ringHomToZMod_ker (p : ℕ) (f : R →+* ZMod p) :
    Nat.card (R ⧸ (RingHom.ker f))=p := by
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ringHomToZMod_surjective p f)).toEquiv,Nat.card_zmod]

/-- Every actual quotient with p elements supplies a map with exactly
that kernel. No field or maximality hypothesis is supplied by the caller. -/
theorem exists_ringHomToZMod_of_card_prime (p : ℕ) [Fact p.Prime]
    (I : Ideal R) (hI : Nat.card (R ⧸ I)=p) :
    ∃ f : R →+* ZMod p, (RingHom.ker f)=I := by
  letI : Finite (R ⧸ I) := Nat.finite_of_card_ne_zero (hI ▸ (Fact.out : p.Prime).ne_zero)
  letI := Fintype.ofFinite (R ⧸ I)
  let e := ZMod.ringEquivOfPrime (R ⧸ I) (Fact.out : p.Prime)
    (by simpa only [Nat.card_eq_fintype_card] using hI)
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk I),?_⟩
  ext x
  change e.symm (Ideal.Quotient.mk I x)=0 ↔ x ∈ I
  rw [e.symm.map_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- A quotient with prime cardinality is a field, so the literal ideal
is maximal. This is proved from its actual quotient map. -/
theorem idealCardPrime_isMaximal (p : ℕ) [Fact p.Prime]
    (I : Ideal R) (hI : Nat.card (R ⧸ I)=p) : I.IsMaximal := by
  obtain ⟨f,hf⟩ := exists_ringHomToZMod_of_card_prime p I hI
  let e := RingHom.quotientKerEquivOfSurjective (ringHomToZMod_surjective p f)
  rw [← hf]
  exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField _) e.toMulEquiv)

/-- Actual ring maps to F_p and actual prime-cardinality quotient ideals
are in bijection. Its forward map takes the literal kernel. -/
noncomputable def ringHomsEquivIdealsCardPrime (p : ℕ) [Fact p.Prime] :
    (R →+* ZMod p) ≃ {I : Ideal R // Nat.card (R ⧸ I)=p} :=
  Equiv.ofBijective (fun f => ⟨(RingHom.ker f),card_quotient_ringHomToZMod_ker p f⟩) ⟨
    fun _ _ h => ringHomToZMod_kernel_injective p (congrArg Subtype.val h),by
      rintro ⟨I,hI⟩
      obtain ⟨f,hf⟩ := exists_ringHomToZMod_of_card_prime p I hI
      exact ⟨f,Subtype.ext hf⟩⟩

end PrimeQuotients

/-- A ring equivalence transports the actual ring-hom carriers by
precomposition. -/
def ringHomsEquivOfRingEquiv {R S F : Type*} [CommRing R] [CommRing S] [CommRing F]
    (e : R ≃+* S) : (S →+* F) ≃ (R →+* F) where
  toFun f := f.comp e.toRingHom
  invFun f := f.comp e.symm.toRingHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

/-- Ring maps from the actual integral coefficient algebra correspond
to its quadratic roots. Negating the generator matches the existing
root convention z^2+T*z-A=0. -/
noncomputable def quadraticRingHomsEquivRoots (A T : ℤ) (p : ℕ) :
    (QuadraticAlgebra ℤ A T →+* ZMod p) ≃
      {z : ZMod p // z*z+(T : ZMod p)*z-A=0} := by
  let e : (QuadraticAlgebra ℤ A T →+* ZMod p) ≃
      (QuadraticAlgebra ℤ A T →ₐ[ℤ] ZMod p) := {
    toFun := RingHom.toIntAlgHom
    invFun := AlgHom.toRingHom
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine (e.trans (QuadraticAlgebra.lift (R := ℤ) (a := A) (b := T)).symm).trans ?_
  refine {
    toFun := fun z => ⟨-z.val,?_⟩
    invFun := fun z => ⟨-z.val,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h := z.prop
    simp only [zsmul_eq_mul,mul_one] at h
    linear_combination h
  · simp only [zsmul_eq_mul,mul_one]
    linear_combination z.prop
  · intro z
    apply Subtype.ext
    exact neg_neg _
  · intro z
    apply Subtype.ext
    exact neg_neg _

/-- An actual integral basis starting with one identifies ring maps to
F_p with roots of its original quadratic multiplication law. -/
noncomputable def basisRingHomsEquivRoots {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (he : e 0=1) (p : ℕ) :
    (B →+* ZMod p) ≃ {z : ZMod p //
      z*z+(basisSquareTrace e : ZMod p)*z-basisSquareConstant e=0} :=
  (ringHomsEquivOfRingEquiv (basisQuadraticEquiv e he).toRingEquiv).trans
    (quadraticRingHomsEquivRoots _ _ p)

/-- The dyadic quadratic root count includes the repeated-root case. -/
theorem card_quadraticRoots_mod_two (A T : ZMod 2) :
    Nat.card {z : ZMod 2 // z*z+T*z-A=0} =
      if T=0 then 1 else if A=0 then 2 else 0 := by
  fin_cases A <;> fin_cases T <;> rw [Nat.card_eq_fintype_card] <;> decide

/-- The exact root count at two uses the same coefficient discriminant. -/
theorem card_quadraticRoots_two_chi_eight (A T : ℤ) :
    (Nat.card {z : ZMod 2 // z*z+(T : ZMod 2)*z-A=0} : ℤ) =
      1+ZMod.χ₈ ((T^2+4*A : ℤ) : ZMod 8) := by
  have h : ∀ a t : ZMod 2,
      (if t=0 then (1 : ℤ) else if a=0 then 2 else 0) +
        (if t=0 then (2 : ℤ) else if a=0 then 1 else 3)=3 := by decide
  rw [card_quadraticRoots_mod_two]
  push_cast
  have hc := dyadic_parity_count_eq_chi_eight A T
  push_cast at hc
  linarith [h A T]

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- Actual ideals in the same maximal order with absolute norm p are
classified by the original integral-basis quadratic roots. -/
noncomputable def maximalNormPrimeIdealsEquivRoots (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=p} ≃
      {z : ZMod p // z*z+(basisSquareTrace (maximalOrderBasisOne a b c hD) : ZMod p)*z-
        basisSquareConstant (maximalOrderBasisOne a b c hD)=0} := by
  letI := fractionNumberField a b c hD
  change {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
    Nat.card (_ ⧸ J)=p} ≃ _
  exact (ringHomsEquivIdealsCardPrime p).symm.trans
    (basisRingHomsEquivRoots (maximalOrderBasisOne a b c hD)
      (maximalOrderBasisOne_zero a b c hD) p)

/-- The prime-norm ideals are finite on their actual carrier, before
any splitting type or Euler recurrence is asserted. -/
theorem finite_maximalNormPrimeIdeals (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    Finite {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=p} := by
  letI := fractionNumberField a b c hD
  exact Finite.of_equiv _ (maximalNormPrimeIdealsEquivRoots a b c hD p).symm

/-- Every actual ideal of prime absolute norm in the same maximal order
is maximal. No extra prime-ideal premise is needed for later factorization. -/
theorem maximalNormPrimeIdeal_isMaximal (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    ∀ J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))),
      Ideal.absNorm J=p → J.IsMaximal := by
  letI := fractionNumberField a b c hD
  intro J hJ
  exact idealCardPrime_isMaximal p J hJ

/-- The actual Dedekind-zeta coefficient at p is one plus the same field
prime sign, including p=2 and ramified primes. -/
theorem card_maximalNormPrimeIdeals (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] :
    letI := fractionNumberField a b c hD
    (Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=p} : ℤ) =
        1+conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p := by
  letI := fractionNumberField a b c hD
  rw [Nat.card_congr (maximalNormPrimeIdealsEquivRoots a b c hD p),conductorPrimeSign_eq]
  by_cases hp : p=2
  · subst p
    rw [if_pos rfl,card_quadraticRoots_two_chi_eight,
      maximalOrder_parameters_discriminant a b c hD]
  · rw [if_neg hp,card_quadraticRoots_odd p hp,
      maximalOrder_parameters_discriminant a b c hD,add_comm]

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.ringHomToZMod_surjective
#assert_standard_axioms BinaryNormIdeal.ringHomToZMod_kernel_injective
#assert_standard_axioms BinaryNormIdeal.card_quotient_ringHomToZMod_ker
#assert_standard_axioms BinaryNormIdeal.exists_ringHomToZMod_of_card_prime
#assert_standard_axioms BinaryNormIdeal.ringHomsEquivIdealsCardPrime
#assert_standard_axioms BinaryNormIdeal.ringHomsEquivOfRingEquiv
#assert_standard_axioms BinaryNormIdeal.quadraticRingHomsEquivRoots
#assert_standard_axioms BinaryNormIdeal.basisRingHomsEquivRoots
#assert_standard_axioms BinaryNormIdeal.card_quadraticRoots_mod_two
#assert_standard_axioms BinaryNormIdeal.card_quadraticRoots_two_chi_eight
#assert_standard_axioms BinaryNormIdeal.maximalNormPrimeIdealsEquivRoots
#assert_standard_axioms BinaryNormIdeal.card_maximalNormPrimeIdeals

#assert_standard_axioms BinaryNormIdeal.idealCardPrime_isMaximal
#assert_standard_axioms BinaryNormIdeal.finite_maximalNormPrimeIdeals
#assert_standard_axioms BinaryNormIdeal.maximalNormPrimeIdeal_isMaximal
