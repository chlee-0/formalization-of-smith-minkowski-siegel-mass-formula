import SMSFormula.BinaryMaximalResidueModel
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Actual residue units through positive powers

The actual quotient by a positive power detects units modulo the first
power. Rank two gives the exact number of lifts. The dyadic sign uses the
Same field discriminant.
-/

namespace BinaryNormIdeal

section Powers

variable {R : Type*} [CommRing R]

/-- Reduction on the literal ideal-power quotients. -/
def idealPowerReduction (I : Ideal R) (k : ℕ) (hk : k ≠ 0) :
    (R ⧸ I^k) →+* R ⧸ I :=
  Ideal.quotientMap I (RingHom.id R) (by simpa using Ideal.pow_le_self (I := I) hk)

theorem idealPowerReduction_surjective (I : Ideal R) (k : ℕ) (hk : k ≠ 0) :
    Function.Surjective (idealPowerReduction I k hk) := by
  apply Ideal.quotientMap_surjective
  exact Function.surjective_id

/-- No maximality, oddness or prime premise is needed for unit detection. -/
theorem isUnit_idealPowerReduction_iff (I : Ideal R) (k : ℕ) (hk : k ≠ 0)
    (x : R ⧸ I^k) : IsUnit x ↔ IsUnit (idealPowerReduction I k hk x) := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [idealPowerReduction] using
    (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I hk (x := z))

/-- Every actual residue unit lifts through each positive ideal power. -/
theorem idealPowerReduction_units_surjective (I : Ideal R) (k : ℕ) (hk : k ≠ 0) :
    Function.Surjective (Units.map (idealPowerReduction I k hk).toMonoidHom) := by
  intro u
  obtain ⟨x,hx⟩ := idealPowerReduction_surjective I k hk u.val
  have hunit : IsUnit x := (isUnit_idealPowerReduction_iff I k hk x).mpr (hx ▸ u.isUnit)
  refine ⟨hunit.unit,?_⟩
  apply Units.ext
  change idealPowerReduction I k hk hunit.unit.val=u.val
  rw [IsUnit.unit_spec,hx]

end Powers

section Kernel

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Subtracting one identifies a unit reduction kernel with the additive
kernel. Unit detection supplies the inverse on the actual carriers. -/
noncomputable def unitsKernelEquivAddKernel (f : R →+* S)
    (h : ∀ x, IsUnit x ↔ IsUnit (f x)) :
    (Units.map f.toMonoidHom).ker ≃ f.toAddMonoidHom.ker where
  toFun u := ⟨u.val.val-1,by
    have hu : f u.val.val=1 := congrArg Units.val u.prop
    change f (u.val.val-1)=0
    rw [map_sub,map_one,hu,sub_self]⟩
  invFun x := ⟨((h (1+x.val)).mpr (by
    have hx : f x.val=0 := x.prop
    rw [map_add,map_one,hx,add_zero]
    exact isUnit_one)).unit,by
      apply Units.ext
      change f _=1
      rw [IsUnit.unit_spec,map_add,map_one]
      have hx : f x.val=0 := x.prop
      rw [hx,add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    change _=u.val.val
    rw [IsUnit.unit_spec]
    ring
  right_inv x := by
    apply Subtype.ext
    dsimp only
    rw [IsUnit.unit_spec]
    ring

end Kernel

/-- Exact additive reduction-kernel count for an actual rank-two integer
algebra. Modulus one and exponent one remain included. -/
theorem card_scalarPowerReduction_addKernel {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    Nat.card (idealPowerReduction (Ideal.span {(n : B)}) k hk).toAddMonoidHom.ker =
      n^(2*(k-1)) := by
  let f := idealPowerReduction (Ideal.span {(n : B)}) k hk
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
    f.toAddMonoidHom (idealPowerReduction_surjective _ k hk)).toEquiv] at hc
  have hbig : Nat.card (B ⧸ (Ideal.span {(n : B)})^k)=(n^k)^2 := by
    rw [Ideal.span_singleton_pow,← Nat.cast_pow]
    exact card_quotient_span_nat e _ (pow_ne_zero _ hn)
  rw [hbig,card_quotient_span_nat e n hn] at hc
  have hp : (n^k)^2=n^2*n^(2*(k-1)) := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [Nat.succ_sub_one,pow_succ,mul_pow]
    rw [mul_comm 2 l,pow_mul]
    ring
  rw [hp] at hc
  exact (mul_left_cancel₀ (pow_ne_zero 2 hn) hc).symm

/-- The exact number of unit lifts through a scalar power is n^(2*(k-1)).
This holds before any quadratic residue sign or splitting type is chosen. -/
theorem card_scalarPowerQuotient_units {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    Nat.card (B ⧸ Ideal.span {((n : B)^k)})ˣ =
      Nat.card (B ⧸ Ideal.span {(n : B)})ˣ * n^(2*(k-1)) := by
  let f := idealPowerReduction (Ideal.span {(n : B)}) k hk
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Units.map f.toMonoidHom).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (Units.map f.toMonoidHom) (idealPowerReduction_units_surjective _ k hk)).toEquiv,
    Nat.card_congr (unitsKernelEquivAddKernel f (isUnit_idealPowerReduction_iff _ k hk)),
    card_scalarPowerReduction_addKernel e n k hn hk,Ideal.span_singleton_pow] at hc
  exact hc

/-- The coefficient-parity count is exactly two minus the standard dyadic
quadratic character of the integral basis discriminant. -/
theorem dyadic_parity_count_eq_chi_eight (A T : ℤ) :
    (if (T : ZMod 2)=0 then (2 : ℤ) else if (A : ZMod 2)=0 then 1 else 3) =
      2-ZMod.χ₈ ((T^2+4*A : ℤ) : ZMod 8) := by
  let f := ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2)
  have h : ∀ a t : ZMod 8,
      (if f t=0 then (2 : ℤ) else if f a=0 then 1 else 3) =
        2-ZMod.χ₈ (t^2+4*a) := by decide
  simpa only [map_intCast,Int.cast_add,Int.cast_pow,Int.cast_mul,Int.cast_ofNat] using h A T

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The dyadic count uses the same field discriminant, never the original
order discriminant at conductor primes. -/
theorem card_maximalOrderResidueUnits_two_fieldDiscr (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {(2 : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))})ˣ : ℤ) =
        2-ZMod.χ₈ (NumberField.discr (FractionRing (CoefficientOrder a b c)) : ZMod 8) := by
  letI := fractionNumberField a b c hD
  rw [card_maximalOrderResidueUnits_mod_two a b c hD]
  push_cast
  rw [dyadic_parity_count_eq_chi_eight, maximalOrder_parameters_discriminant a b c hD]

/-- Exact unit counts through powers in the actual maximal order. -/
theorem card_maximalOrderResidueUnits_power (hD : b^2-4*a*c<0)
    (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {((n : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))^k)})ˣ =
        Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
          Ideal.span {(n : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))})ˣ *
            n^(2*(k-1)) :=
  card_scalarPowerQuotient_units (maximalOrderBasisOne a b c hD) n k hn hk

/-- The evaluated dyadic prime-power numerator on the same actual maximal order. -/
theorem card_maximalOrderResidueUnits_two_power (hD : b^2-4*a*c<0) (k : ℕ) (hk : k ≠ 0) :
    letI := fractionNumberField a b c hD
    (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {((2 : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))^k)})ˣ : ℤ) =
        (2-ZMod.χ₈ (NumberField.discr (FractionRing (CoefficientOrder a b c)) : ZMod 8)) *
          (2 : ℤ)^(2*(k-1)) := by
  letI := fractionNumberField a b c hD
  have h := card_maximalOrderResidueUnits_power a b c hD 2 k (by norm_num) hk
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hc
  simpa only [Nat.cast_ofNat,card_maximalOrderResidueUnits_two_fieldDiscr a b c hD] using hc

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.idealPowerReduction
#assert_standard_axioms BinaryNormIdeal.idealPowerReduction_surjective
#assert_standard_axioms BinaryNormIdeal.isUnit_idealPowerReduction_iff
#assert_standard_axioms BinaryNormIdeal.idealPowerReduction_units_surjective
#assert_standard_axioms BinaryNormIdeal.unitsKernelEquivAddKernel
#assert_standard_axioms BinaryNormIdeal.card_scalarPowerReduction_addKernel
#assert_standard_axioms BinaryNormIdeal.card_scalarPowerQuotient_units
#assert_standard_axioms BinaryNormIdeal.dyadic_parity_count_eq_chi_eight
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_two_fieldDiscr
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_power
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_two_power
