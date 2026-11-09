import SMSFormula.BinaryResiduePrimePowers
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Odd-prime units on the actual quadratic residue carriers

Completing the square counts the roots, and the nonzero second-coordinate
slope counts norm-unit pairs. The actual field discriminant stays fixed.
-/

namespace BinaryNormIdeal

section Field
variable {F : Type*} [Field F]

/-- The exact root/square-root correspondence, including zero discriminant. -/
noncomputable def quadraticRootsEquivSqrts (A T : F) (h2 : (2 : F) ≠ 0) :
    {z : F // z*z+T*z-A=0} ≃ {s : F // s^2=T^2+4*A} where
  toFun z := ⟨2*z.val+T,by linear_combination 4*z.prop⟩
  invFun s := ⟨(s.val-T)/2,by field_simp; linear_combination s.prop⟩
  left_inv z := by apply Subtype.ext; dsimp only; field_simp; ring
  right_inv s := by apply Subtype.ext; dsimp only; field_simp; ring

/-- The homogeneous norm is the slope polynomial times the square of the
second coordinate. This identity is valid in split and repeated-root cases. -/
theorem norm_eq_slope_mul_square (A T x y : F) (hy : y ≠ 0) :
    x*x+T*x*y-A*y*y=((x/y)*(x/y)+T*(x/y)-A)*(y*y) := by
  field_simp

/-- Direct norm-unit pair decomposition. At y=0, x is nonzero. At y!=0,
the slope avoids the quadratic roots. This is an actual carrier bijection. -/
noncomputable def normNonzeroPairsEquiv (A T : F) :
    {p : F × F // p.1*p.1+T*p.1*p.2-A*p.2*p.2 ≠ 0} ≃
      {x : F // x ≠ 0} ⊕ ({y : F // y ≠ 0} × {z : F // z*z+T*z-A ≠ 0}) := by
  classical
  refine {
    toFun := fun p => if hy : p.val.2=0 then
      Sum.inl ⟨p.val.1,by intro hx; exact p.prop (by simp [hx,hy])⟩
      else Sum.inr (⟨p.val.2,hy⟩,⟨p.val.1/p.val.2,by
        intro hz
        apply p.prop
        rw [norm_eq_slope_mul_square A T _ _ hy,hz,zero_mul]⟩)
    invFun := fun s => match s with
      | Sum.inl x => ⟨(x.val,0),by simpa using mul_ne_zero x.prop x.prop⟩
      | Sum.inr (y,z) => ⟨(z.val*y.val,y.val),by
          have h := mul_ne_zero z.prop (mul_ne_zero y.prop y.prop)
          convert h using 1; ring⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    dsimp only
    split_ifs with hy
    · apply Subtype.ext
      exact Prod.ext rfl hy.symm
    · apply Subtype.ext
      change (p.val.1/p.val.2*p.val.2,p.val.2)=p.val
      rw [div_mul_cancel₀ _ hy]
  · rintro (x|⟨y,z⟩)
    · dsimp only
      rw [dif_pos rfl]
    · dsimp only
      rw [dif_neg y.prop]
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact mul_div_cancel_right₀ _ y.prop

end Field

section OddPrime
variable (p : ℕ) [Fact p.Prime]

/-- The complete root count, including the repeated-root discriminant zero. -/
theorem card_quadraticRoots_odd (hp : p ≠ 2) (A T : ℤ) :
    (Nat.card {z : ZMod p // z*z+(T : ZMod p)*z-A=0} : ℤ) =
      legendreSym p (T^2+4*A)+1 := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h1
  have h := legendreSym.card_sqrts (p := p) hp (T^2+4*A)
  rw [Nat.card_congr (quadraticRootsEquivSqrts (A : ZMod p) (T : ZMod p) h2)]
  simpa only [Nat.card_eq_fintype_card,Set.toFinset_card,Int.cast_add,Int.cast_pow,
    Int.cast_mul,Int.cast_ofNat] using h

/-- The odd-prime norm-unit count on the literal coefficient algebra. -/
theorem card_quadraticUnits_odd (hp : p ≠ 2) (A T : ℤ) :
    (Nat.card (QuadraticAlgebra (ZMod p) (A : ZMod p) (T : ZMod p))ˣ : ℤ) =
      ((p : ℤ)-1)*((p : ℤ)-legendreSym p (T^2+4*A)) := by
  classical
  let f : ZMod p → ZMod p := fun z => z*z+(T : ZMod p)*z-A
  have hnz : Nat.card {x : ZMod p // x ≠ 0}=p-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp
  have hnr : Nat.card {x : ZMod p // f x ≠ 0}=
      p-Nat.card {x : ZMod p // f x=0} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [ZMod.card,Nat.card_eq_fintype_card]
  have hrle : Nat.card {x : ZMod p // f x=0} ≤ p := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using
      Fintype.card_subtype_le (fun x : ZMod p => f x=0)
  have hu : Nat.card (QuadraticAlgebra (ZMod p) (A : ZMod p) (T : ZMod p))ˣ =
      Nat.card {q : ZMod p × ZMod p // q.1*q.1+(T : ZMod p)*q.1*q.2-A*q.2*q.2 ≠ 0} := by
    simpa only [isUnit_iff_ne_zero] using
      Nat.card_congr (quadraticUnitsEquivNormPairs (A : ZMod p) (T : ZMod p))
  rw [hu,Nat.card_congr (normNonzeroPairsEquiv (A : ZMod p) (T : ZMod p)),
    Nat.card_sum,Nat.card_prod,hnz,hnr]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp1,Nat.cast_one,Nat.cast_sub hrle]
  have hr : (Nat.card {x : ZMod p // f x=0} : ℤ)=legendreSym p (T^2+4*A)+1 :=
    card_quadraticRoots_odd p hp A T
  rw [hr]
  ring

end OddPrime

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The odd-prime numerator uses the same actual maximal order and same
Field discriminant. No caller classification or root count occurs. -/
theorem card_maximalOrderResidueUnits_odd_fieldDiscr (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    letI := fractionNumberField a b c hD
    (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {(p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))})ˣ : ℤ) =
      ((p : ℤ)-1)*((p : ℤ)-legendreSym p
        (NumberField.discr (FractionRing (CoefficientOrder a b c)))) := by
  letI := fractionNumberField a b c hD
  rw [Nat.card_congr (Units.mapEquiv (maximalOrderResidueEquiv a b c hD p).toMulEquiv).toEquiv,
    card_quadraticUnits_odd p hp,maximalOrder_parameters_discriminant a b c hD]

/-- Every odd-prime power numerator is evaluated on the same actual carrier. -/
theorem card_maximalOrderResidueUnits_odd_power (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) (hk : k ≠ 0) :
    letI := fractionNumberField a b c hD
    (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {((p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))^k)})ˣ : ℤ) =
      ((p : ℤ)-1)*((p : ℤ)-legendreSym p
        (NumberField.discr (FractionRing (CoefficientOrder a b c))))*(p : ℤ)^(2*(k-1)) := by
  letI := fractionNumberField a b c hD
  have h := card_maximalOrderResidueUnits_power a b c hD p k (Fact.out : p.Prime).ne_zero hk
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hc
  rw [card_maximalOrderResidueUnits_odd_fieldDiscr a b c hD p hp] at hc
  exact hc

/-- One actual prime-power formula, retaining the standard dyadic character
and the same field Legendre symbol at odd primes. -/
theorem card_maximalOrderResidueUnits_prime_power (hD : b^2-4*a*c<0)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k ≠ 0) :
    letI := fractionNumberField a b c hD
    (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {((p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))^k)})ˣ : ℤ) =
      ((p : ℤ)-1)*((p : ℤ)-(if p=2 then
        ZMod.χ₈ (NumberField.discr (FractionRing (CoefficientOrder a b c)) : ZMod 8)
        else legendreSym p (NumberField.discr (FractionRing (CoefficientOrder a b c))))) *
          (p : ℤ)^(2*(k-1)) := by
  letI := fractionNumberField a b c hD
  by_cases hp : p=2
  · subst p
    simpa using card_maximalOrderResidueUnits_two_power a b c hD k hk
  · simpa only [if_neg hp] using card_maximalOrderResidueUnits_odd_power a b c hD p hp k hk

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.quadraticRootsEquivSqrts
#assert_standard_axioms BinaryNormIdeal.norm_eq_slope_mul_square
#assert_standard_axioms BinaryNormIdeal.normNonzeroPairsEquiv
#assert_standard_axioms BinaryNormIdeal.card_quadraticRoots_odd
#assert_standard_axioms BinaryNormIdeal.card_quadraticUnits_odd
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_odd_fieldDiscr
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_odd_power
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_prime_power
