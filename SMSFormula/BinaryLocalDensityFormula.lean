import SMSFormula.BinaryFDualFibers
import SMSFormula.BinaryDensityProductReduction

/-!
# The original binary local density

The actual preferred-depth F-dual count and the original determinant norm
cancel the content powers. The original local norm index remains explicit.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Exact scalar cancellation in the binary density normalization.
All natural exponents are retained until conversion to positive real powers. -/
theorem binary_density_power_cancel (P : ℝ) (hP : 0<P) (h a v e : ℕ)
    (hv : v+2*e=2*h+a) (A c r eta : ℝ)
    (hcount : P^(2*v)*A=2*c*P^((h+a+3)+4*h+a)*r) :
    eta*(P^(2*h+a+3))⁻¹*A*P^((h : ℝ)+(a : ℝ)/2)=
      (2*eta*P^(4*e))*c*P^(-(a : ℝ)/2)*r := by
  have hA : A=(2*c*P^((h+a+3)+4*h+a)*r)/P^(2*v) := by
    apply (eq_div_iff (pow_ne_zero _ hP.ne')).mpr
    simpa only [mul_comm A] using hcount
  have hpow : (P^(2*h+a+3))⁻¹*P^((h+a+3)+4*h+a)*(P^(2*v))⁻¹*
      P^((h : ℝ)+(a : ℝ)/2)=P^(4*e)*P^(-(a : ℝ)/2) := by
    simp only [← Real.rpow_natCast,← Real.rpow_neg hP.le,← Real.rpow_add hP]
    congr 1
    have hvR : (v : ℝ)+2*(e : ℝ)=2*(h : ℝ)+(a : ℝ) := by exact_mod_cast hv
    push_cast
    linarith
  calc
    eta*(P^(2*h+a+3))⁻¹*A*P^((h : ℝ)+(a : ℝ)/2)=
        (2*eta*c*r)*((P^(2*h+a+3))⁻¹*P^((h+a+3)+4*h+a)*(P^(2*v))⁻¹*
          P^((h : ℝ)+(a : ℝ)/2)) := by rw [hA]; ring
    _=(2*eta*c*r)*(P^(4*e)*P^(-(a : ℝ)/2)) := by rw [hpow]
    _=_ := by ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The original determinant valuation keeps its exact dyadic shift. -/
theorem binary_det_val_add_two_eq_content (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    padicValInt p K.pairingDeterminant+2*(if p=2 then 1 else 0)=
      2*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs := by
  have hv := K.binary_polarDeterminant_val_eq_content p
  rw [K.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
    padicValInt.mul (pow_ne_zero _ (by norm_num)) (ne_of_gt K.pairingDeterminant_pos)] at hv
  by_cases hp : p=2
  · subst p
    have htwo : padicValInt 2 ((2 : ℤ)^2)=2 := by
      change padicValNat 2 (2^2)=2
      exact padicValNat.prime_pow 2
    have hh : 2+padicValInt 2 K.pairingDeterminant=
        2*padicValNat 2 K.binaryContent+padicValNat 2 K.binaryPrimitiveDiscriminant.natAbs := by
      simpa only [htwo] using hv
    change padicValInt 2 K.pairingDeterminant+2=_
    omega
  · rw [padicValInt_two_pow_eq_zero_of_ne_two p 2 hp,zero_add] at hv
    simpa only [if_neg hp,mul_zero,add_zero] using hv

/-- Exact real determinant-norm factor of the same original lattice.
The half-power is retained when the primitive valuation is odd. -/
theorem binary_polarNorm_half_inverse (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    ‖(K.polarDeterminant : ℤ_[p])‖^(-(1 : ℝ)/2)=
      (p : ℝ)^((padicValNat p K.binaryContent : ℝ)+
        (padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2) := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [polarDeterminant_padic_norm_eq_padicValInt,K.binary_polarDeterminant_val_eq_content,
    ← Real.rpow_mul hp.le]
  congr 1
  push_cast
  ring

/-- The actual original full-O local density at every prime. The original
order-unit norm quotient, actual conductor and same field remain explicit. -/
theorem binaryMassLocalFactor_eq_orderNormIndex (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    massLocalFactor K p=
      (if p=2 then (4 : ℝ) else 1)*
        (Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℝ)*
        (p : ℝ)^(-(padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2)*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (p : ℝ)^(2*padicValInt p K.pairingDeterminant)*
      (localDualQuotientCount K p (localDensityHenselExponent K p) : ℝ)=
      2*(Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℝ)*
        (p : ℝ)^((padicValNat p K.binaryContent+
            padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3)+
          4*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs)*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)) := by
    have hq := K.binary_dualCount_preferred_evaluated p
    by_cases hi : p ∣ K.binaryOrderIndex
    · simp only [if_pos hi] at hq ⊢
      exact_mod_cast hq
    · simp only [if_neg hi] at hq ⊢
      exact_mod_cast hq
  rw [K.binaryMassLocalFactor_eq_dualCount,K.binary_polarNorm_half_inverse,
    localDensityHenselExponent,K.binary_polarDeterminant_val_eq_content]
  have hcoeff : 2*(if p=2 then (1/8 : ℝ) else 1/2)*
      (p : ℝ)^(4*(if p=2 then 1 else 0) : ℕ)=(if p=2 then 4 else 1) := by
    by_cases hp2 : p=2
    · norm_num [hp2]
    · norm_num [hp2]
  have hh := binary_density_power_cancel (p : ℝ) hp
    (padicValNat p K.binaryContent) (padicValNat p K.binaryPrimitiveDiscriminant.natAbs)
    (padicValInt p K.pairingDeterminant) (if p=2 then 1 else 0)
    (K.binary_det_val_add_two_eq_content p) _ _ _ (if p=2 then 1/8 else 1/2) hc
  rw [hcoeff] at hh
  simpa only [localDensityHenselExponent,K.binary_polarDeterminant_val_eq_content] using hh

/-- Every actual inverse-density correction has an explicit original norm
index and conductor factor. The original bad-prime mask is not changed. -/
theorem binaryFieldFactor_mul_inverseDensity (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    K.binaryFieldEulerFactor ⟨p,Fact.out⟩*massLocalInverseFactorAtPrime K ⟨p,Fact.out⟩=
      (if p=2 then (1/4 : ℝ) else 1)*
        (Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℝ)⁻¹*
        (p : ℝ)^((padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2)*
        (if p ∣ K.binaryOrderIndex then K.binaryFieldEulerFactor ⟨p,Fact.out⟩ else 1) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hf := (K.binaryFieldEulerFactor_pos ⟨p,Fact.out⟩).ne'
  have hcoef : ((if p=2 then (4 : ℝ) else 1))⁻¹=(if p=2 then 1/4 else 1) := by
    split_ifs <;> norm_num
  change K.binaryFieldEulerFactor ⟨p,Fact.out⟩*(massLocalFactor K p)⁻¹=_
  rw [K.binaryMassLocalFactor_eq_orderNormIndex,
    show -(padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2=
      -((padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2) by ring,
    Real.rpow_neg hp.le]
  simp only [mul_inv_rev,inv_inv,hcoef]
  by_cases hi : p ∣ K.binaryOrderIndex
  · simp only [if_pos hi,inv_one,one_mul]
    ring
  · simp only [if_neg hi,mul_one]
    change K.binaryFieldEulerFactor ⟨p,Fact.out⟩*
      ((K.binaryFieldEulerFactor ⟨p,Fact.out⟩)⁻¹*
        ((p : ℝ)^((padicValNat p K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2)*
          ((Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℝ)⁻¹*
            (if p=2 then (1/4 : ℝ) else 1))))=_
    rw [← mul_assoc,mul_inv_cancel₀ hf,one_mul]
    ring

/-- The original finite bad-density correction contains no unevaluated
local density. All original bad primes and norm indices appear. -/
theorem binaryBadDensityCorrection_eq_normIndex_product (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    K.binaryBadDensityCorrection=∏ p ∈ massBadPrimeSet K,
      (letI : Fact p.val.Prime := ⟨p.prop⟩
       (if p.val=2 then (1/4 : ℝ) else 1)*
        (Nat.card (OrderUnitNormQuotient ℤ_[p.val] K.binaryPrimitiveDiscriminant) : ℝ)⁻¹*
        (p.val : ℝ)^((padicValNat p.val K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2)*
        (if p.val ∣ K.binaryOrderIndex then K.binaryFieldEulerFactor p else 1)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  unfold binaryBadDensityCorrection
  apply Finset.prod_congr rfl
  intro p _
  letI : Fact p.val.Prime := ⟨p.prop⟩
  exact K.binaryFieldFactor_mul_inverseDensity p.val

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.binary_density_power_cancel
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_det_val_add_two_eq_content
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_polarNorm_half_inverse
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryMassLocalFactor_eq_orderNormIndex

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldFactor_mul_inverseDensity
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadDensityCorrection_eq_normIndex_product
