import SMSFormula.BinaryGlobalNorm

/-!
# Finite local factors for an actual binary kernel ideal

The global norm witness is integral and invertible away from finitely many
rational primes. Local Hilbert90 gives the exact ideal identity at the
remaining primes. The factors can be one outside a finite set. No global
ideal patching or invertibility of a sum of ideals is assumed.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

/-- An integer denominator clears an actual canonical fraction. Taking the
norm of an order denominator gives a POSITIVE rational integer denominator. -/
theorem exists_pos_integer_fraction_denominator (a b c : ℤ)
    [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (z : FractionRing (CoefficientOrder a b c)) :
    ∃ n : ℤ, 0<n ∧ ∃ w : CoefficientOrder a b c,
      (n : FractionRing (CoefficientOrder a b c))*z=algebraMap _ _ w := by
  obtain ⟨r,s,hs,hrs⟩ := IsFractionRing.div_surjective (CoefficientOrder a b c) z
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hsf : algebraMap (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨s.norm,norm_pos_of_discriminant_neg a b c hD s hs0,r*star s,?_⟩
  have hn : (s.norm : FractionRing (CoefficientOrder a b c))=
      algebraMap _ _ s*algebraMap _ _ (star s) := by
    rw [← map_mul,← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simp
  rw [← hrs,hn,map_mul]
  field_simp

/-- Integer units are detected by actual rational-prime divisibility. -/
lemma isUnit_padic_intCast_of_not_dvd (n : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (h : ¬(p : ℤ) ∣ n) : IsUnit (n : ℤ_[p]) := by
  by_contra hu
  exact h (PadicInt.norm_intCast_lt_one_iff.mp (PadicInt.not_isUnit_iff.mp hu))

/-- An invertible scalar denominator gives an actual integral coefficient
preimage of the scalar-extended original fraction. -/
theorem exists_integral_fractionScalarMap (a b c : ℤ)
    [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (z : FractionRing (CoefficientOrder a b c)) (n : ℤ)
    (w : CoefficientOrder a b c)
    (hw : (n : FractionRing (CoefficientOrder a b c))*z=algebraMap _ _ w)
    (p : ℕ) [Fact (Nat.Prime p)] (hn : IsUnit (n : ℤ_[p])) :
    ∃ e : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]),
      coefficientScalarMap a b c (algebraMap ℤ_[p] ℚ_[p]) e=
        fractionScalarMap a b c hD ℚ_[p] z := by
  obtain ⟨u,hu⟩ := hn
  let e : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]) :=
    algebraMap ℤ_[p] _ (u⁻¹ : ℤ_[p]ˣ)*orderScalarMap a b c ℤ_[p] w
  refine ⟨e,?_⟩
  have hm := congrArg (fractionScalarMap a b c hD ℚ_[p]) hw
  rw [map_mul,map_intCast,fractionScalarMap_algebraMap] at hm
  have he : coefficientScalarMap a b c (algebraMap ℤ_[p] ℚ_[p]) e=
      algebraMap ℚ_[p] _ ((↑(u⁻¹) : ℤ_[p]) : ℚ_[p])*orderScalarMap a b c ℚ_[p] w := by
    apply QuadraticAlgebra.ext <;> simp [e,coefficientScalarMap,orderScalarMap]
  rw [he,← hm]
  have hi : algebraMap ℚ_[p] (CoefficientAlgebra (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p]))
      ((↑(u⁻¹) : ℤ_[p]) : ℚ_[p])*(n : CoefficientAlgebra (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p]))=1 := by
    have hn : (n : CoefficientAlgebra (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p]))=
        algebraMap ℚ_[p] _ ((u : ℤ_[p]) : ℚ_[p]) := by rw [hu]; simp
    have huval : ((↑(u⁻¹) : ℤ_[p]) : ℚ_[p])*((u : ℤ_[p]) : ℚ_[p])=1 := by
      simp only [← PadicInt.coe_mul,← Units.val_mul,inv_mul_cancel,Units.val_one,PadicInt.coe_one]
    rw [hn,← map_mul,huval,map_one]
  rw [← mul_assoc,hi,one_mul]

/-- Every actual global fraction-field unit comes from an actual integral
local-order unit outside a finite set of rational primes. -/
theorem exists_finite_fractionScalarMap_order_units (a b c : ℤ)
    [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (beta : (FractionRing (CoefficientOrder a b c))ˣ) :
    ∃ S : Finset ℕ, ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∉ S →
      ∃ e : (CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))ˣ,
        coefficientScalarMap a b c (algebraMap ℤ_[p] ℚ_[p]) e.val=
          fractionScalarMap a b c hD ℚ_[p] beta.val := by
  obtain ⟨n,hn,w,hw⟩ := exists_pos_integer_fraction_denominator a b c hD beta.val
  obtain ⟨m,hm,v,hv⟩ := exists_pos_integer_fraction_denominator a b c hD (beta⁻¹).val
  refine ⟨(n*m).natAbs.primeFactors,?_⟩
  intro p hp hS
  have hnot : ¬(p : ℤ) ∣ n*m := by
    intro hd
    apply hS
    apply Nat.mem_primeFactors.mpr
    exact ⟨hp.out,by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd,Int.natAbs_ne_zero.mpr (ne_of_gt (mul_pos hn hm))⟩
  have hpn : ¬(p : ℤ) ∣ n := fun h => hnot (dvd_mul_of_dvd_left h m)
  have hpm : ¬(p : ℤ) ∣ m := fun h => hnot (dvd_mul_of_dvd_right h n)
  obtain ⟨e,he⟩ := exists_integral_fractionScalarMap a b c hD beta.val n w hw p
    (isUnit_padic_intCast_of_not_dvd n p hpn)
  obtain ⟨f,hf⟩ := exists_integral_fractionScalarMap a b c hD (beta⁻¹).val m v hv p
    (isUnit_padic_intCast_of_not_dvd m p hpm)
  have hef : e*f=1 := by
    apply coefficientScalarMap_injective a b c (algebraMap ℤ_[p] ℚ_[p])
      (fun _ _ h => PadicInt.ext h)
    rw [map_mul,he,hf,map_one,← map_mul,← Units.val_mul,mul_inv_cancel,Units.val_one,map_one]
  exact ⟨Units.mkOfMulEqOne e f hef,he⟩

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped QuadraticAlgebra nonZeroDivisors

/-- At a unit leading coefficient the actual extended norm ideal is the
local order itself, including at dyadic and conductor primes. -/
theorem binaryPadicIdealExtension_eq_one_of_leading_unit (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)]
    (hA : IsUnit ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p
      (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  obtain ⟨u,hu⟩ := hA
  have hv : L.binaryPrimitivePolynomialOver ℤ_[p] ![1,0]=(u : ℤ_[p]) := by
    rw [binaryPrimitivePolynomialOver_apply]
    simpa using hu.symm
  rw [K.binaryPadicIdealExtension_principal L hD p ![1,0] u hv]
  have hgen : L.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hD ℤ_[p] ![1,0]=
      ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) := by
    unfold binaryLocalIdealGeneratorAt
    have hnv : normVector ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])
        (((2*L.pairingMatrix 0 1)/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])
        ((L.pairingMatrix 1 1/(L.binaryContent : ℤ) : ℤ) : ℤ_[p]) ![1,0]=
        ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) :
          CoefficientAlgebra ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])
            (((2*L.pairingMatrix 0 1)/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])
            ((L.pairingMatrix 1 1/(L.binaryContent : ℤ) : ℤ) : ℤ_[p])) := by
      apply QuadraticAlgebra.ext <;> simp [normVector]
    rw [hnv,map_intCast]
  rw [hgen]
  change Submodule.span _ {algebraMap (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
    (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)
    ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)}=1
  exact Submodule.span_singleton_algebraMap_of_isUnit
    ((hu ▸ u.isUnit).map (algebraMap ℤ_[p] (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)))

/-- The actual local ideal has a Hilbert90 twist relative to any chosen
Global norm witness. No field premise is imposed on the local algebra. -/
theorem exists_binaryPadicIdeal_unit_twist (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hk : letI := K.binaryDiscriminantOrder_isDomain
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD ∈ K.binaryIdealLocalNormKernel)
    (beta : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ)
    (hb : K.binaryFractionNorm beta.val=(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ))
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    ∃ y : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
      K.binaryPadicIdealExtension p
          (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)*
          Submodule.span _ {star y.val}=
        Submodule.span _ {K.binaryPadicFractionMap p beta.val}*Submodule.span _ {y.val} := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  obtain ⟨v,u,hu⟩ := L.binaryPrimitivePolynomialOver_padic_exists_unit p
  have hv := hu.symm
  have hm : orderUnitNormQuotientMap ℤ_[p] K.binaryPrimitiveDiscriminant u=1 :=
    (K.binaryIdealLocalNormHom_apply L hg hD p v u hv).symm.trans (hk p)
  obtain ⟨e,he⟩ := (orderUnitNormQuotientMap_eq_iff ℤ_[p] K.binaryPrimitiveDiscriminant u 1).mp hm
  simp only [Units.val_one,one_mul] at he
  let alpha := binaryPadicIdealGeneratorUnit K L hD p v u hv
  let E := Units.map (padicOrderMap p K.binaryPrimitiveDiscriminant).toMonoidHom e
  let B := Units.map (K.binaryPadicFractionMap p).toMonoidHom beta
  have hE : E.val.norm=((u : ℤ_[p]) : ℚ_[p]) := by
    change (padicOrderMap p K.binaryPrimitiveDiscriminant e.val).norm=_
    rw [padicOrderMap,norm_coefficientScalarMap,← he]
    rfl
  have hB : B.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) := by
    change (K.binaryPadicFractionMap p beta.val).norm=_
    rw [binaryPadicFractionMap,norm_fractionScalarMap]
    exact_mod_cast hb
  have hnorm : alpha.val.norm=(B*E).val.norm := by
    rw [Units.val_mul,map_mul,hB,hE]
    exact norm_binaryPadicIdealGeneratorUnit K L hD p v u hv
  have hd : ((K.binaryPrimitiveDiscriminant%2 : ℤ) : ℚ_[p])^2-
      4*((1 : ℤ) : ℚ_[p])*((((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4 : ℤ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast ne_of_lt K.binaryDiscriminantOrder_discriminant_neg
  obtain ⟨y,hy⟩ := exists_unit_norm_comparison _ _ _ hd alpha (B*E) hnorm
  refine ⟨y,?_⟩
  rw [K.binaryPadicIdealExtension_principal L hD p v u hv]
  change Submodule.span _ {alpha.val}*Submodule.span _ {star y.val}=
    Submodule.span _ {B.val}*Submodule.span _ {y.val}
  have hspan (x z : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) :
      Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {x}*
        Submodule.span _ {z}=Submodule.span _ {x*z} :=
    ((Submodule.spanSingleton _).map_mul x z).symm
  have hEu : Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {E.val}=1 :=
    Submodule.span_singleton_algebraMap_of_isUnit e.isUnit
  rw [hspan,hy]
  change Submodule.span _ {(B.val*E.val)*y.val}=_
  rw [← hspan,← hspan,hEu,mul_one]

/-- The local ideal twists have finite support: they can be chosen to be
One outside a finite set. This does not construct a global patched ideal. -/
theorem exists_finite_binaryPadicIdeal_unit_twists (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hk : letI := K.binaryDiscriminantOrder_isDomain
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD ∈ K.binaryIdealLocalNormKernel)
    (beta : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ)
    (hb : K.binaryFractionNorm beta.val=(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ)) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ S : Finset ℕ, ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      ∃ y : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
        (p ∉ S → y=1) ∧
        K.binaryPadicIdealExtension p
            (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)*
            Submodule.span _ {star y.val}=
          Submodule.span _ {K.binaryPadicFractionMap p beta.val}*Submodule.span _ {y.val} := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨S,hS⟩ := exists_finite_fractionScalarMap_order_units
    1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg beta
  let A : ℤ := L.pairingMatrix 0 0/(L.binaryContent : ℤ)
  refine ⟨S ∪ A.natAbs.primeFactors,?_⟩
  intro p hp
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  by_cases hmem : p ∈ S ∪ A.natAbs.primeFactors
  · obtain ⟨y,hy⟩ := K.exists_binaryPadicIdeal_unit_twist L hg hD hk beta hb p
    exact ⟨y,by simp [hmem],hy⟩
  · have hpS : p ∉ S := fun h => hmem (Finset.mem_union_left _ h)
    have hpA : ¬(p : ℤ) ∣ A := by
      intro hd
      apply hmem
      apply Finset.mem_union_right
      exact Nat.mem_primeFactors.mpr ⟨hp.out,Int.natCast_dvd.mp hd,
        Int.natAbs_ne_zero.mpr (ne_of_gt L.binaryPrimitivePolynomial_leading_pos)⟩
    obtain ⟨e,he⟩ := hS p hpS
    have hi := K.binaryPadicIdealExtension_eq_one_of_leading_unit L hD p
      (isUnit_padic_intCast_of_not_dvd A p hpA)
    have hbeta : Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
        {K.binaryPadicFractionMap p beta.val}=1 := by
      change Submodule.span _ {fractionScalarMap _ _ _ _ ℚ_[p] beta.val}=1
      rw [← he]
      exact Submodule.span_singleton_algebraMap_of_isUnit e.isUnit
    refine ⟨1,fun _ => rfl,?_⟩
    simpa only [Units.val_one,star_one,← Submodule.one_eq_span,mul_one] using hi.trans hbeta.symm

/-- Every actual kernel class has one original-(g,D) representative and
One global norm witness with local ideal factors that are one off a finite
set. This supplies finite-support input, not a global patched ideal. -/
theorem exists_binaryKernelClass_finite_local_factors (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hxi : letI := K.binaryDiscriminantOrder_isDomain
      xi ∈ K.binaryIdealLocalNormKernel) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent=K.binaryContent ∧
      ∃ hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant,
        L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD=xi ∧
        ∃ beta : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ,
          K.binaryFractionNorm beta.val=(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) ∧
          ∃ S : Finset ℕ, ∀ (p : ℕ) [Fact (Nat.Prime p)],
            letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
            ∃ y : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
              (p ∉ S → y=1) ∧
              K.binaryPadicIdealExtension p
                  (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)*
                  Submodule.span _ {star y.val}=
                Submodule.span _ {K.binaryPadicFractionMap p beta.val}*Submodule.span _ {y.val} := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨L,hg,hD,hclass,beta,hb,_⟩ := K.exists_binaryKernelClass_global_norm xi hxi
  exact ⟨L,hg,hD,hclass,beta,hb,
    K.exists_finite_binaryPadicIdeal_unit_twists L hg hD (hclass ▸ hxi) beta hb⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_pos_integer_fraction_denominator
#assert_standard_axioms BinaryNormIdeal.isUnit_padic_intCast_of_not_dvd
#assert_standard_axioms BinaryNormIdeal.exists_integral_fractionScalarMap
#assert_standard_axioms BinaryNormIdeal.exists_finite_fractionScalarMap_order_units
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_eq_one_of_leading_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryPadicIdeal_unit_twist
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_finite_binaryPadicIdeal_unit_twists
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryKernelClass_finite_local_factors
