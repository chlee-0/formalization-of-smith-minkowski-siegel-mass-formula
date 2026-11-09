import SMSFormula.BinaryIdealPatchBounds

/-!
# Actual invertible binary ideal patching

Finite coefficient CRT realizes the prescribed principal local spans of
the original-field intersection. The displayed reciprocal intersection
then gives its actual fractional-ideal inverse.
-/

namespace BinaryNormIdeal

open scoped nonZeroDivisors

/-- Clearing M inverse squared chooses a sufficient CRT modulus directly.
No explicit factorization of M or field structure on a quadratic algebra
is needed. -/
theorem exists_padic_pow_dvd_natCast_square (p : ℕ) [Fact (Nat.Prime p)]
    (M : ℕ) (hM : 0<M) : ∃ n : ℕ, (M : ℤ_[p])^2 ∣ (p : ℤ_[p])^n := by
  have hm : (M : ℚ_[p]) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  obtain ⟨n,u,hu⟩ := exists_pow_mul_padicInt p ((M : ℚ_[p])^2)⁻¹
  refine ⟨n,u,?_⟩
  apply PadicInt.ext
  push_cast
  rw [hu]
  field_simp

/-- The scalar divisibility transfers to the actual integral quadratic
order ideal, including at2 and in split local algebras. -/
lemma padicOrder_congruence_mem_natCast_square (p : ℕ) [Fact (Nat.Prime p)]
    (D : ℤ) (M n : ℕ)
    (h : (M : ℤ_[p])^2 ∣ (p : ℤ_[p])^n)
    (z : DiscriminantAlgebra ℤ_[p] D)
    (hz : z ∈ Ideal.span {(p : DiscriminantAlgebra ℤ_[p] D)^n}) :
    z ∈ Ideal.span {(M : DiscriminantAlgebra ℤ_[p] D)^2} := by
  have hh : (M : DiscriminantAlgebra ℤ_[p] D)^2 ∣
      (p : DiscriminantAlgebra ℤ_[p] D)^n := by
    simpa only [map_pow,map_natCast] using map_dvd (algebraMap ℤ_[p] (DiscriminantAlgebra ℤ_[p] D)) h
  exact Ideal.mem_span_singleton.mpr (dvd_trans hh (Ideal.mem_span_singleton.mp hz))

/-- A congruence modulo M squared becomes an exact scalar-M residual
after cancelling the ambient scalar unit M. The scalar ring need not be
a field, and the ambient algebra may have zero divisors. -/
lemma exists_order_residual_of_square_congruence {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (M : ℕ) (hM : IsUnit (M : A))
    (t w : R) (l z : A)
    (ht : algebraMap R A t=(M : A)*l)
    (hw : algebraMap R A w=(M : A)*z)
    (h : t-w ∈ Ideal.span {(M : R)^2}) :
    ∃ r : R, l-z=(M : A)*algebraMap R A r := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp h
  have hh := congrArg (algebraMap R A) hr
  rw [map_mul,map_pow,map_natCast,map_sub,ht,hw] at hh
  refine ⟨r,hM.mul_left_cancel ?_⟩
  linear_combination hh

/-- A nonzero integer scalar is a unit in the ambient quadratic Q_p
algebra. This does not claim it is an integral order unit. -/
lemma isUnit_natCast_padicAlgebra (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ)
    (M : ℕ) (hM : 0<M) : IsUnit (M : DiscriminantAlgebra ℚ_[p] D) := by
  have hu : IsUnit (M : ℚ_[p]) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (ne_of_gt hM))
  simpa only [map_natCast] using hu.map (algebraMap ℚ_[p] (DiscriminantAlgebra ℚ_[p] D))

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- Finite coefficient CRT realizes the actual principal local span of
the original intersection at every finite prime, including exceptional
dyadic and conductor primes. No closure or limiting argument is used. -/
theorem binaryPadicIdealExtension_patch_eq_span (K : PositiveDefiniteIntegralLattice 2)
    (S : Finset ℕ)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (hy : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∉ S → y p=1)
    (M : ℕ) (hM : 0<M) (hsupp : ∀ p : ℕ, p.Prime → p ∣ M → p ∈ S)
    (hbound : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*(y p).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)) ∧
      (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*((y p)⁻¹).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)))
    (J : K.BinaryDiscriminantFractionalIdeals)
    (hJ : (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=K.binaryIdealPatchSubmodule y)
    (hMJ : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ J)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p J=
      Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {(y p).val} := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  by_cases hpS : p ∈ S
  · apply le_antisymm (K.binaryPadicIdealExtension_le_patch_span y J hJ p)
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    let T := S.filter Nat.Prime
    have hT (q : ℕ) (hq : q ∈ T) : q.Prime := (Finset.mem_filter.mp hq).2
    have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hpS,Fact.out⟩
    have hn (q : ℕ) (hq : q ∈ T) :
        letI : Fact (Nat.Prime q) := ⟨hT q hq⟩
        ∃ n : ℕ, (M : ℤ_[q])^2 ∣ (q : ℤ_[q])^n := by
      letI : Fact (Nat.Prime q) := ⟨hT q hq⟩
      exact exists_padic_pow_dvd_natCast_square q M hM
    choose n hn using hn
    let e (q : ℕ) : ℕ := if hq : q ∈ T then n q hq else 0
    obtain ⟨t,ht⟩ := Submodule.mem_one.mp (hbound p).1
    let target (q : ℕ) [Fact (Nat.Prime q)] :
        DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant :=
      if hq : q=p then hq.symm ▸ t else 0
    obtain ⟨w,hw⟩ := exists_order_simultaneous_padic_residues
      K.binaryPrimitiveDiscriminant T hT e target
    have hcong (q : ℕ) (hq : q ∈ T) :
        letI : Fact (Nat.Prime q) := ⟨hT q hq⟩
        target q-orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[q] w ∈
          Ideal.span {(M : DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant)^2} := by
      letI : Fact (Nat.Prime q) := ⟨hT q hq⟩
      exact padicOrder_congruence_mem_natCast_square q _ M (e q)
        (by simpa only [e,dif_pos hq] using hn q hq) _ (hw q hq)
    let x : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant) :=
      algebraMap _ _ w/(M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    have hm0 : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ≠ 0 := by
      exact_mod_cast (ne_of_gt hM)
    have hx : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*x=
        algebraMap _ _ w := by dsimp [x]; field_simp
    have hxq (q : ℕ) [Fact (Nat.Prime q)] :
        letI := padicOrderAlgebra q K.binaryPrimitiveDiscriminant
        algebraMap (DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[q] K.binaryPrimitiveDiscriminant)
          (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
            (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[q] w)=
          (M : DiscriminantAlgebra ℚ_[q] K.binaryPrimitiveDiscriminant)*K.binaryPadicFractionMap q x := by
      letI := padicOrderAlgebra q K.binaryPrimitiveDiscriminant
      have hh := congrArg (K.binaryPadicFractionMap q) hx
      rw [map_mul,map_natCast,K.binaryPadicFractionMap_compatible] at hh
      exact hh.symm
    have hmul (q : ℕ) [Fact (Nat.Prime q)]
        (r : DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant) :
        letI := padicOrderAlgebra q K.binaryPrimitiveDiscriminant
        (M : DiscriminantAlgebra ℚ_[q] K.binaryPrimitiveDiscriminant)*
          padicOrderMap q K.binaryPrimitiveDiscriminant r ∈
          Submodule.span (DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant) {(y q).val} := by
      letI := padicOrderAlgebra q K.binaryPrimitiveDiscriminant
      have hh := (Submodule.span (DiscriminantAlgebra ℤ_[q] K.binaryPrimitiveDiscriminant)
        {(y q).val}).smul_mem r
          (natCast_mem_padic_unit_span q _ (y q) M (hbound q).2)
      simpa only [Algebra.smul_def,mul_comm] using hh
    obtain ⟨r,hr⟩ := exists_order_residual_of_square_congruence M
      (isUnit_natCast_padicAlgebra p _ M hM) (target p)
      (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p] w)
      (y p).val (K.binaryPadicFractionMap p x)
      (by simpa only [target,dif_pos rfl] using ht) (hxq p) (hcong p hpT)
    have hxJ : x ∈ J := by
      change x ∈ (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))
      rw [hJ]
      intro q hq
      letI := padicOrderAlgebra q K.binaryPrimitiveDiscriminant
      by_cases hqp : q=p
      · subst q
        have he : (y p).val-(M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*
            padicOrderMap p K.binaryPrimitiveDiscriminant r=K.binaryPadicFractionMap p x := by
          linear_combination hr
        rw [← he]
        exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self _) (hmul p r)
      · by_cases hqT : q ∈ T
        · obtain ⟨s,hs⟩ := exists_order_residual_of_square_congruence M
            (isUnit_natCast_padicAlgebra q _ M hM) 0
            (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
              (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[q] w)
            0 (K.binaryPadicFractionMap q x) (by simp) (hxq q)
            (by simpa only [target,dif_neg hqp] using hcong q hqT)
          have he : -(M : DiscriminantAlgebra ℚ_[q] K.binaryPrimitiveDiscriminant)*
              padicOrderMap q K.binaryPrimitiveDiscriminant s=K.binaryPadicFractionMap q x := by
            linear_combination hs
          rw [← he]
          simpa only [neg_mul] using Submodule.neg_mem _ (hmul q s)
        · have hqS : q ∉ S := fun h => hqT (Finset.mem_filter.mpr ⟨h,hq.out⟩)
          have hnot : ¬q ∣ M := fun h => hqS (hsupp q hq.out h)
          obtain ⟨u,hu⟩ := exists_integral_fractionScalarMap
            1 (K.binaryPrimitiveDiscriminant%2)
            (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
            K.binaryDiscriminantOrder_discriminant_neg x (M : ℤ) w
            (by simpa only [Int.cast_natCast] using hx) q
            (isUnit_padic_intCast_of_not_dvd (M : ℤ) q (by exact_mod_cast hnot))
          rw [hy q hqS,Units.val_one,← Submodule.one_eq_span]
          exact Submodule.mem_one.mpr ⟨u,hu⟩
    have hxlocal := K.binaryPadicFractionMap_mem_idealExtension J x hxJ p
    have hMlocal := K.binaryPadicFractionMap_mem_idealExtension J _ hMJ p
    rw [map_natCast] at hMlocal
    have hrlocal := (K.binaryPadicIdealExtension p J).smul_mem r hMlocal
    have he : K.binaryPadicFractionMap p x+
        padicOrderMap p K.binaryPrimitiveDiscriminant r*(M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)=
        (y p).val := by linear_combination -hr
    rw [← he]
    exact Submodule.add_mem _ hxlocal hrlocal
  · rw [K.binaryPadicIdealExtension_patch_eq_one_of_natCast_mem y J hJ M hMJ p
      (hy p hpS) (fun hd => hpS (hsupp p Fact.out hd)),hy p hpS,Units.val_one,← Submodule.one_eq_span]

/-- A finite family of ambient local units has an actual invertible
fractional-ideal patch in the original field. Its inverse is the reciprocal
intersection, and its local spans are exact at every finite prime. -/
theorem exists_binaryIdealPatch_unit (K : PositiveDefiniteIntegralLattice 2) (S : Finset ℕ)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (hy : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∉ S → y p=1) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ J : K.BinaryDiscriminantFractionalIdealsˣ,
      (J.val : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=K.binaryIdealPatchSubmodule y ∧
      ((J⁻¹).val : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=
          K.binaryIdealPatchSubmodule (fun p _ => (y p)⁻¹) ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicIdealExtension p J.val=
          Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {(y p).val} := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨M,hM,hsupp,hbound,I,Iprime,hI,hIprime,hMI,hMIprime,hupper,hupperprime,hprod⟩ :=
    K.exists_binaryIdealPatch_pair S y hy
  have hi (p : ℕ) [Fact (Nat.Prime p)] :
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p I=Submodule.span _ {(y p).val} :=
    K.binaryPadicIdealExtension_patch_eq_span S y hy M hM hsupp hbound I hI hMI p
  have hj (p : ℕ) [Fact (Nat.Prime p)] :
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p Iprime=Submodule.span _ {((y p)⁻¹).val} := by
    exact K.binaryPadicIdealExtension_patch_eq_span S (fun p _ => (y p)⁻¹)
      (by intro p hp hpn; change (y p)⁻¹=1; rw [hy p hpn,inv_one]) M hM hsupp
      (fun p _ => ⟨(hbound p).2,by simpa only [inv_inv] using (hbound p).1⟩)
      Iprime hIprime hMIprime p
  obtain ⟨J,hJ,hJinv⟩ := K.exists_binaryFractionalIdeal_unit_of_local_product I Iprime
    (M^2) (pow_pos hM 2) (by simpa only [Nat.cast_pow] using hprod) (by
      intro p hp
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      rw [hi p,hj p]
      calc
        Submodule.span _ {(y p).val}*Submodule.span _ {((y p)⁻¹).val}=
            Submodule.span _ {(y p).val*((y p)⁻¹).val} :=
          ((Submodule.spanSingleton _).map_mul _ _).symm
        _=1 := by rw [← Units.val_mul,mul_inv_cancel,Units.val_one,← Submodule.one_eq_span])
  refine ⟨J,?_,?_,?_⟩
  · simpa only [hJ] using hI
  · simpa only [hJinv] using hIprime
  · intro p hp
    rw [hJ]
    exact hi p

/-- Every actual kernel class has a global invertible patch and the exact
principal conjugate-product identity on the original carriers. -/
theorem exists_binaryKernelClass_global_patch (K : PositiveDefiniteIntegralLattice 2)
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
          ∃ J : K.BinaryDiscriminantFractionalIdealsˣ,
            L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD *
              Units.map (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
                (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)).toMonoidHom J=
              toPrincipalIdeal (DiscriminantOrder K.binaryPrimitiveDiscriminant)
                (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) beta * J := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨L,hg,hD,hclass,beta,hb,S,hlocal⟩ := K.exists_binaryKernelClass_finite_local_factors xi hxi
  choose y hyone hylocal using hlocal
  obtain ⟨J,hJ,hJinv,hpatch⟩ := K.exists_binaryIdealPatch_unit S y hyone
  refine ⟨L,hg,hD,hclass,beta,hb,J,?_⟩
  exact K.binaryIdeal_product_eq_of_invertible_local_patch L hD beta J
    (fun p _ => ⟨y p,hpatch p,hylocal p⟩)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_padic_pow_dvd_natCast_square
#assert_standard_axioms BinaryNormIdeal.padicOrder_congruence_mem_natCast_square
#assert_standard_axioms BinaryNormIdeal.exists_order_residual_of_square_congruence
#assert_standard_axioms BinaryNormIdeal.isUnit_natCast_padicAlgebra
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_patch_eq_span
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryIdealPatch_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryKernelClass_global_patch
