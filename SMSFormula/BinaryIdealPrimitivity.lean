import SMSFormula.BinaryIdealNormalization

/-!
# Invertible binary norm ideals have primitive coefficients

A common coefficient divisor would make theta/d an integral ideal
multiplier. The exact multiplier ring of an invertible ideal excludes it.
The argument stays in the original order and its fraction field.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

private lemma divided_theta_action (A B C d : ℤ) (hA : A ≠ 0)
    (hdA : d ∣ A) (hdB : d ∣ B) (hdC : d ∣ C)
    (z : CoefficientOrder A B C) (hz : z ∈ normIdeal A B C) :
    ∃ w ∈ normIdeal A B C,
      (d : CoefficientOrder A B C)*w = QuadraticAlgebra.omega*z := by
  obtain ⟨a,ha⟩ := hdA
  obtain ⟨b,hb⟩ := hdB
  obtain ⟨c,hc⟩ := hdC
  let v := (coordinates A B C hA).symm ⟨z,hz⟩
  have hv : (coordinates A B C hA v).val = z :=
    congrArg Subtype.val ((coordinates A B C hA).apply_symm_apply ⟨z,hz⟩)
  refine ⟨(coordinates A B C hA ![-c*v 1,a*v 0+b*v 1]).val,
    (coordinates A B C hA _).prop,?_⟩
  rw [← hv,coordinates_apply,coordinates_apply]
  apply QuadraticAlgebra.ext <;> simp [ha,hb,hc] <;> ring

/-- Every integer common divisor of A,B,C divides one if the actual mapped
norm ideal is invertible. The map is an integral order equivalence. -/
theorem common_divisor_dvd_one_of_isUnit_map_normIdeal
    {R : Type*} [CommRing R] [IsDomain R]
    (A B C d : ℤ) (hA : A ≠ 0) (hdA : d ∣ A) (hdB : d ∣ B) (hdC : d ∣ C)
    (E : CoefficientOrder A B C ≃ₐ[ℤ] R)
    (hI : IsUnit ((Ideal.map E.toRingHom (normIdeal A B C)) :
      FractionalIdeal R⁰ (FractionRing R))) : d ∣ (1 : ℤ) := by
  let F := FractionRing R
  let J := Ideal.map E.toRingHom (normIdeal A B C)
  let f : F := algebraMap R F (E QuadraticAlgebra.omega)/(d : F)
  have hd : d ≠ 0 := by
    intro hd
    rw [hd] at hdA
    exact hA (zero_dvd_iff.mp hdA)
  have hdR : (d : R) ≠ 0 := by
    intro hz
    have hh : (d : CoefficientOrder A B C) = 0 := E.injective (by simpa using hz)
    have hr := congrArg QuadraticAlgebra.re hh
    exact hd (by simpa using hr)
  have hdF : (d : F) ≠ 0 := by
    have hh := (IsFractionRing.injective R F).ne hdR
    simpa only [map_intCast,map_zero] using hh
  have hpres : ∀ y ∈ (J : FractionalIdeal R⁰ F), f*y ∈ (J : FractionalIdeal R⁰ F) := by
    intro y hy
    obtain ⟨r,hr,rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    obtain ⟨z,hz,hez⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hr
    obtain ⟨w,hw,hdw⟩ := divided_theta_action A B C d hA hdA hdB hdC z hz
    apply (FractionalIdeal.mem_coeIdeal R⁰).mpr
    refine ⟨E w,Ideal.mem_map_of_mem E.toRingHom hw,?_⟩
    have hh := congrArg (fun z : CoefficientOrder A B C => algebraMap R F (E z)) hdw
    simp only [map_mul,map_intCast] at hh
    change E z = r at hez
    rw [hez] at hh
    calc
      algebraMap R F (E w) = (algebraMap R F (E QuadraticAlgebra.omega)*algebraMap R F r)/(d : F) := by
        apply (eq_div_iff hdF).mpr
        simpa only [mul_comm] using hh
      _ = f*algebraMap R F r := by dsimp [f]; ring
  obtain ⟨r,hr⟩ := (FractionalIdeal.multiplier_iff_of_isUnit
    (J : FractionalIdeal R⁰ F) hI f).mp hpres
  have hmul : (d : R)*r = E QuadraticAlgebra.omega := by
    apply IsFractionRing.injective R F
    rw [map_mul,map_intCast,hr]
    change (d : F) * (algebraMap R F (E QuadraticAlgebra.omega)/(d : F)) = _
    exact mul_div_cancel₀ _ hdF
  have hh := congrArg E.symm hmul
  simp only [map_mul,map_intCast,AlgEquiv.symm_apply_apply] at hh
  have hi := congrArg QuadraticAlgebra.im hh
  simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast,Int.cast_id,zero_mul,mul_zero,add_zero,
    QuadraticAlgebra.omega_im] at hi
  exact ⟨(E.symm r).im,hi.symm⟩

/-- The coefficient gcd is one for an invertible actual mapped norm ideal. -/
theorem coefficients_gcd_eq_one_of_isUnit_map_normIdeal
    {R : Type*} [CommRing R] [IsDomain R]
    (A B C : ℤ) (hA : A ≠ 0) (E : CoefficientOrder A B C ≃ₐ[ℤ] R)
    (hI : IsUnit ((Ideal.map E.toRingHom (normIdeal A B C)) :
      FractionalIdeal R⁰ (FractionRing R))) : Int.gcd A (Int.gcd B C : ℤ) = 1 := by
  have hdA := Int.gcd_dvd_left A (Int.gcd B C : ℤ)
  have hdB := dvd_trans (Int.gcd_dvd_right A (Int.gcd B C : ℤ)) (Int.gcd_dvd_left B C)
  have hdC := dvd_trans (Int.gcd_dvd_right A (Int.gcd B C : ℤ)) (Int.gcd_dvd_right B C)
  have hh := common_divisor_dvd_one_of_isUnit_map_normIdeal A B C
    (Int.gcd A (Int.gcd B C : ℤ)) hA hdA hdB hdC E hI
  exact Nat.dvd_one.mp (by exact_mod_cast hh)

/-- The normalized translation is exactly the canonical equal-discriminant
translation. This fixes the orientation used by the actual class map. -/
theorem normalizedCoefficientOrderEquiv_eq_discriminant (a b c A t : ℤ)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) :
    normalizedCoefficientOrderEquiv a b c A t hdiv =
      coefficientOrderEquivOfDiscriminant A (b+2*t)
        ((⟨t,1⟩ : CoefficientOrder a b c).norm/A) a b c
        (normalized_discriminant a b c A t hdiv) := by
  apply AlgEquiv.ext
  intro z
  apply QuadraticAlgebra.ext
  · change z.re+t*z.im = z.re+((b+2*t-b)/2)*z.im
    have hk : (b+2*t-b)/2=t := by omega
    rw [hk]
  · rfl

/-- Every canonical class is represented by a primitive normalized polynomial
norm ideal in the same original order, with an actual unit and the same class. -/
theorem exists_primitive_normalized_class_representative (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (xi : letI := coefficientOrder_isDomain a b c hD; ClassGroup (CoefficientOrder a b c)) :
    letI := coefficientOrder_isDomain a b c hD
    ∃ (A t : ℤ) (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm), 0 < A ∧
      Int.gcd A (Int.gcd (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A) : ℤ) = 1 ∧
      ∃ u : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ,
        (u : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) =
          (Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
            (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A)) :
              FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) ∧
        ClassGroup.mk (FractionRing (CoefficientOrder a b c)) u = xi := by
  letI := coefficientOrder_isDomain a b c hD
  obtain ⟨A,t,hdiv,hA,u,hu,hclass⟩ := exists_normalized_class_representative a b c hD xi
  have hunit : IsUnit ((Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
      (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A))) :
        FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) := hu ▸ u.isUnit
  have hgcd := coefficients_gcd_eq_one_of_isUnit_map_normIdeal _ _ _ (ne_of_gt hA)
    (normalizedCoefficientOrderEquiv a b c A t hdiv) hunit
  exact ⟨A,t,hdiv,hA,hgcd,u,hu,hclass⟩

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

private lemma normIdealAt_of_coefficients (L : PositiveDefiniteIntegralLattice 2) (D A B C : ℤ)
    (hA : L.pairingMatrix 0 0 / (L.binaryContent : ℤ) = A)
    (hB : 2*L.pairingMatrix 0 1 / (L.binaryContent : ℤ) = B)
    (hC : L.pairingMatrix 1 1 / (L.binaryContent : ℤ) = C)
    (hLD : L.binaryPrimitiveDiscriminant = D) (hD : B^2-4*A*C = D) :
    binaryDiscriminantNormIdealAt L D hLD =
      Ideal.map (BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder A B C D
        (hLD ▸ L.binaryPrimitiveDiscriminant_mod_four) hD).toRingHom
        (BinaryNormIdeal.normIdeal A B C) := by
  subst A
  subst B
  subst C
  exact binaryDiscriminantNormIdealAt_eq_map L D hLD

/-- Every canonical order class is realized by an actual integral lattice at
K's original content and primitive discriminant. This does not assert that
the lattice belongs to K's original local-isometry genus. -/
theorem exists_lattice_of_binaryIdealClass (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent = K.binaryContent ∧
      ∃ hD : L.binaryPrimitiveDiscriminant = K.binaryPrimitiveDiscriminant,
        binaryIdealClassAt L K.binaryPrimitiveDiscriminant hD = xi := by
  letI := K.binaryDiscriminantOrder_isDomain
  let D := K.binaryPrimitiveDiscriminant
  let r := D%2
  let c := (r^2-D)/4
  have hroot : r^2-4*1*c=D := BinaryNormIdeal.discriminantOrder_coefficients D
    K.binaryPrimitiveDiscriminant_mod_four
  have hneg : r^2-4*1*c < 0 := hroot ▸ K.binaryPrimitiveDiscriminant_neg
  obtain ⟨A,t,hdiv,hA,hprim,u,hu,hclass⟩ :=
    BinaryNormIdeal.exists_primitive_normalized_class_representative 1 r c hneg xi
  let B := r+2*t
  let C := (⟨t,1⟩ : BinaryNormIdeal.CoefficientOrder 1 r c).norm/A
  have hDQ : B^2-4*A*C=D :=
    (BinaryNormIdeal.normalized_discriminant 1 r c A t hdiv).trans hroot
  have hQneg : B^2-4*A*C < 0 := hDQ ▸ K.binaryPrimitiveDiscriminant_neg
  have heven : (2 : ℤ) ∣ (K.binaryContent : ℤ)*B :=
    K.binary_scaled_mixed_even_of_discriminant A B C hDQ
  let L := binaryLatticeOfCoefficients K.binaryContent K.binaryContent_pos A B C hA hQneg heven
  have hcoeff := binaryLatticeOfCoefficients_coefficients K.binaryContent K.binaryContent_pos
    A B C hA hQneg heven hprim
  have hLD : L.binaryPrimitiveDiscriminant=D :=
    (binaryLatticeOfCoefficients_discriminant K.binaryContent K.binaryContent_pos
      A B C hA hQneg heven hprim).trans hDQ
  refine ⟨L,binaryLatticeOfCoefficients_content K.binaryContent K.binaryContent_pos
    A B C hA hQneg heven hprim,hLD,?_⟩
  have himage := normIdealAt_of_coefficients L D A B C hcoeff.1 hcoeff.2.1 hcoeff.2.2 hLD hDQ
  have hmap : binaryDiscriminantNormIdealAt L D hLD =
      Ideal.map (BinaryNormIdeal.normalizedCoefficientOrderEquiv 1 r c A t hdiv).toRingHom
        (BinaryNormIdeal.normIdeal A B C) := by
    rw [himage,BinaryNormIdeal.normalizedCoefficientOrderEquiv_eq_discriminant]
    rfl
  have hv := binaryFractionalNormIdealUnitAt_val L D hLD
  rw [hmap] at hv
  have heq := (ClassGroup.mk_eq_mk_of_coe_ideal hv hu).mpr
    ⟨1,1,one_ne_zero,one_ne_zero,by
      simp only [Ideal.span_singleton_one,Ideal.top_mul]
      rfl⟩
  exact heq.trans hclass

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.common_divisor_dvd_one_of_isUnit_map_normIdeal
#assert_standard_axioms BinaryNormIdeal.coefficients_gcd_eq_one_of_isUnit_map_normIdeal

#assert_standard_axioms BinaryNormIdeal.normalizedCoefficientOrderEquiv_eq_discriminant
#assert_standard_axioms BinaryNormIdeal.exists_primitive_normalized_class_representative

#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_lattice_of_binaryIdealClass
