import SMSFormula.BinaryClassGroupMap

/-!
# Integral ideal coordinates in a quadratic order

Positive generators of the real intersection and imaginary image give an
actual two-element integer basis. Ideal closure forces a common integer
scalar. No maximal-order or invertibility hypothesis is used for this step.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

private lemma positive_integer_generator (J : Ideal ℤ) (hJ : J ≠ ⊥) :
    ∃ a : ℤ, 0 < a ∧ ∀ n : ℤ, n ∈ J ↔ a ∣ n := by
  let g := Submodule.IsPrincipal.generator J
  have hg : g ≠ 0 := by
    intro hz
    exact hJ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J).mpr hz)
  refine ⟨|g|, abs_pos.mpr hg, ?_⟩
  intro n
  rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
  exact (abs_dvd g n).symm

/-- The actual image of an integral order ideal under the imaginary coordinate.
It is an integer ideal, not an ideal in the quadratic order. -/
def imaginaryIdeal (a b c : ℤ) (I : Ideal (CoefficientOrder a b c)) : Ideal ℤ where
  carrier := {n | ∃ z ∈ I, z.im = n}
  zero_mem' := ⟨0,I.zero_mem,rfl⟩
  add_mem' := by
    rintro x y ⟨z,hz,hx⟩ ⟨w,hw,hy⟩
    exact ⟨z+w,I.add_mem hz hw, by simp [hx,hy]⟩
  smul_mem' := by
    rintro r n ⟨z,hz,hn⟩
    exact ⟨(r : CoefficientOrder a b c)*z,I.mul_mem_left _ hz,by simp [hn]⟩

/-- A nonzero ideal contains a positive rational integer: take the norm of
any of its nonzero elements in the negative-discriminant order. -/
theorem exists_pos_integer_mem (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (I : Ideal (CoefficientOrder a b c)) (hI : I ≠ ⊥) :
    ∃ n : ℤ, 0 < n ∧ (n : CoefficientOrder a b c) ∈ I := by
  obtain ⟨z,hz,hzne⟩ := I.ne_bot_iff.mp hI
  refine ⟨z.norm,norm_pos_of_discriminant_neg a b c hD z hzne,?_⟩
  rw [show (z.norm : CoefficientOrder a b c) = z*star z from
    QuadraticAlgebra.algebraMap_norm_eq_mul_star z]
  exact I.mul_mem_right _ hz

/-- An actual integer basis of any nonzero ideal: (A,T+c*omega), A,c>0.
The coefficients need not be coprime and no invertibility is assumed. -/
theorem exists_integer_ideal_basis (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (I : Ideal (CoefficientOrder a b c)) (hI : I ≠ ⊥) :
    ∃ A T C : ℤ, 0 < A ∧ 0 < C ∧
      (A : CoefficientOrder a b c) ∈ I ∧ (⟨T,C⟩ : CoefficientOrder a b c) ∈ I ∧
      ∀ z : CoefficientOrder a b c,
        z ∈ I ↔ ∃ x y : ℤ, z = ⟨A*x+T*y,C*y⟩ := by
  obtain ⟨n,hn,hnI⟩ := exists_pos_integer_mem a b c hD I hI
  let J := I.comap (Int.castRingHom (CoefficientOrder a b c))
  have hJ : J ≠ ⊥ := by
    intro hz
    have hh : n ∈ J := hnI
    rw [hz] at hh
    exact (ne_of_gt hn) hh
  obtain ⟨A,hA,hAr⟩ := positive_integer_generator J hJ
  have hAI : (A : CoefficientOrder a b c) ∈ I := (hAr A).mpr (dvd_refl A)
  have hImag : imaginaryIdeal a b c I ≠ ⊥ := by
    intro hz
    have hh : n ∈ imaginaryIdeal a b c I :=
      ⟨(n : CoefficientOrder a b c)*QuadraticAlgebra.omega,I.mul_mem_right _ hnI,by simp⟩
    rw [hz] at hh
    exact (ne_of_gt hn) hh
  obtain ⟨C,hC,hCr⟩ := positive_integer_generator (imaginaryIdeal a b c I) hImag
  obtain ⟨w,hw,hwC⟩ := (hCr C).mpr (dvd_refl C)
  have hTI : (⟨w.re,C⟩ : CoefficientOrder a b c) ∈ I := by
    convert hw using 1
    apply QuadraticAlgebra.ext <;> simp [hwC]
  refine ⟨A,w.re,C,hA,hC,hAI,hTI,?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨y,hy⟩ := (hCr z.im).mp ⟨z,hz,rfl⟩
    have hsub : z - (y : CoefficientOrder a b c)*⟨w.re,C⟩ ∈ I :=
      I.sub_mem hz (I.mul_mem_left _ hTI)
    have hre : ((z.re-w.re*y : ℤ) : CoefficientOrder a b c) ∈ I := by
      convert hsub using 1
      apply QuadraticAlgebra.ext <;> simp [hy] <;> ring
    obtain ⟨x,hx⟩ := (hAr (z.re-w.re*y)).mp hre
    refine ⟨x,y,?_⟩
    apply QuadraticAlgebra.ext
    · change z.re = A*x+w.re*y
      omega
    · exact hy
  · rintro ⟨x,y,rfl⟩
    have hh := I.add_mem (I.mul_mem_left (x : CoefficientOrder a b c) hAI)
      (I.mul_mem_left (y : CoefficientOrder a b c) hTI)
    convert hh using 1
    apply QuadraticAlgebra.ext <;> simp <;> ring

/-- Every nonzero integral ideal is a positive integer scalar times
(a,t+omega), with a positive and a dividing N(t+omega). -/
theorem exists_normalized_ideal (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (I : Ideal (CoefficientOrder a b c)) (hI : I ≠ ⊥) :
    ∃ C A t : ℤ, 0 < C ∧ 0 < A ∧
      I = Ideal.span {(C : CoefficientOrder a b c)} *
        Ideal.span {(A : CoefficientOrder a b c), (⟨t,1⟩ : CoefficientOrder a b c)} ∧
      A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm := by
  obtain ⟨A,T,C,hA,hC,hAI,hTI,hrep⟩ := exists_integer_ideal_basis a b c hD I hI
  have hCA : C ∣ A := by
    obtain ⟨x,y,hh⟩ := (hrep ((A : CoefficientOrder a b c)*QuadraticAlgebra.omega)).mp
      (I.mul_mem_right _ hAI)
    refine ⟨y,?_⟩
    simpa using congrArg QuadraticAlgebra.im hh
  have hCT : C ∣ T := by
    obtain ⟨x,y,hh⟩ := (hrep (QuadraticAlgebra.omega*(⟨T,C⟩ : CoefficientOrder a b c))).mp
      (I.mul_mem_left _ hTI)
    have hi := congrArg QuadraticAlgebra.im hh
    simp at hi
    refine ⟨y-b,?_⟩
    nlinarith only [hi]
  obtain ⟨A',hAA⟩ := hCA
  obtain ⟨t,hTt⟩ := hCT
  have hA' : 0 < A' := by nlinarith [hAA]
  have hnrep (z : CoefficientOrder a b c) : z ∈ I ↔
      ∃ x y : ℤ, z = (C : CoefficientOrder a b c)*⟨A'*x+t*y,y⟩ := by
    rw [hrep z]
    constructor
    · rintro ⟨x,y,rfl⟩
      refine ⟨x,y,?_⟩
      apply QuadraticAlgebra.ext <;> simp [hAA,hTt]
      ring
    · rintro ⟨x,y,rfl⟩
      refine ⟨x,y,?_⟩
      apply QuadraticAlgebra.ext <;> simp [hAA,hTt]
      ring
  have hgA : (C : CoefficientOrder a b c)*(A' : CoefficientOrder a b c) ∈ I := by
    apply (hnrep _).mpr
    refine ⟨1,0,?_⟩
    apply QuadraticAlgebra.ext <;> simp
  have hgt : (C : CoefficientOrder a b c)*(⟨t,1⟩ : CoefficientOrder a b c) ∈ I := by
    apply (hnrep _).mpr
    refine ⟨0,1,?_⟩
    apply QuadraticAlgebra.ext <;> simp
  refine ⟨C,A',t,hC,hA',?_,?_⟩
  · apply le_antisymm
    · intro z hz
      obtain ⟨x,y,rfl⟩ := (hnrep z).mp hz
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨⟨A'*x+t*y,y⟩,?_,rfl⟩
      have hv : (⟨A'*x+t*y,y⟩ : CoefficientOrder a b c) =
          (x : CoefficientOrder a b c)*(A' : CoefficientOrder a b c) +
            (y : CoefficientOrder a b c)*⟨t,1⟩ := by
        apply QuadraticAlgebra.ext <;> simp
        ring
      rw [hv]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [Ideal.span_mul_span]
      apply Ideal.span_le.mpr
      intro z hz
      obtain ⟨u,hu,v,hv,rfl⟩ := Set.mem_mul.mp hz
      obtain rfl := Set.mem_singleton_iff.mp hu
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact hgA
      · obtain rfl := Set.mem_singleton_iff.mp hv
        exact hgt
  · obtain ⟨x,y,hh⟩ := (hnrep (QuadraticAlgebra.omega *
        ((C : CoefficientOrder a b c)*(⟨t,1⟩ : CoefficientOrder a b c)))).mp
      (I.mul_mem_left _ hgt)
    have hr : C*(-a*c) = C*(A'*x+t*y) := by
      have h := congrArg QuadraticAlgebra.re hh
      simp at h
      nlinarith only [h]
    have hi : C*(t+b) = C*y := by
      have h := congrArg QuadraticAlgebra.im hh
      simp at h
      nlinarith only [h]
    have hr' := mul_left_cancel₀ (ne_of_gt hC) hr
    have hi' := mul_left_cancel₀ (ne_of_gt hC) hi
    rw [← hi'] at hr'
    refine ⟨-x,?_⟩
    rw [QuadraticAlgebra.norm_def]
    simp only
    nlinarith only [hr']

/-- Exact coefficient relation after dividing the shifted generator norm. -/
lemma normalized_norm_relation (a b c A t : ℤ)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) :
    A*((⟨t,1⟩ : CoefficientOrder a b c).norm/A) = a*c+b*t+t^2 := by
  calc
    _ = (⟨t,1⟩ : CoefficientOrder a b c).norm := Int.mul_ediv_cancel' hdiv
    _ = _ := by rw [QuadraticAlgebra.norm_def]; simp; ring

/-- The normalized ideal's coefficient order maps integrally to the original
order by theta -> t+omega, with no inverse of 2 or maximality premise. -/
def normalizedCoefficientOrderEquiv (a b c A t : ℤ)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) :
    CoefficientOrder A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A) ≃ₐ[ℤ]
      CoefficientOrder a b c :=
  coefficientOrderEquivOfShift _ _ _ a b c t rfl (normalized_norm_relation a b c A t hdiv)

/-- Normalization preserves the exact order discriminant, including odd trace. -/
theorem normalized_discriminant (a b c A t : ℤ)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) :
    (b+2*t)^2 - 4*A*((⟨t,1⟩ : CoefficientOrder a b c).norm/A) = b^2-4*a*c := by
  have h := normalized_norm_relation a b c A t hdiv
  nlinarith only [h]

/-- The normalized two-generator ideal is exactly the image of the coefficient
norm ideal, not merely a lattice with the same rank or discriminant. -/
theorem normalizedIdeal_eq_map_normIdeal (a b c A t : ℤ)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) :
    Ideal.span {(A : CoefficientOrder a b c),(⟨t,1⟩ : CoefficientOrder a b c)} =
      Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
        (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A)) := by
  rw [normIdeal_eq_span, Ideal.map_span, Set.image_pair]
  congr 1
  simp [normalizedCoefficientOrderEquiv, coefficientOrderEquivOfShift]

/-- The exact normalized coordinates keep norm A*Q on the same integer pair. -/
theorem norm_normalized_coordinates (a b c A t : ℤ) (hA : A ≠ 0)
    (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm) (v : Fin 2 → ℤ) :
    (normalizedCoefficientOrderEquiv a b c A t hdiv
      (coordinates A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A) hA v).val).norm =
        A*(A*v 0^2+(b+2*t)*v 0*v 1+((⟨t,1⟩ : CoefficientOrder a b c).norm/A)*v 1^2) := by
  unfold normalizedCoefficientOrderEquiv
  rw [norm_coefficientOrderEquivOfShift, norm_coordinates]

/-- Every nonzero integral ideal has an exact coefficient norm-ideal
presentation. The resulting polynomial is not yet asserted primitive. -/
theorem exists_coefficient_normIdeal_presentation (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (I : Ideal (CoefficientOrder a b c)) (hI : I ≠ ⊥) :
    ∃ C A t : ℤ, 0 < C ∧ 0 < A ∧
      ∃ hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm,
        I = Ideal.span {(C : CoefficientOrder a b c)} *
          Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
            (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A)) ∧
        (b+2*t)^2 - 4*A*((⟨t,1⟩ : CoefficientOrder a b c).norm/A) = b^2-4*a*c := by
  obtain ⟨C,A,t,hC,hA,hIeq,hdiv⟩ := exists_normalized_ideal a b c hD I hI
  refine ⟨C,A,t,hC,hA,hdiv,?_,normalized_discriminant a b c A t hdiv⟩
  rw [← normalizedIdeal_eq_map_normIdeal]
  exact hIeq

/-- Every canonical class has an invertible representative that is a
coefficient norm ideal in the original order. Primitivity of its polynomial
coefficients is a separate condition. -/
theorem exists_normalized_class_representative (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (xi : letI := coefficientOrder_isDomain a b c hD; ClassGroup (CoefficientOrder a b c)) :
    letI := coefficientOrder_isDomain a b c hD
    ∃ (A t : ℤ) (hdiv : A ∣ (⟨t,1⟩ : CoefficientOrder a b c).norm), 0 < A ∧
      ∃ u : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ,
        (u : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) =
          (Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
            (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A)) :
              FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) ∧
        ClassGroup.mk (FractionRing (CoefficientOrder a b c)) u = xi := by
  letI := coefficientOrder_isDomain a b c hD
  obtain ⟨I,u,hu,hclass⟩ := ClassGroup.exists_integral_unit_representative xi
  have hI : I ≠ ⊥ := by
    intro hz
    have hh := hu
    rw [hz] at hh
    simp at hh
  obtain ⟨C,A,t,hC,hA,hdiv,hIeq,_⟩ := exists_coefficient_normIdeal_presentation a b c hD I hI
  let J := Ideal.map (normalizedCoefficientOrderEquiv a b c A t hdiv).toRingHom
    (normIdeal A (b+2*t) ((⟨t,1⟩ : CoefficientOrder a b c).norm/A))
  have hunit : IsUnit (J : FractionalIdeal (CoefficientOrder a b c)⁰
      (FractionRing (CoefficientOrder a b c))) := by
    have hh : IsUnit (I : FractionalIdeal (CoefficientOrder a b c)⁰
        (FractionRing (CoefficientOrder a b c))) := hu ▸ u.isUnit
    rw [hIeq, FractionalIdeal.coeIdeal_mul] at hh
    exact (IsUnit.mul_iff.mp hh).2
  have hCne : (C : CoefficientOrder a b c) ≠ 0 := by
    intro hz
    have hr := congrArg QuadraticAlgebra.re hz
    exact (ne_of_gt hC) (by simpa using hr)
  refine ⟨A,t,hdiv,hA,hunit.unit,hunit.unit_spec,?_⟩
  have heq := (ClassGroup.mk_eq_mk_of_coe_ideal hu hunit.unit_spec).mpr
    (show ∃ x y : CoefficientOrder a b c, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * I = Ideal.span {y} * J from
      ⟨1,(C : CoefficientOrder a b c),one_ne_zero,hCne,by simpa using hIeq⟩)
  exact heq.symm.trans hclass

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.imaginaryIdeal
#assert_standard_axioms BinaryNormIdeal.exists_pos_integer_mem
#assert_standard_axioms BinaryNormIdeal.exists_integer_ideal_basis

#assert_standard_axioms BinaryNormIdeal.exists_normalized_ideal

#assert_standard_axioms BinaryNormIdeal.normalized_norm_relation
#assert_standard_axioms BinaryNormIdeal.normalizedCoefficientOrderEquiv
#assert_standard_axioms BinaryNormIdeal.normalized_discriminant
#assert_standard_axioms BinaryNormIdeal.normalizedIdeal_eq_map_normIdeal
#assert_standard_axioms BinaryNormIdeal.norm_normalized_coordinates
#assert_standard_axioms BinaryNormIdeal.exists_coefficient_normIdeal_presentation

#assert_standard_axioms BinaryNormIdeal.exists_normalized_class_representative
