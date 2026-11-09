import SMSFormula.BinaryPicardKernel

/-!
# Actual conductor patching for Picard surjectivity

Maximal-order ideals are restricted to the original order by its proved
positive index. The maximal order itself is not declared invertible over A.
-/

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]

/-- The conductor patch on actual original-order fractional-ideal carriers. -/
noncomputable def overorderPatch (C J : FractionalIdeal R⁰ F) (x : F) : FractionalIdeal R⁰ F :=
  spanSingleton R⁰ x+C*J

/-- Reciprocal overorder residue generators supply literal inverse patches.
No invertibility of the overorder as an R-ideal is assumed. -/
theorem overorderPatch_mul_inverse (T C J K : FractionalIdeal R⁰ F)
    (hC : C ≤ 1) (hTC : T*C=C) (hJK : J*K=T)
    (x y : F) (hx : x ∈ J) (hy : y ∈ K) (hxy : x*y-1 ∈ C) :
    overorderPatch C J x * overorderPatch C K y=1 := by
  let L := overorderPatch C J x
  let M := overorderPatch C K y
  have hU : spanSingleton R⁰ x ≤ J := spanSingleton_le_iff_mem.mpr hx
  have hV : spanSingleton R⁰ y ≤ K := spanSingleton_le_iff_mem.mpr hy
  have hUK : spanSingleton R⁰ x*K ≤ T := by
    calc
      spanSingleton R⁰ x*K ≤ J*K := mul_le_mul_left hU K
      _ = T := hJK
  have hJV : J*spanSingleton R⁰ y ≤ T := by
    calc
      J*spanSingleton R⁰ y ≤ J*K := mul_le_mul_right hV J
      _ = T := hJK
  have hCT : C*T=C := (mul_comm C T).trans hTC
  have hUV : spanSingleton R⁰ x*spanSingleton R⁰ y ≤ 1 := by
    rw [spanSingleton_mul_spanSingleton]
    apply spanSingleton_le_iff_mem.mpr
    have hh := ((1 : FractionalIdeal R⁰ F) : Submodule R F).add_mem (hC hxy) (one_mem_one (S := R⁰) (P := F))
    simpa using hh
  have h1 : spanSingleton R⁰ x*(C*K) ≤ 1 := by
    calc
      spanSingleton R⁰ x*(C*K)=C*(spanSingleton R⁰ x*K) := by ac_rfl
      _ ≤ C*T := mul_le_mul_right hUK C
      _ = C := hCT
      _ ≤ 1 := hC
  have h2 : (C*J)*spanSingleton R⁰ y ≤ 1 := by
    calc
      (C*J)*spanSingleton R⁰ y=C*(J*spanSingleton R⁰ y) := mul_assoc _ _ _
      _ ≤ C*T := mul_le_mul_right hJV C
      _ = C := hCT
      _ ≤ 1 := hC
  have h3eq : (C*J)*(C*K)=C*C := by
    calc
      (C*J)*(C*K)=(C*C)*(J*K) := by ac_rfl
      _ = (C*C)*T := by rw [hJK]
      _ = C*C := by rw [mul_assoc,hCT]
  have h3 : (C*J)*(C*K) ≤ 1 := by
    rw [h3eq]
    calc
      C*C ≤ C*1 := mul_le_mul_right hC C
      _ = C := mul_one C
      _ ≤ 1 := hC
  have hle : L*M ≤ 1 := by
    change (spanSingleton R⁰ x+C*J)*(spanSingleton R⁰ y+C*K) ≤ 1
    rw [add_mul,mul_add,mul_add]
    exact sup_le (sup_le hUV h1) (sup_le h2 h3)
  have hxL : x ∈ L := (show spanSingleton R⁰ x ≤ L from le_sup_left) (mem_spanSingleton_self R⁰ x)
  have hyM : y ∈ M := (show spanSingleton R⁰ y ≤ M from le_sup_left) (mem_spanSingleton_self R⁰ y)
  have hCC : C*C ≤ L*M := by
    rw [← h3eq]
    calc
      (C*J)*(C*K) ≤ L*(C*K) := mul_le_mul_left (show C*J ≤ L from le_sup_right) (C*K)
      _ ≤ L*M := mul_le_mul_right (show C*K ≤ M from le_sup_right) L
  have hCM : C*K ≤ M := le_sup_right
  have hCLM : C ≤ L*M := by
    intro z hz
    have hzxy : x*(z*y) ∈ L*M := mul_mem_mul hxL (hCM (mul_mem_mul hz hy))
    have hres : z*(x*y-1) ∈ L*M := hCC (mul_mem_mul hz hxy)
    have hh := ((L*M : FractionalIdeal R⁰ F) : Submodule R F).sub_mem hzxy hres
    convert hh using 1
    ring
  have hone : 1 ≤ L*M := by
    apply one_le.mpr
    have hh := ((L*M : FractionalIdeal R⁰ F) : Submodule R F).sub_mem (mul_mem_mul hxL hyM) (hCLM hxy)
    convert hh using 1
    ring
  exact le_antisymm hle hone

/-- The actual patch extends to its chosen overorder ideal. -/
theorem overorderPatch_mul_overorder (T C J K : FractionalIdeal R⁰ F)
    (hC : C ≤ 1) (hJT : J*T=J) (hKJ : K*J=T)
    (x y : F) (hx : x ∈ J) (hy : y ∈ K) (hxy : x*y-1 ∈ C) :
    overorderPatch C J x*T=J := by
  have hCJ : C*J ≤ J := by
    simpa using mul_le_mul_left hC J
  have hLJ : overorderPatch C J x ≤ J := sup_le (spanSingleton_le_iff_mem.mpr hx) hCJ
  apply le_antisymm
  · calc
      overorderPatch C J x*T ≤ J*T := mul_le_mul_left hLJ T
      _ = J := hJT
  · intro z hz
    have hvz : y*z ∈ T := by rw [← hKJ]; exact mul_mem_mul hy hz
    have hterm : x*(y*z) ∈ overorderPatch C J x*T :=
      mul_mem_mul (show x ∈ overorderPatch C J x from
        (show spanSingleton R⁰ x ≤ overorderPatch C J x from le_sup_left) (mem_spanSingleton_self R⁰ x)) hvz
    have hdiff : (1-x*y)*z ∈ overorderPatch C J x*T := by
      have hneg : 1-x*y ∈ C := by simpa using (C : Submodule R F).neg_mem hxy
      have hm : (1-x*y)*z ∈ C*J := mul_mem_mul hneg hz
      have hsub : C*J ≤ overorderPatch C J x*T := by
        have heq : (C*J)*T=C*J := by rw [mul_assoc,hJT]
        rw [← heq]
        exact mul_le_mul_left (show C*J ≤ overorderPatch C J x from le_sup_right) T
      exact hsub hm
    have hh := ((overorderPatch C J x*T : FractionalIdeal R⁰ F) : Submodule R F).add_mem hterm hdiff
    convert hh using 1
    ring

end FractionalIdeal

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- Restriction of an actual maximal-order fractional ideal to the original
order. The positive actual index clears its maximal-order denominator. -/
noncomputable def restrictMaximalIdeal (hD : b^2-4*a*c<0)
    (J : FractionalIdeal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
      (FractionRing (CoefficientOrder a b c))) :
    FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)) where
  val := {
    carrier := J
    zero_mem' := J.zero_mem
    add_mem' := (J : Submodule (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) (FractionRing (CoefficientOrder a b c))).add_mem
    smul_mem' := fun r x hx => by
      simpa only [Algebra.smul_def,orderToRingOfIntegers_coe] using
        (J : Submodule (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) (FractionRing (CoefficientOrder a b c))).smul_mem (orderToRingOfIntegers a b c r) hx }
  property := by
    letI := fractionNumberField a b c hD
    obtain ⟨d,hd,hbound⟩ := J.isFractional
    obtain ⟨r,hr⟩ := index_mul_mem_orderImage a b c hD d
    have hrF : algebraMap (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) r =
        (orderIndex a b c : FractionRing (CoefficientOrder a b c))*algebraMap _ _ d := by
      have hh := congrArg (algebraMap (NumberField.RingOfIntegers
        (FractionRing (CoefficientOrder a b c))) (FractionRing (CoefficientOrder a b c))) hr
      simpa only [map_mul,map_natCast,orderToRingOfIntegers_coe] using hh
    refine ⟨r,?_,?_⟩
    · apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro hz
      have hI : (orderIndex a b c : FractionRing (CoefficientOrder a b c)) ≠ 0 := by
        exact_mod_cast (ne_of_gt (orderIndex_pos a b c hD))
      have hd0 : algebraMap (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
          (FractionRing (CoefficientOrder a b c)) d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      exact (mul_ne_zero hI hd0) (by simpa only [hz,map_zero] using hrF.symm)
    · intro x hx
      obtain ⟨z,hz⟩ := hbound x hx
      obtain ⟨s,hs⟩ := index_mul_mem_orderImage a b c hD z
      refine ⟨s,?_⟩
      have hh := congrArg (algebraMap (NumberField.RingOfIntegers
        (FractionRing (CoefficientOrder a b c))) (FractionRing (CoefficientOrder a b c))) hs
      simp only [map_mul,map_natCast] at hh
      rw [Algebra.smul_def,hrF]
      rw [hz,Algebra.smul_def] at hh
      simpa only [mul_assoc] using hh

/-- Restriction keeps the literal same field elements. -/
theorem mem_restrictMaximalIdeal (hD : b^2-4*a*c<0)
    (J : FractionalIdeal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
      (FractionRing (CoefficientOrder a b c))) (x : FractionRing (CoefficientOrder a b c)) :
    x ∈ restrictMaximalIdeal a b c hD J ↔ x ∈ J := Iff.rfl

/-- Restriction preserves multiplication, but its identity is the overorder
T, rather than the original-order unit ideal. -/
theorem restrictMaximalIdeal_mul (hD : b^2-4*a*c<0)
    (J K : FractionalIdeal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
      (FractionRing (CoefficientOrder a b c))) :
    restrictMaximalIdeal a b c hD (J*K)=
      restrictMaximalIdeal a b c hD J*restrictMaximalIdeal a b c hD K := by
  apply le_antisymm
  · intro x hx
    change x ∈ (J*K : FractionalIdeal _ _) at hx
    change x ∈ ((J*K : FractionalIdeal
      (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
      (FractionRing (CoefficientOrder a b c))) : Submodule
      (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
      (FractionRing (CoefficientOrder a b c))) at hx
    rw [FractionalIdeal.coe_mul] at hx
    refine Submodule.mul_induction_on hx (fun u hu v hv => ?_) (fun u v hu hv => ?_)
    · exact FractionalIdeal.mul_mem_mul hu hv
    · exact ((restrictMaximalIdeal a b c hD J*restrictMaximalIdeal a b c hD K :
        FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) :
        Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))).add_mem hu hv
  · apply FractionalIdeal.mul_le.mpr
    intro x hx y hy
    exact FractionalIdeal.mul_mem_mul hx hy

theorem restrictMaximalIdeal_one (hD : b^2-4*a*c<0) :
    restrictMaximalIdeal a b c hD 1=maximalOrderFractionalIdeal a b c hD := by
  ext x
  exact (FractionalIdeal.mem_one_iff
    (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰).trans
      (mem_maximalOrderFractionalIdeal a b c hD x).symm


/-- The actual conductor in B has finite maximal support, with no numerical
conductor or residue-unit count assumption. -/
theorem finite_maximalSpectrum_above_orderConductor (hD : b^2-4*a*c<0) :
    Finite {m : MaximalSpectrum (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      orderConductor a b c ≤ m.asIdeal} := by
  classical
  letI := fractionNumberField a b c hD
  let d : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) := orderIndex a b c
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (ne_of_gt (orderIndex_pos a b c hD))
  have hdC : d ∈ orderConductor a b c := by
    rw [orderConductor_eq_span_index a b c hD]
    exact Ideal.subset_span (Set.mem_singleton _)
  letI : Ring.HasFiniteQuotients (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :=
    Ring.HasFiniteQuotients.of_module_finite ℤ _
  letI : Fintype {P : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) // d ∈ P} :=
    (Ring.HasFiniteQuotients.finite_setOf_mem d hd0).fintype
  apply Finite.of_injective (fun m =>
    (⟨m.val.asIdeal,m.prop hdC⟩ :
      {P : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) // d ∈ P}))
  intro m n h
  apply Subtype.ext
  apply MaximalSpectrum.ext
  exact congrArg Subtype.val h

/-- Every actual invertible B-ideal is the literal extension of an actual
invertible A-ideal. The displayed inverse comes from the reciprocal patch. -/
theorem exists_idealUnit_extension_eq (hD : b^2-4*a*c<0)
    (J : (FractionalIdeal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
      (FractionRing (CoefficientOrder a b c)))ˣ) :
    ∃ L : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ,
      orderIdealExtension a b c hD L=J.val := by
  letI := fractionNumberField a b c hD
  letI := finite_maximalSpectrum_above_orderConductor a b c hD
  obtain ⟨x,y,hxy⟩ := FractionalIdeal.exists_unit_pair_mod_conductor J (orderConductor a b c)
  let A := restrictMaximalIdeal a b c hD J.val
  let B := restrictMaximalIdeal a b c hD J⁻¹.val
  let T := maximalOrderFractionalIdeal a b c hD
  let C := conductorFractionalIdeal a b c hD
  have hAB : A*B=T := by
    change restrictMaximalIdeal a b c hD J.val*restrictMaximalIdeal a b c hD J⁻¹.val=T
    rw [← restrictMaximalIdeal_mul,J.mul_inv,restrictMaximalIdeal_one]
  have hAT : A*T=A := by
    change restrictMaximalIdeal a b c hD J.val*maximalOrderFractionalIdeal a b c hD=
      restrictMaximalIdeal a b c hD J.val
    rw [← restrictMaximalIdeal_one a b c hD,← restrictMaximalIdeal_mul,mul_one]
  have hxyC : (x : FractionRing (CoefficientOrder a b c))*(y : FractionRing _)-1 ∈ C := by
    obtain ⟨z,hz,he⟩ := (FractionalIdeal.mem_coeIdeal _).mp hxy
    have hh := (mem_conductorFractionalIdeal_iff a b c hD z).mpr hz
    rwa [he] at hh
  let L := FractionalIdeal.overorderPatch C A (x : FractionRing _)
  let M := FractionalIdeal.overorderPatch C B (y : FractionRing _)
  have hLM : L*M=1 := FractionalIdeal.overorderPatch_mul_inverse T C A B
    (conductorFractionalIdeal_le_one a b c hD) (maximalOrderFractionalIdeal_mul_conductor a b c hD)
    hAB _ _ x.prop y.prop hxyC
  let U : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ :=
    ⟨L,M,hLM,(mul_comm M L).trans hLM⟩
  have hLT : L*T=A := FractionalIdeal.overorderPatch_mul_overorder T C A B
    (conductorFractionalIdeal_le_one a b c hD) hAT ((mul_comm B A).trans hAB)
    _ _ x.prop y.prop hxyC
  refine ⟨U,?_⟩
  ext z
  change z ∈ orderIdealExtension a b c hD L ↔ z ∈ J.val
  rw [orderIdealExtension_mem_iff_mul_maximalOrder]
  change z ∈ L*T ↔ z ∈ J.val
  rw [hLT]
  exact mem_restrictMaximalIdeal a b c hD J.val z

/-- General surjectivity of the actual canonical Picard extension. -/
theorem orderPicardExtension_surjective (hD : b^2-4*a*c<0) :
    Function.Surjective (orderPicardExtension a b c hD) := by
  letI := fractionNumberField a b c hD
  intro d
  refine ClassGroup.induction (FractionRing (CoefficientOrder a b c)) (fun J => ?_) d
  obtain ⟨L,hL⟩ := exists_idealUnit_extension_eq a b c hD J
  refine ⟨ClassGroup.mk _ L,?_⟩
  rw [orderPicardExtension_mk]
  congr 1
  exact Units.ext hL


/-- Complete conductor Picard quotient, now with the entire maximal-order
class group as codomain. -/
noncomputable def conductorPicardQuotientEquivMaximalClassGroup (hD : b^2-4*a*c<0) :
    ClassGroup (CoefficientOrder a b c) ⧸ (conductorResidueQuotientClassHom a b c hD).range ≃*
      ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) := by
  rw [← orderPicardExtension_ker a b c hD]
  exact QuotientGroup.quotientKerEquivOfSurjective (orderPicardExtension a b c hD)
    (orderPicardExtension_surjective a b c hD)

/-- The complete class-number correction in terms of the residue-unit
quotient and the original-to-maximal unit index. -/
theorem card_classGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient (hD : b^2-4*a*c<0) :
    Nat.card (ClassGroup (CoefficientOrder a b c))*orderUnitIndex a b c =
      Nat.card (ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))) *
        Nat.card (ConductorResidueUnitQuotient a b c) := by
  have h := card_classGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient a b c hD
  rw [MonoidHom.range_eq_top.mpr (orderPicardExtension_surjective a b c hD),Subgroup.card_top] at h
  exact h

/-- Exact unit-weighted conductor correction. Original and maximal units
remain distinct; no numerical value of the unit index is substituted. -/
theorem classNumber_div_orderUnits_eq_maximalClassNumber_div_units_mul_residueQuotient
    (hD : b^2-4*a*c<0) :
    (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ) / Nat.card (CoefficientOrder a b c)ˣ =
      (Nat.card (ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))) : ℚ) /
        Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ *
          Nat.card (ConductorResidueUnitQuotient a b c) := by
  have hU : (orderUnitIndex a b c : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (orderUnitIndex_pos a b c hD))
  have hc : (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ)*(orderUnitIndex a b c : ℚ) =
      (Nat.card (ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))) : ℚ)*
        Nat.card (ConductorResidueUnitQuotient a b c) := by
    exact_mod_cast card_classGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient a b c hD
  have hu : (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ : ℚ) =
      (Nat.card (CoefficientOrder a b c)ˣ : ℚ)*(orderUnitIndex a b c : ℚ) := by
    exact_mod_cast card_integerUnits_eq_orderUnits_mul_index a b c
  rw [hu]
  calc
    (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ) / Nat.card (CoefficientOrder a b c)ˣ =
      ((Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ)*(orderUnitIndex a b c : ℚ)) /
        ((Nat.card (CoefficientOrder a b c)ˣ : ℚ)*(orderUnitIndex a b c : ℚ)) := by
          rw [mul_div_mul_right _ _ hU]
    _ = _ := by rw [hc]; ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- General actual conductor Picard surjectivity for K's original order. -/
theorem binaryOrderPicardExtension_surjective (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Function.Surjective K.binaryOrderPicardExtension := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact BinaryNormIdeal.orderPicardExtension_surjective _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- Full class-number correction using K's actual conductor quotient and U. -/
theorem card_binaryClassGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (ClassGroup (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant))*
      K.binaryOrderUnitIndex =
        Nat.card (ClassGroup (NumberField.RingOfIntegers
          (FractionRing (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)))) *
            Nat.card (BinaryNormIdeal.ConductorResidueUnitQuotient 1 (K.binaryPrimitiveDiscriminant%2)
              (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact BinaryNormIdeal.card_classGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient _ _ _
    K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms FractionalIdeal.overorderPatch
#assert_standard_axioms FractionalIdeal.overorderPatch_mul_inverse
#assert_standard_axioms FractionalIdeal.overorderPatch_mul_overorder
#assert_standard_axioms BinaryNormIdeal.restrictMaximalIdeal
#assert_standard_axioms BinaryNormIdeal.mem_restrictMaximalIdeal
#assert_standard_axioms BinaryNormIdeal.restrictMaximalIdeal_mul
#assert_standard_axioms BinaryNormIdeal.restrictMaximalIdeal_one
#assert_standard_axioms BinaryNormIdeal.finite_maximalSpectrum_above_orderConductor
#assert_standard_axioms BinaryNormIdeal.exists_idealUnit_extension_eq
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_surjective
#assert_standard_axioms BinaryNormIdeal.conductorPicardQuotientEquivMaximalClassGroup
#assert_standard_axioms BinaryNormIdeal.card_classGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient
#assert_standard_axioms BinaryNormIdeal.classNumber_div_orderUnits_eq_maximalClassNumber_div_units_mul_residueQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderPicardExtension_surjective
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryClassGroup_mul_unitIndex_eq_maximalClassGroup_mul_residueQuotient
