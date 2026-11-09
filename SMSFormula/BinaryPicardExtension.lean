import SMSFormula.BinaryConductorKernel
import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Extension to the same maximal order

The actual extension of invertible original-order fractional ideals descends
to the canonical ClassGroup. The field stays the original FractionRing.
The carrier comparison identifies extension with multiplication by the
already constructed maximal-order fractional ideal.
-/

open scoped nonZeroDivisors

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The original embedding maps nonzero denominators to nonzero denominators. -/
theorem orderToRingOfIntegers_nonZeroDivisors :
    (CoefficientOrder a b c)⁰ ≤ Submonoid.comap
      (orderToRingOfIntegers a b c).toRingHom
      (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰ :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (orderToRingOfIntegers_injective a b c)

/-- Fractional-ideal extension into the same fraction field. The source order
is not required to be integrally closed. -/
noncomputable def orderIdealExtension (hD : b^2-4*a*c < 0) :
    FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)) →+*
      FractionalIdeal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
        (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionNumberField a b c hD
  exact FractionalIdeal.extendedHom' _ (orderToRingOfIntegers_nonZeroDivisors a b c)

/-- The localization map of the actual order embedding is the identity on
its original field. -/
theorem orderLocalizationMap_eq_id (hD : b^2-4*a*c < 0) :
    letI := fractionNumberField a b c hD
    IsLocalization.map (FractionRing (CoefficientOrder a b c))
      (orderToRingOfIntegers a b c).toRingHom
      (orderToRingOfIntegers_nonZeroDivisors a b c) =
        RingHom.id (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionNumberField a b c hD
  apply IsLocalization.map_unique
  intro x
  rfl

/-- The literal B-span of the original fractional ideal in the same field. -/
theorem coe_orderIdealExtension (hD : b^2-4*a*c < 0)
    (J : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) :
    (orderIdealExtension a b c hD J :
      Submodule (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
        (FractionRing (CoefficientOrder a b c))) =
      Submodule.span _ (J : Set (FractionRing (CoefficientOrder a b c))) := by
  letI := fractionNumberField a b c hD
  simp only [orderIdealExtension,FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span,orderLocalizationMap_eq_id a b c hD,
    RingHom.id_apply]
  congr 1
  exact Set.image_id _

/-- Principals extend with the same field element as generator. -/
theorem orderIdealExtension_spanSingleton (hD : b^2-4*a*c < 0)
    (x : FractionRing (CoefficientOrder a b c)) :
    letI := fractionNumberField a b c hD
    orderIdealExtension a b c hD (FractionalIdeal.spanSingleton _ x) =
      FractionalIdeal.spanSingleton _ x := by
  letI := fractionNumberField a b c hD
  apply FractionalIdeal.coeToSubmodule_injective
  change (orderIdealExtension a b c hD (FractionalIdeal.spanSingleton _ x) :
    Submodule (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
      (FractionRing (CoefficientOrder a b c))) =
        ((FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰ x : FractionalIdeal
          (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))⁰
          (FractionRing (CoefficientOrder a b c))) : Submodule
          (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
          (FractionRing (CoefficientOrder a b c)))
  rw [coe_orderIdealExtension,FractionalIdeal.coe_spanSingleton]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨r,hr⟩ := (FractionalIdeal.mem_spanSingleton _).mp hy
    rw [← hr]
    simpa only [Algebra.smul_def,orderToRingOfIntegers_coe] using
      (Submodule.span (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) {x}).smul_mem (orderToRingOfIntegers a b c r)
      (Submodule.subset_span (Set.mem_singleton x))
  · apply Submodule.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Submodule.subset_span (FractionalIdeal.mem_spanSingleton_self _ x)

/-- Multiplication by the already constructed B fractional ideal is exactly
the same B-span, when scalars are restricted to the original order. -/
theorem orderIdealExtension_mem_iff_mul_maximalOrder (hD : b^2-4*a*c < 0)
    (J : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))
    (x : FractionRing (CoefficientOrder a b c)) :
    x ∈ orderIdealExtension a b c hD J ↔ x ∈ J*maximalOrderFractionalIdeal a b c hD := by
  change x ∈ (orderIdealExtension a b c hD J :
    Submodule (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
      (FractionRing (CoefficientOrder a b c))) ↔ _
  rw [coe_orderIdealExtension]
  constructor
  · intro hx
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_)
      (fun r y _ hy => ?_) hx
    · simpa using FractionalIdeal.mul_mem_mul hy
        (FractionalIdeal.one_le.mp (one_le_maximalOrderFractionalIdeal a b c hD))
    · exact (J*maximalOrderFractionalIdeal a b c hD).zero_mem
    · exact ((J*maximalOrderFractionalIdeal a b c hD : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) : Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))).add_mem hy hz
    · change algebraMap _ _ r*y ∈ _
      change y ∈ ((J*maximalOrderFractionalIdeal a b c hD : FractionalIdeal
        (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) :
          Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))) at hy
      rw [FractionalIdeal.coe_mul] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => ?_)
      · have hm := (maximalOrderSubalgebra a b c).mul_mem ⟨r,rfl⟩ hv
        have hh := FractionalIdeal.mul_mem_mul hu
          (show algebraMap _ _ r*v ∈ maximalOrderFractionalIdeal a b c hD from hm)
        convert hh using 1
        ring
      · simpa only [mul_add] using ((J*maximalOrderFractionalIdeal a b c hD : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) : Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))).add_mem
          hu hv
  · intro hx
    change x ∈ ((J*maximalOrderFractionalIdeal a b c hD : FractionalIdeal
        (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) :
          Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))) at hx
    rw [FractionalIdeal.coe_mul] at hx
    refine Submodule.mul_induction_on hx (fun u hu v hv => ?_)
      (fun u v hu hv => Submodule.add_mem _ hu hv)
    obtain ⟨r,rfl⟩ := (mem_maximalOrderFractionalIdeal a b c hD v).mp hv
    have hh := (Submodule.span _ (J : Set (FractionRing (CoefficientOrder a b c)))).smul_mem r
      (Submodule.subset_span hu)
    simpa only [Algebra.smul_def,mul_comm] using hh


/-- Extension preserves principal fractional-ideal units with their actual
original field generators. -/
theorem orderIdealExtension_toPrincipalIdeal (hD : b^2-4*a*c < 0)
    (x : (FractionRing (CoefficientOrder a b c))ˣ) :
    letI := fractionNumberField a b c hD
    Units.map (orderIdealExtension a b c hD).toMonoidHom
      (toPrincipalIdeal (CoefficientOrder a b c) _ x) =
        toPrincipalIdeal
          (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) _ x := by
  letI := fractionNumberField a b c hD
  apply Units.ext
  simp only [Units.coe_map,coe_toPrincipalIdeal]
  exact orderIdealExtension_spanSingleton a b c hD x.val

/-- The actual canonical Picard extension. Both ClassGroups keep their
standard Mathlib carriers; the source need not be maximal. -/
noncomputable def orderPicardExtension (hD : b^2-4*a*c < 0) :
    ClassGroup (CoefficientOrder a b c) →*
      ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) := by
  letI := fractionNumberField a b c hD
  refine QuotientGroup.lift (toPrincipalIdeal (CoefficientOrder a b c)
    (FractionRing (CoefficientOrder a b c))).range
    ((ClassGroup.mk (FractionRing (CoefficientOrder a b c))).comp
      (Units.map (orderIdealExtension a b c hD).toMonoidHom)) ?_
  rintro J ⟨x,rfl⟩
  change ClassGroup.mk _ (Units.map (orderIdealExtension a b c hD).toMonoidHom
    (toPrincipalIdeal _ _ x))=1
  rw [orderIdealExtension_toPrincipalIdeal]
  apply ClassGroup.mk_eq_one_iff.mpr
  rw [coe_toPrincipalIdeal,FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_,rfl⟩⟩

/-- The class extension computes on any actual invertible ideal, with no
choice of coprime representative or caller certificate. -/
theorem orderPicardExtension_mk (hD : b^2-4*a*c < 0)
    (J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ) :
    letI := fractionNumberField a b c hD
    orderPicardExtension a b c hD (ClassGroup.mk _ J) =
      ClassGroup.mk (FractionRing (CoefficientOrder a b c))
        (Units.map (orderIdealExtension a b c hD).toMonoidHom J) := by
  letI := fractionNumberField a b c hD
  rw [← ClassGroup.Quot_mk_eq_mk]
  rfl

/-- The connecting ideal extends to the unit ideal in the same maximal
order. -/
theorem orderIdealExtension_residueConnectingIdeal (hD : b^2-4*a*c < 0)
    (q : ConductorResidueUnits a b c) :
    orderIdealExtension a b c hD (residueConnectingIdealUnit a b c hD q) = 1 := by
  ext x
  rw [orderIdealExtension_mem_iff_mul_maximalOrder,
    residueConnectingIdeal_mul_maximalOrder]
  exact (mem_maximalOrderFractionalIdeal a b c hD x).trans
    (FractionalIdeal.mem_one_iff _).symm

/-- Every actual connecting class lies in the kernel of the actual extension. -/
theorem orderPicardExtension_conductorResidueClassHom (hD : b^2-4*a*c < 0)
    (q : ConductorResidueUnits a b c) :
    orderPicardExtension a b c hD (conductorResidueClassHom a b c hD q)=1 := by
  letI := fractionNumberField a b c hD
  rw [conductorResidueClassHom,MonoidHom.comp_apply,orderPicardExtension_mk]
  have h : Units.map (orderIdealExtension a b c hD).toMonoidHom
      (residueConnectingIdealUnit a b c hD q)=1 := by
    apply Units.ext
    exact orderIdealExtension_residueConnectingIdeal a b c hD q
  change ClassGroup.mk _ (Units.map (orderIdealExtension a b c hD).toMonoidHom
    (residueConnectingIdealUnit a b c hD q))=1
  rw [h,map_one]

/-- Quotient descent uses the same already defined connecting map. -/
theorem orderPicardExtension_conductorResidueQuotientClassHom (hD : b^2-4*a*c < 0)
    (q : ConductorResidueUnitQuotient a b c) :
    orderPicardExtension a b c hD (conductorResidueQuotientClassHom a b c hD q)=1 := by
  refine QuotientGroup.induction_on q fun u => ?_
  exact orderPicardExtension_conductorResidueClassHom a b c hD u

/-- One inclusion in the conductor Picard sequence: the range of the residue
quotient class map lies in the kernel of the extension map.  The reverse
inclusion and surjectivity are not proved here. -/
theorem conductorResidueQuotientClassHom_range_le_extension_ker (hD : b^2-4*a*c < 0) :
    (conductorResidueQuotientClassHom a b c hD).range ≤
      (orderPicardExtension a b c hD).ker := by
  rintro x ⟨q,rfl⟩
  exact orderPicardExtension_conductorResidueQuotientClassHom a b c hD q

/-- The exact kernel criterion is principality of the actual extended ideal.
This is not the unresolved equality with the connecting image. -/
theorem orderPicardExtension_mk_eq_one_iff (hD : b^2-4*a*c < 0)
    (J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ) :
    letI := fractionNumberField a b c hD
    orderPicardExtension a b c hD (ClassGroup.mk _ J)=1 ↔
      ∃ x : (FractionRing (CoefficientOrder a b c))ˣ,
        orderIdealExtension a b c hD J = FractionalIdeal.spanSingleton _ x.val := by
  letI := fractionNumberField a b c hD
  rw [orderPicardExtension_mk]
  constructor
  · exact FractionalIdeal.exists_unit_generator_of_class_eq_one _
  · rintro ⟨x,hx⟩
    apply ClassGroup.mk_eq_one_iff.mpr
    change (orderIdealExtension a b c hD J : Submodule
      (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
        (FractionRing (CoefficientOrder a b c))).IsPrincipal
    rw [hx,FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_,rfl⟩⟩


/-- Every extension-kernel class has an actual invertible representative
whose extension is literally the unit ideal of B. The scalar normalization
is principal in the original field, so its original class is unchanged. -/
theorem exists_unit_representative_extension_one (hD : b^2-4*a*c < 0)
    (d : ClassGroup (CoefficientOrder a b c)) (hd : orderPicardExtension a b c hD d=1) :
    ∃ J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ,
      ClassGroup.mk _ J=d ∧ orderIdealExtension a b c hD J=1 := by
  letI := fractionNumberField a b c hD
  revert hd
  refine ClassGroup.induction (FractionRing (CoefficientOrder a b c)) (fun J hd => ?_) d
  obtain ⟨x,hx⟩ := (orderPicardExtension_mk_eq_one_iff a b c hD J).mp hd
  let P := toPrincipalIdeal (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) x⁻¹
  refine ⟨J*P,?_,?_⟩
  · have hp : ClassGroup.mk (FractionRing (CoefficientOrder a b c)) P=1 := by
      apply ClassGroup.mk_eq_one_iff.mpr
      rw [show (P : FractionalIdeal (CoefficientOrder a b c)⁰
        (FractionRing (CoefficientOrder a b c))) =
        FractionalIdeal.spanSingleton _ x⁻¹.val from coe_toPrincipalIdeal x⁻¹,
        FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨_,rfl⟩⟩
    rw [map_mul,hp,mul_one]
  · change orderIdealExtension a b c hD ((J : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))*P.val)=1
    rw [map_mul,hx,show P.val=FractionalIdeal.spanSingleton _ x⁻¹.val from coe_toPrincipalIdeal x⁻¹,
      orderIdealExtension_spanSingleton,FractionalIdeal.spanSingleton_mul_spanSingleton]
    simp

/-- A normalized ideal lies inside the same maximal order and absorbs the
actual conductor exactly. No invertibility of B over A is asserted. -/
theorem conductor_bounds_of_extension_one (hD : b^2-4*a*c < 0)
    (J : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))
    (hJ : orderIdealExtension a b c hD J=1) :
    conductorFractionalIdeal a b c hD ≤ J ∧ J ≤ maximalOrderFractionalIdeal a b c hD ∧
      J*conductorFractionalIdeal a b c hD=conductorFractionalIdeal a b c hD := by
  have hext : J*maximalOrderFractionalIdeal a b c hD=maximalOrderFractionalIdeal a b c hD := by
    ext x
    rw [← orderIdealExtension_mem_iff_mul_maximalOrder,hJ]
    exact (FractionalIdeal.mem_one_iff _).trans (mem_maximalOrderFractionalIdeal a b c hD x).symm
  have hprod : J*conductorFractionalIdeal a b c hD=conductorFractionalIdeal a b c hD := by
    calc
      J*conductorFractionalIdeal a b c hD =
        J*(maximalOrderFractionalIdeal a b c hD*conductorFractionalIdeal a b c hD) := by
          rw [maximalOrderFractionalIdeal_mul_conductor]
      _ = (J*maximalOrderFractionalIdeal a b c hD)*conductorFractionalIdeal a b c hD :=
        (mul_assoc _ _ _).symm
      _ = conductorFractionalIdeal a b c hD := by
        rw [hext,maximalOrderFractionalIdeal_mul_conductor]
  refine ⟨?_,?_,hprod⟩
  · calc
      conductorFractionalIdeal a b c hD = J*conductorFractionalIdeal a b c hD := hprod.symm
      _ ≤ J*1 := mul_le_mul_right (conductorFractionalIdeal_le_one a b c hD) J
      _ = J := mul_one J
  · calc
      J = J*1 := (mul_one J).symm
      _ ≤ J*maximalOrderFractionalIdeal a b c hD :=
        mul_le_mul_right (one_le_maximalOrderFractionalIdeal a b c hD) J
      _ = maximalOrderFractionalIdeal a b c hD := hext


/-- The actual inverse also extends to B; no inverse is guessed from
an overorder module or a local span. -/
theorem orderIdealExtension_inv_eq_one (hD : b^2-4*a*c < 0)
    (J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ)
    (hJ : orderIdealExtension a b c hD J=1) :
    orderIdealExtension a b c hD J⁻¹.val=1 := by
  have h : Units.map (orderIdealExtension a b c hD).toMonoidHom J=1 := Units.ext hJ
  have hi : Units.map (orderIdealExtension a b c hD).toMonoidHom J⁻¹=1 := by
    rw [map_inv,h,inv_one]
  exact congrArg Units.val hi

/-- A kernel class has one actual representative and its actual inverse
between the conductor and B. These are consequences, not caller certificates. -/
theorem exists_bounded_inverse_pair_of_extension_kernel (hD : b^2-4*a*c < 0)
    (d : ClassGroup (CoefficientOrder a b c)) (hd : orderPicardExtension a b c hD d=1) :
    ∃ J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ,
      ClassGroup.mk _ J=d ∧ orderIdealExtension a b c hD J=1 ∧
      conductorFractionalIdeal a b c hD ≤ J.val ∧ J.val ≤ maximalOrderFractionalIdeal a b c hD ∧
      conductorFractionalIdeal a b c hD ≤ J⁻¹.val ∧
        J⁻¹.val ≤ maximalOrderFractionalIdeal a b c hD ∧
      J.val*conductorFractionalIdeal a b c hD=conductorFractionalIdeal a b c hD ∧
      J⁻¹.val*conductorFractionalIdeal a b c hD=conductorFractionalIdeal a b c hD := by
  obtain ⟨J,hclass,hJ⟩ := exists_unit_representative_extension_one a b c hD d hd
  obtain ⟨hl,hu,hprod⟩ := conductor_bounds_of_extension_one a b c hD J.val hJ
  obtain ⟨hil,hiu,hiprod⟩ := conductor_bounds_of_extension_one a b c hD J⁻¹.val
    (orderIdealExtension_inv_eq_one a b c hD J hJ)
  exact ⟨J,hclass,hJ,hl,hu,hil,hiu,hprod,hiprod⟩

/-- At actual index one the extension has no nontrivial kernel. This includes
the zero conductor residue ring; no positive-modulus exclusion is used. -/
theorem orderPicardExtension_injective_of_index_one (hD : b^2-4*a*c < 0)
    (hI : orderIndex a b c=1) : Function.Injective (orderPicardExtension a b c hD) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro d hd
  change d=1
  obtain ⟨J,hclass,hJ⟩ := exists_unit_representative_extension_one a b c hD d hd
  have hC : conductorFractionalIdeal a b c hD=1 := by
    have hCT : conductorFractionalIdeal a b c hD=maximalOrderFractionalIdeal a b c hD := by
      unfold conductorFractionalIdeal
      rw [hI,Nat.cast_one,FractionalIdeal.spanSingleton_one,one_mul]
    exact le_antisymm (conductorFractionalIdeal_le_one a b c hD)
      (hCT ▸ one_le_maximalOrderFractionalIdeal a b c hD)
  obtain ⟨hl,hu,_⟩ := conductor_bounds_of_extension_one a b c hD J.val hJ
  have hT : maximalOrderFractionalIdeal a b c hD=1 := by
    simpa only [conductorFractionalIdeal,hI,Nat.cast_one,FractionalIdeal.spanSingleton_one,one_mul]
      using hC
  have hval : J.val=1 := le_antisymm (hT ▸ hu) (hC ▸ hl)
  have hunit : J=1 := Units.ext hval
  rw [← hclass,hunit,map_one]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The canonical Picard extension for K's original order and same field. -/
noncomputable def binaryOrderPicardExtension (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (NumberField.RingOfIntegers
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderPicardExtension _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The already defined connecting image is contained in the actual
extension kernel, with original content and discriminant unchanged. -/
theorem binaryConductorConnectingImage_le_extension_ker (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryConductorResidueQuotientClassHom.range ≤ K.binaryOrderPicardExtension.ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact conductorResidueQuotientClassHom_range_le_extension_ker _ _ _
    K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.orderToRingOfIntegers_nonZeroDivisors
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension
#assert_standard_axioms BinaryNormIdeal.orderLocalizationMap_eq_id
#assert_standard_axioms BinaryNormIdeal.coe_orderIdealExtension
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension_spanSingleton
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension_mem_iff_mul_maximalOrder
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension_toPrincipalIdeal
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_mk
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension_residueConnectingIdeal
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_conductorResidueClassHom
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_conductorResidueQuotientClassHom
#assert_standard_axioms BinaryNormIdeal.conductorResidueQuotientClassHom_range_le_extension_ker
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_mk_eq_one_iff
#assert_standard_axioms BinaryNormIdeal.exists_unit_representative_extension_one
#assert_standard_axioms BinaryNormIdeal.conductor_bounds_of_extension_one
#assert_standard_axioms BinaryNormIdeal.orderIdealExtension_inv_eq_one
#assert_standard_axioms BinaryNormIdeal.exists_bounded_inverse_pair_of_extension_kernel
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_injective_of_index_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderPicardExtension
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryConductorConnectingImage_le_extension_ker
