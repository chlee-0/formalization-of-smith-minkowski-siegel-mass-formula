import SMSFormula.BinaryConductorIdeals

/-!
# Descent by original-order residue units

The actual connecting ideal of an original-order residue unit is one.
The residue-to-class homomorphism therefore descends through the quotient
by those units. No Picard exactness or integer residue-ring model is assumed.
-/

open scoped nonZeroDivisors

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The literal conductor pulled back to the original order. -/
noncomputable def originalConductorIdeal : Ideal (CoefficientOrder a b c) :=
  (orderConductor a b c).comap (orderToRingOfIntegers a b c).toRingHom

/-- The actual original-to-maximal conductor residue map. -/
noncomputable def originalConductorResidueMap :
    CoefficientOrder a b c ⧸ originalConductorIdeal a b c →+*
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderConductor a b c :=
  Ideal.quotientMap _ (orderToRingOfIntegers a b c).toRingHom le_rfl

noncomputable def originalConductorResidueUnitsHom :
    (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)ˣ →* ConductorResidueUnits a b c :=
  Units.map (originalConductorResidueMap a b c).toMonoidHom

/-- A generator from the original order gives an integral connecting ideal. -/
theorem conductorConnectingIdeal_orderElement_le_one (hD : b^2-4*a*c < 0)
    (r : CoefficientOrder a b c) :
    conductorConnectingIdeal a b c hD (orderToRingOfIntegers a b c r) ≤ 1 := by
  apply sup_le _ (conductorFractionalIdeal_le_one a b c hD)
  apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨r,rfl⟩

/-- An original residue unit gives literally the unit ideal, not merely a
trivial class. Its inverse is constructed from its original inverse residue. -/
theorem residueConnectingIdealHom_originalResidueUnit (hD : b^2-4*a*c < 0)
    (q : (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)ˣ) :
    residueConnectingIdealHom a b c hD (originalConductorResidueUnitsHom a b c q) = 1 := by
  let r : CoefficientOrder a b c := Quotient.out q.val
  let s : CoefficientOrder a b c := Quotient.out q⁻¹.val
  have hr : Ideal.Quotient.mk (originalConductorIdeal a b c) r=q.val := Ideal.Quotient.mk_out _
  have hs : Ideal.Quotient.mk (originalConductorIdeal a b c) s=q⁻¹.val := Ideal.Quotient.mk_out _
  have hC : r*s-1 ∈ originalConductorIdeal a b c := by
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp
    rw [map_mul,hr,hs]
    simp
  have hC' : orderToRingOfIntegers a b c r * orderToRingOfIntegers a b c s - 1 ∈
      orderConductor a b c := by
    change orderToRingOfIntegers a b c (r*s-1) ∈ orderConductor a b c at hC
    simpa only [map_sub,map_mul,map_one] using hC
  have hprod := conductorConnectingIdeal_mul_inverse a b c hD _ _ hC'
  have hle := conductorConnectingIdeal_orderElement_le_one a b c hD r
  have hge : 1 ≤ conductorConnectingIdeal a b c hD (orderToRingOfIntegers a b c r) := by
    have hh := mul_le_mul_right (conductorConnectingIdeal_orderElement_le_one a b c hD s)
      (conductorConnectingIdeal a b c hD (orderToRingOfIntegers a b c r))
    simpa only [hprod,mul_one] using hh
  apply Units.ext
  change conductorConnectingIdeal a b c hD
    (conductorResidueLift a b c (originalConductorResidueUnitsHom a b c q))=1
  have heq : conductorConnectingIdeal a b c hD
      (conductorResidueLift a b c (originalConductorResidueUnitsHom a b c q)) =
        conductorConnectingIdeal a b c hD (orderToRingOfIntegers a b c r) := by
    apply conductorConnectingIdeal_eq_of_sub_mem
    apply Ideal.Quotient.eq.mp
    rw [mk_conductorResidueLift]
    change originalConductorResidueMap a b c q.val = _
    rw [← hr]
    rfl
  exact heq.trans (le_antisymm hle hge)

theorem conductorResidueClassHom_originalResidueUnit (hD : b^2-4*a*c < 0)
    (q : (CoefficientOrder a b c ⧸ originalConductorIdeal a b c)ˣ) :
    conductorResidueClassHom a b c hD (originalConductorResidueUnitsHom a b c q) = 1 := by
  change ClassGroup.mk _ (residueConnectingIdealHom a b c hD _) = 1
  rw [residueConnectingIdealHom_originalResidueUnit,map_one]

/-- The actual residue-unit quotient, before identifying the original
residue order with integers modulo the conductor index. -/
abbrev ConductorResidueUnitQuotient :=
  ConductorResidueUnits a b c ⧸ (originalConductorResidueUnitsHom a b c).range

/-- The connecting map descends by all original-order residue units. -/
noncomputable def conductorResidueQuotientClassHom (hD : b^2-4*a*c < 0) :
    ConductorResidueUnitQuotient a b c →* ClassGroup (CoefficientOrder a b c) :=
  QuotientGroup.lift _ (conductorResidueClassHom a b c hD) (by
    rintro q ⟨u,rfl⟩
    exact conductorResidueClassHom_originalResidueUnit a b c hD u)

theorem conductorResidueQuotientClassHom_mk (hD : b^2-4*a*c < 0)
    (q : ConductorResidueUnits a b c) :
    conductorResidueQuotientClassHom a b c hD (QuotientGroup.mk q) =
      conductorResidueClassHom a b c hD q := rfl

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The residue-unit quotient connecting map on K's original order. -/
noncomputable def binaryConductorResidueQuotientClassHom (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    BinaryNormIdeal.ConductorResidueUnitQuotient 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) →*
        ClassGroup (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact BinaryNormIdeal.conductorResidueQuotientClassHom _ _ _ K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.originalConductorIdeal
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueMap
#assert_standard_axioms BinaryNormIdeal.originalConductorResidueUnitsHom
#assert_standard_axioms BinaryNormIdeal.conductorConnectingIdeal_orderElement_le_one
#assert_standard_axioms BinaryNormIdeal.residueConnectingIdealHom_originalResidueUnit
#assert_standard_axioms BinaryNormIdeal.conductorResidueClassHom_originalResidueUnit
#assert_standard_axioms BinaryNormIdeal.ConductorResidueUnitQuotient
#assert_standard_axioms BinaryNormIdeal.conductorResidueQuotientClassHom
#assert_standard_axioms BinaryNormIdeal.conductorResidueQuotientClassHom_mk
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryConductorResidueQuotientClassHom
