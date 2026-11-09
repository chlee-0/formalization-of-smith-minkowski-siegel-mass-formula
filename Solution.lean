import SMSFormula.StatementsExamples
import SMSFormula.Applications.Unimodular.E8Mass
import SMSFormula.Applications.Unimodular.TypeITotalMass
import SMSFormula.Applications.Unimodular.TypeIITotalMass
import SMSFormula.Applications.Examples.A2Intrinsic
import SMSFormula.Applications.Examples.TernaryMass
import SMSFormula.Applications.Examples.A4Mass

/-!
# Solution

Proofs of the statements of `Challenge.lean` from the library.
-/

open SMSFormula.Statements PositiveDefiniteIntegralLattice MassFormulaReleaseExamples

namespace SMSFormula.Challenge

theorem genusMass_A1 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 1))) ∧
      genusMass (CartanMatrix.A 1) = 1 / 2 :=
  genusMass_cartanA1

theorem genusMass_A2 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 2))) ∧
      genusMass (CartanMatrix.A 2) = 1 / 12 := by
  have h := genusMass_of_isometric a2.latticeOfPolarForm cartanA2_isometric
  exact ⟨h.1, h.2.trans a2_latticeOfPolarForm_ordinaryGenusMass⟩

theorem genusMass_ternary :
    Finite (IsometryClasses (SameGenus !![(1 : ℤ), 0, 0; 0, 2, 0; 0, 0, 11])) ∧
      genusMass !![(1 : ℤ), 0, 0; 0, 2, 0; 0, 0, 11] = 3 / 8 := by
  have h := genusMass_of_isometric ternaryLattice (isometric_equivalence.refl _)
  exact ⟨h.1, h.2.trans ternary_ordinaryGenusMass⟩

theorem genusMass_A4 :
    Finite (IsometryClasses (SameGenus (CartanMatrix.A 4))) ∧
      genusMass (CartanMatrix.A 4) = 1 / 240 := by
  have h := genusMass_of_isometric a4.latticeOfPolarForm cartanA4_isometric
  exact ⟨h.1, h.2.trans a4_latticeOfPolarForm_ordinaryGenusMass⟩

theorem genusMass_E8 :
    Finite (IsometryClasses (SameGenus CartanMatrix.E₈)) ∧
      genusMass CartanMatrix.E₈ = 1 / 696729600 :=
  ⟨genusMass_cartanE8.1, genusMass_cartanE8.2.trans e8Lattice_ordinaryGenusMass⟩

theorem mass_typeI (n : ℕ) :
    Finite (IsometryClasses (@IsTypeI n)) ∧ mass (@IsTypeI n) = typeIConstant n := by
  classical
  have h := mass_eq_sum (ι := UnimodularTypeIIsometryClass n) IsTypeI typeIClassRepresentative
    (fun C => (isTypeI_iff _).2
      ⟨typeIClassRepresentative_isUnimodular C, typeIClassRepresentative_hasOddNorm C⟩)
    (fun C D hCD => Subtype.ext (by
      rw [typeIClassRepresentative_globalIsometryClass C,
        typeIClassRepresentative_globalIsometryClass D]
      exact globalIsometryClass_eq_of_isGlobalIsometry hCD))
    (fun L hL => by
      obtain ⟨hU, hO⟩ := (isTypeI_iff L).1 hL
      let C : UnimodularTypeIIsometryClass n := ⟨L.globalIsometryClass, L, hU, hO, rfl⟩
      exact ⟨C, isGlobalIsometry_of_globalIsometryClass_eq
        (typeIClassRepresentative_globalIsometryClass C).symm⟩)
  refine ⟨h.1, ?_⟩
  calc mass (@IsTypeI n) = totalTypeIClassMass n := h.2
    _ = UnimodularMass.typeIConstant n := totalTypeIClassMass_eq_typeIConstant
    _ = typeIConstant n := rfl

theorem mass_typeII (n : ℕ) :
    Finite (IsometryClasses (@IsTypeII n)) ∧ mass (@IsTypeII n) = typeIIConstant n := by
  classical
  have h := mass_eq_sum (ι := UnimodularTypeIIIsometryClass n) IsTypeII typeIIClassRepresentative
    (fun C => (isTypeII_iff _).2
      ⟨typeIIClassRepresentative_isUnimodular C, typeIIClassRepresentative_hasEvenNorms C⟩)
    (fun C D hCD => Subtype.ext (by
      rw [typeIIClassRepresentative_globalIsometryClass C,
        typeIIClassRepresentative_globalIsometryClass D]
      exact globalIsometryClass_eq_of_isGlobalIsometry hCD))
    (fun L hL => by
      obtain ⟨hU, hE⟩ := (isTypeII_iff L).1 hL
      let C : UnimodularTypeIIIsometryClass n := ⟨L.globalIsometryClass, L, hU, hE, rfl⟩
      exact ⟨C, isGlobalIsometry_of_globalIsometryClass_eq
        (typeIIClassRepresentative_globalIsometryClass C).symm⟩)
  refine ⟨h.1, ?_⟩
  calc mass (@IsTypeII n) = totalTypeIIClassMass n := h.2
    _ = UnimodularMass.typeIIConstant n := totalTypeIIClassMass_eq_typeIIConstant n
    _ = typeIIConstant n := rfl

end SMSFormula.Challenge
