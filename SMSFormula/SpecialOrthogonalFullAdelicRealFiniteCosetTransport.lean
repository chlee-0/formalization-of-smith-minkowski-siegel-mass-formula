import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteOpenStabilizer
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countable transport from the open full-adelic stabilizer to its cosets

The quotient by the open real/unrestricted, finite/integral stabilizer is
discrete.  Since the ambient full-adelic special orthogonal group is second
countable, this quotient is countable.  Left multiplication by the chosen
representative of each quotient class then gives a literal homeomorphism from
the stabilizer subgroup onto that chosen coset.

This module is measure-independent.  In particular, it does
not sum translated subgroup measures or assert an ambient Haar measure.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The concrete full-adelic special orthogonal group is second countable,
transported through its real/finite splitting. -/
noncomputable instance
    concreteFullAdelicSpecialOrthogonalGroupSecondCountableTopology
    (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopology L.ConcreteFullAdelicSpecialOrthogonalGroup := by
  letI :
      SecondCountableTopology L.ConcreteRealSpecialOrthogonalGroup :=
    L.concreteRealSpecialOrthogonalGroup_secondCountable
  exact
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.isEmbedding.secondCountableTopology

/-- The quotient by the open full-adelic stabilizer has the discrete
topology. -/
theorem fullAdelicRealFiniteLatticeStabilizerCosetIndex_discreteTopology
    (L : PositiveDefiniteIntegralLattice n) :
    DiscreteTopology
      L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
  QuotientGroup.discreteTopology
    L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup

/-- The quotient indexing the open stabilizer's left cosets is countable. -/
noncomputable instance
    fullAdelicRealFiniteLatticeStabilizerCosetIndexCountable
    (L : PositiveDefiniteIntegralLattice n) :
    Countable L.FullAdelicRealFiniteLatticeStabilizerCosetIndex := by
  letI :
      DiscreteTopology
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
    L.fullAdelicRealFiniteLatticeStabilizerCosetIndex_discreteTopology
  letI :
      SecondCountableTopology
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
    QuotientGroup.instSecondCountableTopology
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup
  exact countable_of_Lindelof_of_discrete

/-- The subtype carrier of one chosen full-adelic stabilizer coset. -/
abbrev FullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :=
  {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
    g ∈ L.fullAdelicRealFiniteLatticeStabilizerCoset C}

/-- Left multiplication by the chosen representative gives the underlying
equivalence from the stabilizer to its chosen left coset. -/
def fullAdelicRealFiniteLatticeStabilizerCosetEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup ≃
      L.FullAdelicRealFiniteLatticeStabilizerCoset C where
  toFun h :=
    ⟨Quotient.out C * h, by
      exact ⟨h, h.property, rfl⟩⟩
  invFun g :=
    ⟨(Quotient.out C)⁻¹ * g, by
      rcases g.property with ⟨h, hh, hEq⟩
      rw [← hEq]
      simpa only [inv_mul_cancel_left] using hh⟩
  left_inv h := by
    ext
    simp only [inv_mul_cancel_left]
  right_inv g := by
    ext
    simp only [mul_inv_cancel_left]

/-- Left multiplication by the chosen representative identifies the natural
stabilizer homeomorphically with the corresponding chosen left coset. -/
def fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup ≃ₜ
      L.FullAdelicRealFiniteLatticeStabilizerCoset C where
  toEquiv := L.fullAdelicRealFiniteLatticeStabilizerCosetEquiv C
  continuous_toFun :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- Ambient formula for the chosen-coset homeomorphism. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph_apply_coe
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup) :
    (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C h :
      L.ConcreteFullAdelicSpecialOrthogonalGroup) =
        Quotient.out C * h :=
  rfl

/-- Ambient formula for the inverse chosen-coset homeomorphism. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph_symm_apply_coe
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    (g : L.FullAdelicRealFiniteLatticeStabilizerCoset C) :
    ((L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).symm g :
      L.ConcreteFullAdelicSpecialOrthogonalGroup) =
        (Quotient.out C)⁻¹ * g :=
  rfl

/-- Applying the inverse after transport recovers the stabilizer point. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph_symm_apply_apply
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup) :
    (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).symm
        (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C h) = h :=
  (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).symm_apply_apply h

/-- Transporting the inverse recovers the chosen-coset point. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph_apply_symm_apply
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    (g : L.FullAdelicRealFiniteLatticeStabilizerCoset C) :
    L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C
        ((L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).symm g) = g :=
  (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).apply_symm_apply g

end PositiveDefiniteIntegralLattice
