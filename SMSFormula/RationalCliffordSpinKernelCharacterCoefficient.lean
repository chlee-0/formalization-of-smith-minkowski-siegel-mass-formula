import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalMuTwoCharacterCohomology
import SMSFormula.RationalQuadraticKummerLocalization

/-!
# The specialized character coefficient of the Clifford--Spin kernel

The completed group-scheme kernel is isomorphic to the explicit algebraic
group `mu_2`.  Its intrinsic Hopf character group is therefore transported
from the already computed group-like elements of `ℚ[ZMod 2]`.  This file
additivizes that group, identifies it with the `ZMod 2` coefficient used in
the continuous Kummer calculation, and packages the resulting `h^0/i^1 = 2`
cohomological factor.

This is the specialized coefficient needed for Ono's orthogonal relative
formula.  It does not introduce a general algebraic-group character functor
and does not address fppf surjectivity of the candidate-to-`SO` morphism.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace RationalTamagawa

/-- The additive form of the intrinsic group-like character group of the
central `mu_2` kernel. -/
abbrev SpinCentralKernelCharacterModule :=
  Additive RationalMuTwoCharacterGroup

/-- The intrinsic Hopf character module is the explicit order-two coefficient
used in the earlier Galois-cohomology reduction. -/
def spinCentralKernelCharacterModuleEquivMuTwo :
    SpinCentralKernelCharacterModule ≃+ MuTwoCharacterModule :=
  (MulEquiv.toAdditive muTwoMonomialGroupLikeEquiv.symm).trans
    AddEquiv.toAdditive_toMultiplicative

/-- The same identification as an integral linear equivalence. -/
def spinCentralKernelCharacterModuleLinearEquivMuTwo :
    SpinCentralKernelCharacterModule ≃ₗ[ℤ] MuTwoCharacterModule :=
  spinCentralKernelCharacterModuleEquivMuTwo.toIntLinearEquiv

/-- The intrinsic central-kernel character module has order two. -/
theorem natCard_spinCentralKernelCharacterModule_eq_two :
    Nat.card SpinCentralKernelCharacterModule = 2 := by
  rw [Nat.card_congr spinCentralKernelCharacterModuleEquivMuTwo.toEquiv]
  exact natCard_muTwoCharacterModule_eq_two

noncomputable instance spinCentralKernelCharacterModuleTopologicalSpace :
    TopologicalSpace SpinCentralKernelCharacterModule := ⊥

instance spinCentralKernelCharacterModuleDiscreteTopology :
    DiscreteTopology SpinCentralKernelCharacterModule := ⟨rfl⟩

/-- The coefficient equivalence is a homeomorphism for the finite discrete
topologies used in continuous Galois cohomology. -/
def spinCentralKernelCharacterModuleContinuousEquivMuTwo :
    SpinCentralKernelCharacterModule ≃ₜ+ MuTwoCharacterModule where
  toAddEquiv := spinCentralKernelCharacterModuleEquivMuTwo
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The constant absolute-Galois representation on the intrinsic character
module transported from the actual central kernel. -/
abbrev spinCentralKernelCharacterRepresentation
    (K : Type) [Field K] : Rep ℤ (Field.absoluteGaloisGroup K) :=
  Rep.trivial ℤ (Field.absoluteGaloisGroup K)
    SpinCentralKernelCharacterModule

/-- The intrinsic kernel-character representation is trivial. -/
@[simp]
theorem spinCentralKernelCharacterRepresentation_apply
    (K : Type) [Field K]
    (σ : Field.absoluteGaloisGroup K)
    (x : SpinCentralKernelCharacterModule) :
    (spinCentralKernelCharacterRepresentation K).ρ σ x = x := by
  rfl

/-- The intrinsic and explicit coefficient identifications intertwine their
trivial absolute-Galois actions. -/
@[simp]
theorem spinCentralKernelCharacterModuleEquivMuTwo_galois
    (K : Type) [Field K]
    (σ : Field.absoluteGaloisGroup K)
    (x : SpinCentralKernelCharacterModule) :
    spinCentralKernelCharacterModuleEquivMuTwo
        ((spinCentralKernelCharacterRepresentation K).ρ σ x) =
      (muTwoCharacterRepresentation K).ρ σ
        (spinCentralKernelCharacterModuleEquivMuTwo x) := by
  rfl

/-- Continuous degree-one cohomology for the intrinsic kernel character
module. -/
abbrev SpinCentralKernelCharacterContinuousH1
    (K : Type) [Field K] :=
  ContinuousAddMonoidHom
    (Additive (Field.absoluteGaloisGroup K))
    SpinCentralKernelCharacterModule

set_option synthInstance.maxHeartbeats 200000 in
/-- The intrinsic and explicit continuous degree-one models are equivalent. -/
def spinCentralKernelCharacterContinuousH1EquivMuTwo
    (K : Type) [Field K] :
    SpinCentralKernelCharacterContinuousH1 K ≃+
      MuTwoContinuousH1 K where
  toFun χ :=
    (spinCentralKernelCharacterModuleContinuousEquivMuTwo :
      ContinuousAddMonoidHom _ _).comp χ
  invFun χ :=
    (spinCentralKernelCharacterModuleContinuousEquivMuTwo.symm :
      ContinuousAddMonoidHom _ _).comp χ
  left_inv χ := by
    apply ContinuousAddMonoidHom.ext
    intro σ
    exact spinCentralKernelCharacterModuleContinuousEquivMuTwo.symm_apply_apply (χ σ)
  right_inv χ := by
    apply ContinuousAddMonoidHom.ext
    intro σ
    exact spinCentralKernelCharacterModuleContinuousEquivMuTwo.apply_symm_apply (χ σ)
  map_add' χ ψ := by
    apply ContinuousAddMonoidHom.ext
    intro σ
    exact map_add spinCentralKernelCharacterModuleContinuousEquivMuTwo (χ σ) (ψ σ)

abbrev RationalSpinCentralKernelCharacterContinuousH1 :=
  SpinCentralKernelCharacterContinuousH1 ℚ

abbrev RealSpinCentralKernelCharacterContinuousH1 :=
  SpinCentralKernelCharacterContinuousH1 ℝ

abbrev PadicSpinCentralKernelCharacterContinuousH1
    (p : ℕ) [Fact p.Prime] :=
  SpinCentralKernelCharacterContinuousH1 ℚ_[p]

/-- Real localization on the intrinsic central-kernel character coefficient,
defined by conjugating the completed `ZMod 2` restriction map. -/
noncomputable def spinCentralKernelCharacterContinuousH1ToReal :
    RationalSpinCentralKernelCharacterContinuousH1 →+
      RealSpinCentralKernelCharacterContinuousH1 :=
  (spinCentralKernelCharacterContinuousH1EquivMuTwo ℝ).symm.toAddMonoidHom.comp
    (rationalMuTwoContinuousH1ToReal.comp
      (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).toAddMonoidHom)

/-- `p`-adic localization on the intrinsic central-kernel character
coefficient. -/
noncomputable def spinCentralKernelCharacterContinuousH1ToPadic
    (p : ℕ) [Fact p.Prime] :
    RationalSpinCentralKernelCharacterContinuousH1 →+
      PadicSpinCentralKernelCharacterContinuousH1 p :=
  (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ_[p]).symm.toAddMonoidHom.comp
    (rationalMuTwoContinuousH1ToPadic p |>.comp
      (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).toAddMonoidHom)

@[simp]
theorem spinCentralKernelCharacterContinuousH1ToReal_equiv
    (χ : RationalSpinCentralKernelCharacterContinuousH1) :
    spinCentralKernelCharacterContinuousH1EquivMuTwo ℝ
        (spinCentralKernelCharacterContinuousH1ToReal χ) =
      rationalMuTwoContinuousH1ToReal
        (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ χ) := by
  exact (spinCentralKernelCharacterContinuousH1EquivMuTwo ℝ).apply_symm_apply _

@[simp]
theorem spinCentralKernelCharacterContinuousH1ToPadic_equiv
    (p : ℕ) [Fact p.Prime]
    (χ : RationalSpinCentralKernelCharacterContinuousH1) :
    spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ_[p]
        (spinCentralKernelCharacterContinuousH1ToPadic p χ) =
      rationalMuTwoContinuousH1ToPadic p
        (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ χ) := by
  exact (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ_[p]).apply_symm_apply _

/-- The fixed part of the intrinsic central-kernel character module. -/
abbrev SpinCentralKernelCharacterFixedPart
    (K : Type) [Field K] :=
  (spinCentralKernelCharacterRepresentation K).ρ.invariants

/-- The entire intrinsic character module is fixed. -/
theorem spinCentralKernelCharacterFixedPart_eq_top
    (K : Type) [Field K] :
    (spinCentralKernelCharacterRepresentation K).ρ.invariants = ⊤ :=
  Representation.invariants_eq_top _

/-- Ono's numerator for the actual specialized Spin kernel is two. -/
theorem natCard_spinCentralKernelCharacterFixedPart_eq_two
    (K : Type) [Field K] :
    Nat.card (SpinCentralKernelCharacterFixedPart K) = 2 := by
  change Nat.card
      ↑((spinCentralKernelCharacterRepresentation K).ρ.invariants) = 2
  rw [spinCentralKernelCharacterFixedPart_eq_top]
  simpa using natCard_spinCentralKernelCharacterModule_eq_two

/-- The specialized continuous localization denominator, transported through
the explicit intrinsic-character-module equivalence, is the completed
order-two Kummer kernel. -/
noncomputable def SpinCentralKernelCharacterI1 :
    AddSubgroup RationalSpinCentralKernelCharacterContinuousH1 :=
  AddSubgroup.comap
    (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).toAddMonoidHom
    rationalMuTwoContinuousH1LocalGlobalKernel

/-- The transported intrinsic localization kernel is additively equivalent to
the completed `ZMod 2` localization kernel. -/
def spinCentralKernelCharacterI1EquivMuTwo :
    SpinCentralKernelCharacterI1 ≃+
      rationalMuTwoContinuousH1LocalGlobalKernel where
  toFun χ := ⟨spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ χ.1, χ.2⟩
  invFun χ :=
    ⟨(spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).symm χ.1, by
      change spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ
          ((spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).symm χ.1) ∈
        rationalMuTwoContinuousH1LocalGlobalKernel
      rw [(spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).apply_symm_apply]
      exact χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    exact (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).symm_apply_apply χ.1
  right_inv χ := by
    apply Subtype.ext
    exact (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ).apply_symm_apply χ.1
  map_add' χ ψ := by
    apply Subtype.ext
    exact map_add (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ) χ.1 ψ.1

/-- Membership in the intrinsic denominator has the expected literal local-
triviality description. -/
theorem mem_spinCentralKernelCharacterI1_iff
    (χ : RationalSpinCentralKernelCharacterContinuousH1) :
    χ ∈ SpinCentralKernelCharacterI1 ↔
      spinCentralKernelCharacterContinuousH1ToReal χ = 0 ∧
        ∀ (p : ℕ) [Fact p.Prime],
          spinCentralKernelCharacterContinuousH1ToPadic p χ = 0 := by
  constructor
  · intro hχ
    change spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ χ ∈
      rationalMuTwoContinuousH1LocalGlobalKernel at hχ
    constructor
    · apply (spinCentralKernelCharacterContinuousH1EquivMuTwo ℝ).injective
      rw [spinCentralKernelCharacterContinuousH1ToReal_equiv, map_zero]
      exact hχ.1
    · intro p hp
      apply (spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ_[p]).injective
      rw [spinCentralKernelCharacterContinuousH1ToPadic_equiv, map_zero]
      exact hχ.2 p
  · rintro ⟨hreal, hpadic⟩
    change spinCentralKernelCharacterContinuousH1EquivMuTwo ℚ χ ∈
      rationalMuTwoContinuousH1LocalGlobalKernel
    constructor
    · rw [← spinCentralKernelCharacterContinuousH1ToReal_equiv, hreal, map_zero]
    · intro p hp
      rw [← spinCentralKernelCharacterContinuousH1ToPadic_equiv, hpadic p, map_zero]

/-- Ono's denominator for the specialized central-kernel coefficient is one. -/
theorem natCard_spinCentralKernelCharacterI1_eq_one :
    Nat.card SpinCentralKernelCharacterI1 = 1 := by
  rw [Nat.card_congr spinCentralKernelCharacterI1EquivMuTwo.toEquiv]
  exact natCard_rationalMuTwoContinuousH1LocalGlobalKernel_eq_one

/-- The completed cohomological factor for the actual order-two central
kernel is `h^0 / i^1 = 2`. -/
theorem spinCentralKernelCharacter_h0_div_i1_eq_two :
    (Nat.card (SpinCentralKernelCharacterFixedPart ℚ) : ℚ) /
        Nat.card SpinCentralKernelCharacterI1 = 2 := by
  rw [natCard_spinCentralKernelCharacterFixedPart_eq_two,
    natCard_spinCentralKernelCharacterI1_eq_one]
  norm_num

end RationalTamagawa

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The specialized Ono coefficient attached to the completed Clifford--Spin
kernel has numerator two and localization denominator one. -/
theorem spinCentralKernelCharacter_cohomological_cards :
    Nat.card (SpinCentralKernelCharacterFixedPart ℚ) = 2 ∧
      Nat.card SpinCentralKernelCharacterI1 = 1 :=
  ⟨natCard_spinCentralKernelCharacterFixedPart_eq_two ℚ,
    natCard_spinCentralKernelCharacterI1_eq_one⟩

end RationalQuadraticSpaceMatrix
