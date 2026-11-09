import SMSFormula.RationalIdeleDifferentialGenuinePrincipalBlockInclusion

/-!
# Open differential rational-idele principal blocks

A genuine `S`-principal block consists of finite ideles whose value and inverse
are integral outside `S`.  This is a literal open restricted-product condition,
so the block inclusion into `RationalFiniteAdeleˣ` is a measurable embedding.

No measure comparison is made here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped RestrictedProduct

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleGenuineBlockOpenPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Finite adeles integral outside a displayed finite set form an open
restricted-product cylinder. -/
theorem isOpen_rationalFiniteAdele_integralOutside
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen {a : RationalFiniteAdele |
      ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers ℚ} := by
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun _v ↦ Valued.isOpen_valuationSubring _)

/-- The literal genuine differential finite-idele principal block is open in
the ambient finite-idele group. -/
theorem isOpen_isRationalIdeleDifferentialGenuinePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen {a : RationalFiniteAdeleˣ |
      IsRationalIdeleDifferentialGenuinePrincipalBlock S a} := by
  let U : Set RationalFiniteAdele :=
    {a | ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers ℚ}
  have hU : IsOpen U := isOpen_rationalFiniteAdele_integralOutside S
  have hopen : IsOpen
      ((fun a : RationalFiniteAdeleˣ ↦ (a : RationalFiniteAdele)) ⁻¹' U ∩
        (fun a : RationalFiniteAdeleˣ ↦
          ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele)) ⁻¹' U) :=
    (hU.preimage Units.continuous_val).inter
      (hU.preimage (Units.continuous_val.comp continuous_inv))
  convert hopen using 1
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, U]
  constructor
  · intro ha
    constructor
    · intro v hv
      have hlocal :=
        (mem_padicIntegralUnitsSubgroup_iff _ _).1 (ha v hv)
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      exact hlocal.1
    · intro v hv
      have hlocal :=
        (mem_padicIntegralUnitsSubgroup_iff _ _).1 (ha v hv)
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      exact hlocal.2
  · rintro ⟨ha, hai⟩ v hv
    rw [mem_padicIntegralUnitsSubgroup_iff]
    constructor
    · change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (a : RationalFiniteAdele) ∈ PadicInt.subring _
      exact (mem_adicCompletionIntegers_iff_padic v _).1 (ha v hv)
    · change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) ∈
          PadicInt.subring _
      exact (mem_adicCompletionIntegers_iff_padic v _).1 (hai v hv)

end RationalQuadraticSpaceMatrix
