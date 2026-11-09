import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierSource

/-!
# Finite-adelic presentation overlap carrier images

The native block and ambient overlap-cylinder carriers are the ranges of the
two maps from the common source.  The already certified commuting square then
identifies their image and inverse image under presentation transport.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierImageDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance overlapCarrierImagePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem blockFiniteAdelicPresentationOverlapCylinderCarrier_eq_range
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S =
      Set.range (P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨g, rfl⟩ :=
      P.exists_blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_preimage
        hx hS z hz
    exact ⟨g, rfl⟩
  · rintro y ⟨g, rfl⟩
    refine ⟨P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g,
      P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_mem_carrier
        hx hS g, rfl⟩

theorem ambientFiniteAdelicPresentationOverlapCylinderCarrier_eq_range
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S =
      Set.range (P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨g, rfl⟩ :=
      P.exists_ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_preimage
        hx hS z hz
    exact ⟨g, rfl⟩
  · rintro y ⟨g, rfl⟩
    refine ⟨P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g,
      P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_mem_carrier
        hx hS g, rfl⟩

theorem image_blockFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx ''
        P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S =
      P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S := by
  rw [P.blockFiniteAdelicPresentationOverlapCylinderCarrier_eq_range hx hS,
    P.ambientFiniteAdelicPresentationOverlapCylinderCarrier_eq_range hx hS]
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS g,
      (P.blockToAmbientFiniteAdelicPresentationOverlapCylinder_commutes hx hS g).symm⟩
  · rintro ⟨g, rfl⟩
    let z := (P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS).symm g
    refine ⟨P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS z,
      ⟨z, rfl⟩, ?_⟩
    rw [P.blockToAmbientFiniteAdelicPresentationOverlapCylinder_commutes hx hS z]
    simp only [z, MeasurableEquiv.apply_symm_apply]

theorem preimage_ambientFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx :
      (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup →
        V.FiniteAdelicCliffordGeneralSpinGroup) ⁻¹'
        P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S =
      P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S := by
  ext g
  constructor
  · intro hg
    rw [← P.image_blockFiniteAdelicPresentationOverlapCylinderCarrier hx hS] at hg
    obtain ⟨z, hz, hzg⟩ := hg
    have hzg' : z = g :=
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).injective hzg
    exact hzg' ▸ hz
  · intro hg
    rw [← P.image_blockFiniteAdelicPresentationOverlapCylinderCarrier hx hS]
    exact ⟨g, hg, rfl⟩

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
