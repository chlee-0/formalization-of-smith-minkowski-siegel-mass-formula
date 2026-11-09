import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierRegularity

/-!
# Coherent finite-adelic presentation weight comparison

The global finite-Haar scalar comparison is restricted to the genuine overlap
cylinders and compared with their two coherent weighted descriptions.  The
unweighted cylinder transport supplies the finite product of local reciprocal
determinant norms.  Cancellation is performed only on a compact subset of
positive finite ambient Haar mass.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance coherentWeightComparisonFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance coherentWeightComparisonFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- Exact comparison forced by the coherent block normalizations.  This is
the scalar relation that must be combined with an arithmetic comparison of
the two explicit weights before the global finite factor can be evaluated. -/
theorem coherentRestrictedBlockWeight_mul_modulus_eq_finiteHaarScalar_mul
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight S *
        (P.finiteExceptionalPadicPresentationModulus S hx : ℝ≥0∞) =
      (P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S := by
  let F := P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
  let μB := P.transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS
  let μA := P.ambientFiniteAdelicPresentationOverlapCylinderMeasure hx hS
  let HB := (P.blockSpace hx).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let HA := V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let B := P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S
  let A := P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S
  let wB := (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let wA := V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let q : ℝ≥0∞ := P.finiteExceptionalPadicPresentationModulus S hx
  let c : ℝ≥0∞ := P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx
  have hB : HB.restrict B = wB • μB :=
    P.blockFiniteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_presentationOverlap
      hx hS
  have hA : HA.restrict A = wA • μA :=
    P.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_presentationOverlap
      hx hS
  have hglobal : Measure.map F (HB.restrict B) = c • HA.restrict A :=
    P.map_blockFiniteHaar_restrict_presentationOverlap hx hS
  have hunweighted : Measure.map F μB = q • μA :=
    P.map_transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS
  have hmeasure : (wB * q) • μA = (c * wA) • μA := by
    calc
      (wB * q) • μA = wB • (q • μA) := by rw [smul_smul]
      _ = wB • Measure.map F μB := by rw [hunweighted]
      _ = Measure.map F (wB • μB) := by rw [Measure.map_smul]
      _ = Measure.map F (HB.restrict B) := by rw [hB]
      _ = c • HA.restrict A := hglobal
      _ = c • (wA • μA) := by rw [hA]
      _ = (c * wA) • μA := by rw [smul_smul]
  obtain ⟨K, hKmeas, hKA, hHK0, hHKtop⟩ :=
    P.exists_subset_ambientPresentationOverlap_measure_ne_zero_ne_top hx S
  have hrestrict : (HA.restrict A) K = HA K := by
    rw [Measure.restrict_apply hKmeas, Set.inter_eq_left.mpr hKA]
  have hAat := congrArg (fun ρ : Measure V.FiniteAdelicCliffordGeneralSpinGroup ↦ ρ K) hA
  change (HA.restrict A) K = wA * μA K at hAat
  rw [hrestrict] at hAat
  have hwA0 : wA ≠ 0 :=
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_zero S
  have hμA0 : μA K ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hAat
    exact hHK0 hAat
  have hμAtop : μA K ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hwA0] at hAat
    exact hHKtop hAat
  have hmass := congrArg
    (fun ρ : Measure V.FiniteAdelicCliffordGeneralSpinGroup ↦ ρ K) hmeasure
  change (wB * q) * μA K = (c * wA) * μA K at hmass
  apply (ENNReal.mul_right_inj hμA0 hμAtop).mp
  simpa only [mul_comm] using hmass

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
