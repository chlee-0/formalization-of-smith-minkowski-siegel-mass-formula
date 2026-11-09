import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRealFactor
import SMSFormula.RationalCliffordSpinCandidateLatticeCofinalRawBlockScaleComparison
import SMSFormula.RationalCliffordSpinCandidateLatticeRawBlockScaleComparison
import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDifferentialScale
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicGenuineBlockCoherence
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicGenuinePrincipalBlockCarrier
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockCylinderMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDirectedMeasure
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor
import SMSFormula.RationalCliffordSpinCandidateAdelicProduct
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeRefinedPieceRestrictedPushforward
import SMSFormula.RationalPadicUnitSquarePushforward

/-!
# Local Spin conditions in the retained finite GSpin carrier

The retained finite orbital calculation uses the existing p-adic Spin
identity source and the existing integral Spin subgroup.  This file proves
that both are recovered exactly by the intrinsic Spin embedding into
`GSpin`: the identity square branch removes the possible central scalar
`-1`, while integral `GSpin` coordinates on an embedded Spin point are
equivalent to the four families of integral Spin
coordinates.

These are local carrier-identification statements only.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance retainedFiniteLocalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- On the retained p-adic identity square branch, the intrinsic Spin
embedding sees exactly the existing Spin identity-chart source. -/
theorem preimage_cliffordSpinCandidateToCliffordGeneralSpinHom_padicCentralFiberIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] ⁻¹'
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =
      (V.padicCliffordSpinCandidateIdentityChart p).source := by
  ext s
  constructor
  · intro hs
    change V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s ∈
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target at hs
    rcases hs with ⟨q, hq, hqs⟩
    have hsq : q.1 ^ 2 = (1 : ℚ_[p]ˣ) := by
      simpa using congrArg
        (fun z : V.PadicCliffordGeneralSpinGroup p => z.similitude) hqs
    have hcases : q.1 = 1 ∨ q.1 = -1 := by
      apply Rat.eq_one_or_neg_one_of_unitSquareMonoidHom_eq_one p q.1
      simpa [Rat.unitSquareMonoidHom] using hsq
    have hqone : q.1 = 1 := by
      rcases hcases with h | h
      · exact h
      · exfalso
        exact Rat.neg_one_not_mem_unitSquareIdentityChart_source ℚ_[p] (h ▸ hq.1)
    have hspin : q.2 = s := by
      apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective ℚ_[p]
      simpa [RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication,
        hqone] using hqs
    simpa [hspin] using hq.2
  · intro hs
    change V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s ∈
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target
    refine ⟨(1, s), ⟨Rat.one_mem_unitSquareIdentityChart_source ℚ_[p], hs⟩, ?_⟩
    simp [RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication]

/-- Literal integral `GSpin` coordinates on an embedded local Spin point are
equivalent to the existing local Spin integrality predicate. -/
theorem padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (s : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v).1
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s) ↔
      V.HeightOnePadicCliffordSpinCandidateIsIntegral v s := by
  rw [V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic]
  have hpointInv := map_inv
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s
  change V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s⁻¹ =
    (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s)⁻¹ at hpointInv
  have hcliffInv (u : Finset (Fin n)) :
      (V.cliffordCoordinateBaseChangeBasis
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (V.cliffordCoordinateBaseChangeReverse
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).clifford) u =
      s⁻¹ (V.cliffordSpinCandidateCliffordCoordinate u) := by
    rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
    rw [hpointInv, CliffordSpinCandidatePointData.inv_clifford]
  have hmatrixInv (i j : Fin n) :
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).matrixGroup⁻¹.1.1.1 i j =
        s⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) := by
    rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
    change
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).matrixGroup⁻¹.1.1.1 i j =
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s⁻¹).matrixPoint.1 i j
    rw [hpointInv]
    change
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).matrixGroup⁻¹.1.1.1 i j =
        ((V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s)⁻¹).matrixGroup.1.1.1 i j
    rw [CliffordSpinCandidatePointData.inv_matrixGroup]
  have hmatrixPointInv (i j : Fin n) :
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).matrixPoint.1⁻¹ i j =
        s⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) := by
    rw [← CliffordSpinCandidatePointData.matrixGroup_coe]
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact hmatrixInv i j
  unfold PadicCliffordGeneralSpinIsIntegral
  simp [RationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom,
    CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
    CliffordGeneralSpinIntrinsicPoint.ofSpin,
    hcliffInv, hmatrixPointInv]
  aesop

end RationalQuadraticSpaceMatrix

end
