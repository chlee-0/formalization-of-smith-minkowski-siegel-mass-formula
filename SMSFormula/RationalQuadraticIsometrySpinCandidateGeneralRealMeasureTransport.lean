import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRealGroupHaar
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction

/-!
# Real Spin Haar transport under an arbitrary rational isometry

The arbitrary-isometry Spin-to-SO square and the exact real SO modulus identify
the Haar scalar on the existing chart-glued Spin measures.  The scalar is
forced after pushforward through the two-sheet Spin map and cancellation on a
compact positive finite patch inside its open image.

No Spin or SO chart is transported or selected.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped Matrix ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

private theorem nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
    {Y : Type*} [MeasurableSpace Y]
    (rho : Measure Y) (K : Set Y) (c d : NNReal)
    (h0 : rho K ≠ 0) (htop : rho K ≠ ⊤)
    (h : (d : ENNReal) • rho = (c : ENNReal) • rho) :
    d = c := by
  have hmass := congrArg (fun eta : Measure Y => eta K) h
  change (d : ENNReal) * rho K = (c : ENNReal) * rho K at hmass
  apply ENNReal.coe_injective
  apply (ENNReal.mul_right_inj h0 htop).mp
  simpa only [mul_comm] using hmass

section SameRank

variable {n : ℕ}
variable (U V : RationalQuadraticSpaceMatrix n)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance realSpinMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace W.RealCliffordSpinCandidateGroup := borel _

local instance realSpinBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace W.RealCliffordSpinCandidateGroup := ⟨rfl⟩

local instance realInvariantSOMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (W.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

local instance realInvariantSOBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (W.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

local instance realSchemeSOMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (W.specialOrthogonalMatrixGroup ℝ) := borel _

local instance realSchemeSOBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace (W.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- In equal native dimensions, arbitrary rational-isometry Spin transport
has the reciprocal archimedean norm of the canonical rational tangent
determinant. -/
theorem map_rationalIsometryRealCliffordSpinCandidateChartGluedMeasure_sameRank :
    Measure.map (rationalIsometrySpinCandidateContinuousMulEquiv U V e ℝ)
        U.realCliffordSpinCandidateChartGluedMeasure =
      (Real.toNNReal
        |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)|)⁻¹ •
        V.realCliffordSpinCandidateChartGluedMeasure := by
  let E := rationalIsometrySpinCandidateContinuousMulEquiv U V e ℝ
  let F := (rationalIsometryRealFormCongruenceData U V e).groupEquiv
  let f := U.realCliffordSpinCandidateToSpecialOrthogonalHom
  let g := V.realCliffordSpinCandidateToSpecialOrthogonalHom
  let mu1 := U.realCliffordSpinCandidateChartGluedMeasure
  let mu2 := V.realCliffordSpinCandidateChartGluedMeasure
  let nu1 := U.realInvariantDifferentialGroupMeasure
  let nu2 := V.realInvariantDifferentialGroupMeasure
  let S1 : Set U.RealSpecialOrthogonalGroup :=
    {q | ∃ z : U.CliffordSpinCandidateGroup ℝ, f z = q}
  let S2 : Set V.RealSpecialOrthogonalGroup :=
    {q | ∃ z : V.CliffordSpinCandidateGroup ℝ, g z = q}
  let c : NNReal :=
    (Real.toNNReal
      |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)|)⁻¹
  have hS2 : MeasurableSet S2 :=
    V.isOpen_realCliffordSpinCandidateImage.measurableSet
  have hsquare : g ∘ E = F ∘ f := by
    funext z
    exact (rationalIsometrySpinCandidate_realSpecialOrthogonal_commutes
      U V e z).symm
  have hpre : F ⁻¹' S2 = S1 := by
    exact preimage_rationalIsometrySpinCandidate_realSpecialOrthogonal_range
      U V e
  have hmu1 : Measure.map f mu1 = (2 : ENNReal) • nu1.restrict S1 := by
    exact U.map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image
  have hmu2 : Measure.map g mu2 = (2 : ENNReal) • nu2.restrict S2 := by
    exact V.map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image
  have hnu : Measure.map F nu1 = (c : ENNReal) • nu2 := by
    dsimp only [F, nu1, nu2, c]
    exact map_rationalIsometryRealInvariantDifferentialGroupMeasure U V e
  have hrestrict : Measure.map F (nu1.restrict S1) =
      (c : ENNReal) • nu2.restrict S2 := by
    have hr := Measure.restrict_map (μ := nu1) F.measurable hS2
    change (Measure.map F nu1).restrict S2 =
      Measure.map F (nu1.restrict (F ⁻¹' S2)) at hr
    rw [hpre] at hr
    rw [← hr, hnu, Measure.restrict_smul]
  have hpushC : Measure.map g (Measure.map E mu1) =
      (c : ENNReal) • Measure.map g mu2 := by
    calc
      Measure.map g (Measure.map E mu1) =
          Measure.map (g ∘ E) mu1 := Measure.map_map
            (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).measurable
            E.measurable
      _ = Measure.map (F ∘ f) mu1 := by rw [hsquare]
      _ = Measure.map F (Measure.map f mu1) :=
        (Measure.map_map F.measurable
          (U.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).measurable).symm
      _ = Measure.map F ((2 : ENNReal) • nu1.restrict S1) := by rw [hmu1]
      _ = (2 : ENNReal) • Measure.map F (nu1.restrict S1) := by
        rw [Measure.map_smul]
      _ = (2 : ENNReal) • ((c : ENNReal) • nu2.restrict S2) := by
        rw [hrestrict]
      _ = (c : ENNReal) • ((2 : ENNReal) • nu2.restrict S2) := by
        rw [smul_smul, smul_smul, mul_comm (2 : ENNReal) c]
      _ = (c : ENNReal) • Measure.map g mu2 := by rw [hmu2]
  letI : Measure.IsHaarMeasure mu1 :=
    U.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure mu2 :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  have hmapHaar : Measure.IsHaarMeasure (Measure.map E mu1) :=
    E.toMulEquiv.isHaarMeasure_map mu1 E.continuous E.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map E mu1) := hmapHaar
  let d : NNReal := Measure.haarScalarFactor (Measure.map E mu1) mu2
  have hglobal : Measure.map E mu1 = (d : ENNReal) • mu2 :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hpushD : Measure.map g (Measure.map E mu1) =
      (d : ENNReal) • Measure.map g mu2 := by
    rw [hglobal, Measure.map_smul]
  have hdcMeasure : (d : ENNReal) • Measure.map g mu2 =
      (c : ENNReal) • Measure.map g mu2 := hpushD.symm.trans hpushC
  have hS2open : IsOpen S2 := V.isOpen_realCliffordSpinCandidateImage
  have hone : (1 : V.specialOrthogonalMatrixGroup ℝ) ∈ S2 := by
    exact ⟨1, map_one g⟩
  obtain ⟨K, hK, honeK, hKS2⟩ := exists_compact_subset hS2open hone
  letI : Measure.IsHaarMeasure nu2 :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  have hnu20 : nu2 K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior nu2 ⟨1, honeK⟩).ne'
  have hnu2top : nu2 K ≠ ⊤ := hK.measure_ne_top
  have hrhoK : (Measure.map g mu2) K = 2 * nu2 K := by
    rw [hmu2]
    change (2 : ENNReal) * (nu2.restrict S2) K = 2 * nu2 K
    congr 1
    rw [Measure.restrict_apply (μ := nu2) (s := S2) (t := K)
        hK.measurableSet,
      Set.inter_eq_left.mpr hKS2]
  have hrho0 : (Measure.map g mu2) K ≠ 0 := by
    rw [hrhoK]
    exact mul_ne_zero (by norm_num) hnu20
  have hrhotop : (Measure.map g mu2) K ≠ ⊤ := by
    rw [hrhoK]
    exact ENNReal.mul_ne_top (by norm_num) hnu2top
  have hdc : d = c :=
    nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
      (Measure.map g mu2) K c d hrho0 hrhotop hdcMeasure
  rw [hdc] at hglobal
  change Measure.map E mu1 = (c : ENNReal) • mu2
  exact hglobal

end SameRank

section ArbitraryRank

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

/-- Real Spin Haar transport for a supplied rational quadratic isometry
between its original native carriers. -/
theorem map_rationalIsometryRealCliffordSpinCandidateChartGluedMeasure :
    Measure.map (rationalIsometrySpinCandidateContinuousMulEquiv U V e ℝ)
        U.realCliffordSpinCandidateChartGluedMeasure =
      (Real.toNNReal
        |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)|)⁻¹ •
        V.realCliffordSpinCandidateChartGluedMeasure := by
  have hdim := rationalIsometry_dimension_eq U V e
  subst s
  exact map_rationalIsometryRealCliffordSpinCandidateChartGluedMeasure_sameRank
    U V e

end ArbitraryRank

end RationalQuadraticSpaceMatrix

end
