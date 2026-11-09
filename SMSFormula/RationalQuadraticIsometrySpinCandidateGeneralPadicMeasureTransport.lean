import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralPadicGroupHaar
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction

/-!
# P-adic Spin Haar transport under an arbitrary rational isometry

The arbitrary-isometry Spin equivalence commutes with the represented SO map.
The certified p-adic SO modulus therefore determines the Spin modulus through
the existing two-sheet pushforward identities and Haar uniqueness.

No Spin chart is transported or selected, and no integral structure, finite
cylinder, raw certificate, quotient measure, or Tamagawa value is asserted.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

variable {m : ℕ}
variable (U V : RationalQuadraticSpaceMatrix (m + 1))
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

/-- The represented SO image of Spin pulls back to the source image under
the arbitrary-isometry SO equivalence. -/
theorem preimage_rationalIsometrySpinCandidate_specialOrthogonal_range
    (A : Type*) [Field A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e A ⁻¹'
        ((V.cliffordSpinCandidateGroupToSpecialOrthogonal A).range : Set _) =
      ((U.cliffordSpinCandidateGroupToSpecialOrthogonal A).range : Set _) := by
  ext g
  constructor
  · rintro ⟨t, ht⟩
    let s := (rationalIsometrySpinCandidateMulEquiv U V e A).symm t
    refine ⟨s, ?_⟩
    apply (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e A).injective
    rw [rationalIsometrySpinCandidate_specialOrthogonal_commutes]
    simpa [s] using ht
  · rintro ⟨s, rfl⟩
    exact ⟨rationalIsometrySpinCandidateMulEquiv U V e A s,
      (rationalIsometrySpinCandidate_specialOrthogonal_commutes
        U V e A s).symm⟩

private theorem nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
    {Y : Type*} [MeasurableSpace Y]
    (ρ : Measure Y) (K : Set Y) (c d : NNReal)
    (h0 : ρ K ≠ 0) (htop : ρ K ≠ ⊤)
    (h : (d : ENNReal) • ρ = (c : ENNReal) • ρ) :
    d = c := by
  have hmass := congrArg (fun η : Measure Y ↦ η K) h
  change (d : ENNReal) * ρ K = (c : ENNReal) * ρ K at hmass
  apply ENNReal.coe_injective
  apply (ENNReal.mul_right_inj h0 htop).mp
  simpa only [mul_comm] using hmass

local instance sourcePadicSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (U.PadicCliffordSpinCandidateGroup p) := borel _

local instance sourcePadicSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (U.PadicCliffordSpinCandidateGroup p) := ⟨rfl⟩

local instance targetPadicSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.PadicCliffordSpinCandidateGroup p) := borel _

local instance targetPadicSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.PadicCliffordSpinCandidateGroup p) := ⟨rfl⟩

local instance sourcePadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (U.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

local instance sourcePadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (U.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

local instance targetPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

local instance targetPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

local instance sourcePadicInvariantSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

local instance sourcePadicInvariantSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

local instance targetPadicInvariantSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

local instance targetPadicInvariantSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The existing p-adic chart-glued Spin measures transform by the reciprocal
local norm of the canonical arbitrary-isometry tangent modulus. -/
theorem map_rationalIsometryPadicCliffordSpinCandidateChartGluedMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (rationalIsometrySpinCandidateContinuousMulEquiv
        U V e ℚ_[p])
        (U.padicCliffordSpinCandidateChartGluedMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        V.padicCliffordSpinCandidateChartGluedMeasure p := by
  let E := rationalIsometrySpinCandidateContinuousMulEquiv U V e ℚ_[p]
  let F := rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
    U V e ℚ_[p]
  let f := U.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
  let g := V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
  let μU := U.padicCliffordSpinCandidateChartGluedMeasure p
  let μV := V.padicCliffordSpinCandidateChartGluedMeasure p
  let νU := U.padicInvariantDifferentialGroupMeasure p
  let νV := V.padicInvariantDifferentialGroupMeasure p
  let SU := (f.range : Set (U.specialOrthogonalMatrixGroup ℚ_[p]))
  let SV := (g.range : Set (V.specialOrthogonalMatrixGroup ℚ_[p]))
  let c : NNReal := ‖algebraMap ℚ ℚ_[p]
    (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
  have hSV : MeasurableSet SV :=
    (V.isOpen_padicCliffordSpinCandidateImage p).measurableSet
  have hsquare : g ∘ E = F ∘ f := by
    funext s
    exact (rationalIsometrySpinCandidate_specialOrthogonal_commutes
      U V e ℚ_[p] s).symm
  have hpre : F ⁻¹' SV = SU :=
    preimage_rationalIsometrySpinCandidate_specialOrthogonal_range
      U V e ℚ_[p]
  have hμU : Measure.map f μU = (2 : ENNReal) • νU.restrict SU := by
    exact U.map_padicCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image p
  have hμV : Measure.map g μV = (2 : ENNReal) • νV.restrict SV := by
    exact V.map_padicCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image p
  have hν : Measure.map F νU = (c : ENNReal) • νV := by
    dsimp only [F, νU, νV, c]
    exact map_rationalIsometryPadicInvariantDifferentialGroupMeasure U V e p
  have hrestrict : Measure.map F (νU.restrict SU) =
      (c : ENNReal) • νV.restrict SV := by
    have hr := Measure.restrict_map (μ := νU) F.measurable hSV
    change (Measure.map F νU).restrict SV =
      Measure.map F (νU.restrict (F ⁻¹' SV)) at hr
    rw [hpre] at hr
    rw [← hr, hν, Measure.restrict_smul]
  have hpushC : Measure.map g (Measure.map E μU) =
      (c : ENNReal) • Measure.map g μV := by
    calc
      Measure.map g (Measure.map E μU) =
          Measure.map (g ∘ E) μU := Measure.map_map
            (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal
              ℚ_[p]).measurable E.measurable
      _ = Measure.map (F ∘ f) μU := by rw [hsquare]
      _ = Measure.map F (Measure.map f μU) :=
        (Measure.map_map F.measurable
          (U.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal
            ℚ_[p]).measurable).symm
      _ = Measure.map F ((2 : ENNReal) • νU.restrict SU) := by rw [hμU]
      _ = (2 : ENNReal) • Measure.map F (νU.restrict SU) := by
        rw [Measure.map_smul]
      _ = (2 : ENNReal) • ((c : ENNReal) • νV.restrict SV) := by rw [hrestrict]
      _ = (c : ENNReal) • ((2 : ENNReal) • νV.restrict SV) := by
        rw [smul_smul, smul_smul, mul_comm (2 : ENNReal) c]
      _ = (c : ENNReal) • Measure.map g μV := by rw [hμV]
  letI : Measure.IsHaarMeasure μU :=
    U.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  letI : Measure.IsHaarMeasure μV :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  have hmapHaar : Measure.IsHaarMeasure (Measure.map E μU) :=
    E.toMulEquiv.isHaarMeasure_map μU E.continuous E.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map E μU) := hmapHaar
  let d : NNReal := Measure.haarScalarFactor (Measure.map E μU) μV
  have hglobal : Measure.map E μU = (d : ENNReal) • μV :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map E μU) μV
  have hpushD : Measure.map g (Measure.map E μU) =
      (d : ENNReal) • Measure.map g μV := by
    rw [hglobal, Measure.map_smul]
  have hdcMeasure : (d : ENNReal) • Measure.map g μV =
      (c : ENNReal) • Measure.map g μV := hpushD.symm.trans hpushC
  have hSVopen : IsOpen SV := V.isOpen_padicCliffordSpinCandidateImage p
  have hone : (1 : V.specialOrthogonalMatrixGroup ℚ_[p]) ∈ SV := by
    exact ⟨1, map_one g⟩
  obtain ⟨K, hK, honeK, hKSV⟩ := exists_compact_subset hSVopen hone
  letI : Measure.IsHaarMeasure νV :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  have hνV0 : νV K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior νV ⟨1, honeK⟩).ne'
  have hνVtop : νV K ≠ ⊤ := hK.measure_ne_top
  have hρK : (Measure.map g μV) K = 2 * νV K := by
    rw [hμV]
    change (2 : ENNReal) * (νV.restrict SV) K = 2 * νV K
    congr 1
    rw [Measure.restrict_apply (μ := νV) (s := SV) (t := K)
        hK.measurableSet,
      Set.inter_eq_left.mpr hKSV]
  have hρ0 : (Measure.map g μV) K ≠ 0 := by
    rw [hρK]
    exact mul_ne_zero (by norm_num) hνV0
  have hρtop : (Measure.map g μV) K ≠ ⊤ := by
    rw [hρK]
    exact ENNReal.mul_ne_top (by norm_num) hνVtop
  have hdc : d = c :=
    nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
      (Measure.map g μV) K c d hρ0 hρtop hdcMeasure
  rw [hdc] at hglobal
  change Measure.map E μU = (c : ENNReal) • μV
  exact hglobal

end RationalQuadraticSpaceMatrix

end
