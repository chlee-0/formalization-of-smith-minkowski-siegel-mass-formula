import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTargetRecovery
import SMSFormula.RationalCliffordGeneralSpinLocalDifferentialChartMeasure

/-!
# P-adic presentation factor for the glued special-orthogonal measure

The canonical Cayley target calculation determines the presentation factor
of the repository's globally glued invariant-differential `SO(ℚ_p)` measure.
Haar uniqueness supplies only an unnamed comparison scalar; restriction to
the exact identity Cayley target and the already computed tangent Jacobian
evaluate that scalar as the reciprocal p-adic norm of the rational modulus.

No selected general-Spin chart or finite cylinder is transported here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace MeasureTheory.Measure

/-- Two nonnegative real scalars multiplying the same measure are equal as
soon as that measure has one nonzero finite measurable value. -/
private theorem nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (c d : ℝ≥0)
    (h0 : μ K ≠ 0) (htop : μ K ≠ ∞)
    (h : (d : ℝ≥0∞) • μ = (c : ℝ≥0∞) • μ) :
    d = c := by
  have hmass := congrArg (fun ρ : Measure X ↦ ρ K) h
  change (d : ℝ≥0∞) * μ K = (c : ℝ≥0∞) * μ K at hmass
  apply ENNReal.coe_injective
  apply (ENNReal.mul_right_inj h0 htop).mp
  simpa only [mul_comm] using hmass

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance padicGroupHaarFactorGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicGroupHaarFactorGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- On the exact ambient identity Cayley target, the presentation pushforward
of the full block group measure already has the reciprocal local modulus. -/
theorem restrict_map_blockToAmbientPadicInvariantDifferentialGroupMeasure_identityTarget
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (Measure.map
      (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p])
      ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p)).restrict
        (padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        (V.padicInvariantDifferentialGroupMeasure p).restrict
          (padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p) := by
  let E := P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]
  let μ := (P.blockSpace hx).padicInvariantDifferentialGroupMeasure p
  let ν := V.padicInvariantDifferentialGroupMeasure p
  let U := padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  let c : ℝ≥0 :=
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  let μtarget := (P.blockSpace hx)
    |>.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p
  let νtarget := V.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p
  let Etarget := P.blockToAmbientPadicCayleyIdentityTargetHomeomorph hx p
  exact Measure.restrict_map_eq_smul_restrict_of_map_subtype_of_mem_iff
    (isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain
      (P.blockSpace hx).pairingMatrix p).measurableSet
    (isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain
      V.pairingMatrix p).measurableSet
    E E.measurable Etarget.toMeasurableEquiv μ ν μtarget νtarget c
    ((P.blockSpace hx)
      |>.map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_subtypeVal p)
    (V.map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_subtypeVal p)
    (P.map_blockToAmbientPadicCayleyIdentityTargetDifferentialMeasure hx p)
    (fun _ ↦ rfl)
    (fun g ↦ P.blockToAmbientPadicCayleyIdentityTarget_iff hx p g)

set_option backward.isDefEq.respectTransparency false in
/-- The fixed p-adic invariant-differential group measure transforms by the
reciprocal local norm of the rational presentation tangent determinant. -/
theorem map_blockToAmbientPadicInvariantDifferentialGroupMeasure_fin_add_one_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p])
        ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        V.padicInvariantDifferentialGroupMeasure p := by
  let E := P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]
  let μ := (P.blockSpace hx).padicInvariantDifferentialGroupMeasure p
  let ν := V.padicInvariantDifferentialGroupMeasure p
  let U := padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  let c : ℝ≥0 :=
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  letI : Measure.IsHaarMeasure μ :=
    (P.blockSpace hx).padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  have hmapHaar : Measure.IsHaarMeasure (Measure.map E μ) :=
    E.toMulEquiv.isHaarMeasure_map μ E.continuous E.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map E μ) := hmapHaar
  letI : Measure.IsHaarMeasure ν :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  let d : ℝ≥0 := Measure.haarScalarFactor (Measure.map E μ) ν
  have hglobal : Measure.map E μ = d • ν :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map E μ) ν
  have hlocal : (Measure.map E μ).restrict U = c • ν.restrict U := by
    exact P.restrict_map_blockToAmbientPadicInvariantDifferentialGroupMeasure_identityTarget hx p
  have hdMeasure : (d : ℝ≥0∞) • ν.restrict U =
      (c : ℝ≥0∞) • ν.restrict U := by
    have hr := congrArg (fun ρ : Measure (V.specialOrthogonalMatrixGroup ℚ_[p]) ↦
      ρ.restrict U) hglobal
    change (Measure.map E μ).restrict U = (d • ν).restrict U at hr
    rw [Measure.restrict_smul] at hr
    exact hr.symm.trans hlocal
  have hU : IsOpen U :=
    isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  have hone : (1 : V.specialOrthogonalMatrixGroup ℚ_[p]) ∈ U :=
    one_mem_padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_locallyCompact
      p (m + 1) V.pairingMatrix V.form_det_ne_zero
  obtain ⟨K, hK, honeK, hKU⟩ := exists_compact_subset hU hone
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hν0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨1, honeK⟩).ne'
  have hνtop : ν K ≠ ∞ := hK.measure_ne_top
  have hrestrict : (ν.restrict U) K = ν K := by
    rw [Measure.restrict_apply hKmeas, Set.inter_eq_left.mpr hKU]
  have hdc : d = c :=
    Measure.nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top
      (ν.restrict U) K c d (by simpa only [hrestrict])
      (by simpa only [hrestrict]) hdMeasure
  exact hglobal.trans (by rw [hdc])

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Intrinsic-rank form of the exact p-adic special-orthogonal group-measure
presentation formula. -/
theorem map_blockToAmbientPadicInvariantDifferentialGroupMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p])
        ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        V.padicInvariantDifferentialGroupMeasure p := by
  have hdim := P.dimension_add_one hx
  subst n
  exact P.map_blockToAmbientPadicInvariantDifferentialGroupMeasure_fin_add_one_eq hx p

set_option backward.isDefEq.respectTransparency false in
/-- The crossed `ℚ_pˣ × SO(ℚ_p)` product measure has the same presentation
factor because the supplied presentation leaves the unit coordinate fixed. -/
theorem map_blockToAmbientPadicCentralFiberProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℚ_[p])
        ((P.blockSpace hx)
          |>.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p := by
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
    Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
  letI : SigmaFinite
      ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p (m + 1) (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
      (P.blockSpace hx).form_det_ne_zero
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  have hunit : Measurable (id : ℚ_[p]ˣ → ℚ_[p]ˣ) := measurable_id
  have hso : Measurable
      (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]) :=
    (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).measurable
  change Measure.map
      (Prod.map id
        (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]))
      ((Measure.haar : Measure ℚ_[p]ˣ).prod
        ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p)) = _
  rw [← Measure.map_prod_map _ _ hunit hso, Measure.map_id,
    P.map_blockToAmbientPadicInvariantDifferentialGroupMeasure hx p]
  rw [padicCliffordGeneralSpinHorizontalDifferentialProductMeasure]
  exact Measure.prod_smul_right
    (μ := (Measure.haar : Measure ℚ_[p]ˣ))
    (ν := V.padicInvariantDifferentialGroupMeasure p)
    (((‖algebraMap ℚ ℚ_[p]
      (P.blockToAmbientSkewAdjointDetScalar hx)‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞)

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
