import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralPadicCayleyTransport
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicGroupHaarFactor

/-!
# P-adic SO Haar transport under an arbitrary rational isometry

The canonical identity Cayley square for a supplied same-rank rational
isometry preserves the nonlinear differential density.  Its source and target
measures therefore transform by the reciprocal p-adic norm of the canonical
rational tangent determinant.  Haar uniqueness then extends the calculation
from the literal identity Cayley target to the repository's globally glued
invariant-differential SO measure.

No independently selected Spin chart, integral structure, finite cylinder,
raw certificate, quotient measure, or Tamagawa value is transported here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace MeasureTheory.Measure

/-- Two nonnegative real scalars multiplying the same measure agree when the
measure has one nonzero finite measurable value. -/
private theorem nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top_generalIsometry
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

set_option maxHeartbeats 800000

variable {m : ℕ}
variable (U V : RationalQuadraticSpaceMatrix (m + 1))
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance generalPadicGroupHaarModelMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance generalPadicGroupHaarModelBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance generalPadicGroupHaarGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance generalPadicGroupHaarGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Arbitrary-isometry conjugation preserves the determinant of the Cayley
denominator. -/
theorem det_one_sub_rationalIsometryPadicSkewAdjointLinearEquiv
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource U.pairingMatrix p) :
    Matrix.det
        (1 - (rationalIsometryPadicSkewAdjointLinearEquiv U V e p X.1 :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])) =
      Matrix.det (1 - (X.1 :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])) := by
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])
  let N := (rationalIsometryInverseMatrix U V e).map
    (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryMatrix_mul_inverseMatrix U V e)
  rw [coe_rationalIsometryPadicSkewAdjointLinearEquiv_apply]
  let Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] := X.1
  change Matrix.det (1 - M * Y * N) = Matrix.det (1 - Y)
  have hmat : 1 - M * Y * N = M * (1 - Y) * N := by
    calc
      1 - M * Y * N = M * N - M * Y * N := by rw [hMN]
      _ = M * (1 - Y) * N := by noncomm_ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul]
  have hdetMN := congrArg Matrix.det hMN
  simp only [Matrix.det_mul, Matrix.det_one] at hdetMN
  calc
    M.det * Matrix.det (1 - Y) * N.det =
        (M.det * N.det) * Matrix.det (1 - Y) := by ring
    _ = Matrix.det (1 - Y) := by rw [hdetMN, one_mul]

/-- The reciprocal Cayley differential density is invariant under
arbitrary-isometry conjugation on the exact source. -/
theorem rationalIsometryPadicCayleySourceDifferentialDensityENNReal
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource U.pairingMatrix p) :
    Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p (m + 1) V.pairingMatrix
        (rationalIsometryPadicCayleySourceHomeomorph U V e p X) =
      Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p (m + 1) U.pairingMatrix X := by
  unfold Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
  unfold Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
  unfold Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
  rw [rationalIsometryPadicCayleySourceHomeomorph_apply,
    det_one_sub_rationalIsometryPadicSkewAdjointLinearEquiv]
  have hrank := LinearEquiv.finrank_eq
    (rationalIsometrySkewAdjointLinearEquiv U V e)
  rw [hrank]

/-- The source homeomorphism has the arbitrary-isometry p-adic tangent map as
its underlying function. -/
theorem rationalIsometryPadicCayleySourceHomeomorph_val
    (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ∘ rationalIsometryPadicCayleySourceHomeomorph U V e p =
      rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p ∘
        Subtype.val := by
  funext X
  exact rationalIsometryPadicCayleySourceHomeomorph_apply U V e p X

/-- The fixed coordinate measure on the exact p-adic Cayley source transforms
by the reciprocal norm of the canonical rational tangent modulus. -/
theorem map_rationalIsometryPadicCayleySourceCoordinateSubtypeMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (rationalIsometryPadicCayleySourceHomeomorph U V e p)
        (Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p (m + 1) U.pairingMatrix) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p (m + 1) V.pairingMatrix := by
  apply Measure.map_comap_subtype_of_map_smul_of_mem_iff
    (Matrix.isOpen_skewAdjointPadicCayleySource
      U.pairingMatrix p).measurableSet
    (Matrix.isOpen_skewAdjointPadicCayleySource
      V.pairingMatrix p).measurableSet
    (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p)
    (rationalIsometryPadicSkewAdjointContinuousLinearEquiv
      U V e p).continuous.measurable
    (rationalIsometryPadicCayleySourceHomeomorph U V e p).toMeasurableEquiv
    (rationalIsometryPadicCayleySourceHomeomorph_val U V e p)
    (Matrix.skewAdjointPadicCoordinateMeasure U.pairingMatrix p)
    (Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p)
    ‖algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
    (map_rationalIsometryPadicSkewAdjointCoordinateMeasure U V e p)
  intro X
  exact rationalIsometryPadicCayleySource_iff U V e p X

/-- The nonlinear p-adic Cayley source differential measure transforms by
the same reciprocal local tangent modulus. -/
theorem map_rationalIsometryPadicCayleySourceDifferentialSubtypeMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (rationalIsometryPadicCayleySourceHomeomorph U V e p)
        (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p (m + 1) U.pairingMatrix) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p (m + 1) V.pairingMatrix := by
  let E := rationalIsometryPadicCayleySourceHomeomorph U V e p
  let μ := Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    p (m + 1) U.pairingMatrix
  let ν := Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    p (m + 1) V.pairingMatrix
  let dU := Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
    p (m + 1) U.pairingMatrix
  let dV := Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
    p (m + 1) V.pairingMatrix
  let c := ‖algebraMap ℚ ℚ_[p]
    (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
  have hdV : Measurable dV :=
    Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p (m + 1) V.pairingMatrix
  have hdensity : dU = dV ∘ E := by
    funext X
    exact (rationalIsometryPadicCayleySourceDifferentialDensityENNReal
      U V e p X).symm
  change Measure.map E (μ.withDensity dU) = c • ν.withDensity dV
  calc
    Measure.map E (μ.withDensity dU) =
        Measure.map E (μ.withDensity (dV ∘ E)) := by rw [hdensity]
    _ = (Measure.map E μ).withDensity dV :=
      PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable
        E μ dV E.measurable hdV
    _ = (c • ν).withDensity dV := by
      rw [map_rationalIsometryPadicCayleySourceCoordinateSubtypeMeasure]
    _ = c • ν.withDensity dV := by
      ext s hs
      rw [withDensity_apply _ hs, Measure.coe_nnreal_smul_apply,
        withDensity_apply _ hs, Measure.restrict_smul,
        lintegral_smul_measure]
      rfl

/-- The arbitrary-isometry map on identity Cayley targets transports the
fixed target differential measure by the reciprocal local tangent modulus. -/
theorem map_rationalIsometryPadicCayleyIdentityTargetDifferentialMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (rationalIsometryPadicCayleyIdentityTargetHomeomorph U V e p)
        (U.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        V.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p := by
  unfold padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure
  apply Measure.map_map_eq_smul_map_of_forall_commutes
    (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
      U p)
    (rationalIsometryPadicCayleyIdentityTargetHomeomorph U V e p)
    (rationalIsometryPadicCayleySourceHomeomorph U V e p)
    (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
      V p)
    (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
      U p).measurable
    (rationalIsometryPadicCayleyIdentityTargetHomeomorph U V e p).measurable
    (rationalIsometryPadicCayleySourceHomeomorph U V e p).measurable
    (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
      V p).measurable
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p (m + 1) U.pairingMatrix)
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p (m + 1) V.pairingMatrix)
    ‖algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
  · intro X
    exact rationalIsometryPadicCayleyIdentityHomeomorph_commutes U V e p X
  · exact map_rationalIsometryPadicCayleySourceDifferentialSubtypeMeasure
      U V e p

/-- On the exact target identity neighborhood, the pushforward of the full
source group measure already has the reciprocal local tangent modulus. -/
theorem restrict_map_rationalIsometryPadicInvariantDifferentialGroupMeasure_identityTarget
    (p : ℕ) [Fact (Nat.Prime p)] :
    (Measure.map
      (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e ℚ_[p])
      (U.padicInvariantDifferentialGroupMeasure p)).restrict
        (padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        (V.padicInvariantDifferentialGroupMeasure p).restrict
          (padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p) := by
  let E := rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
    U V e ℚ_[p]
  let μ := U.padicInvariantDifferentialGroupMeasure p
  let ν := V.padicInvariantDifferentialGroupMeasure p
  let source := padicCayleySpecialOrthogonalSubgroupInverseDomain U.pairingMatrix p
  let target := padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  let c : ℝ≥0 := ‖algebraMap ℚ ℚ_[p]
    (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
  let μtarget := U.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p
  let νtarget := V.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p
  let Etarget := rationalIsometryPadicCayleyIdentityTargetHomeomorph U V e p
  exact Measure.restrict_map_eq_smul_restrict_of_map_subtype_of_mem_iff
    (isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain
      U.pairingMatrix p).measurableSet
    (isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain
      V.pairingMatrix p).measurableSet
    E E.measurable Etarget.toMeasurableEquiv μ ν μtarget νtarget c
    (U.map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_subtypeVal p)
    (V.map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_subtypeVal p)
    (map_rationalIsometryPadicCayleyIdentityTargetDifferentialMeasure U V e p)
    (fun _ ↦ rfl)
    (fun g ↦ rationalIsometryPadicCayleyIdentityTarget_iff U V e p g)

set_option backward.isDefEq.respectTransparency false in
/-- The repository's glued p-adic invariant-differential SO measure
transforms by the reciprocal p-adic norm of the canonical rational tangent
modulus. -/
theorem map_rationalIsometryPadicInvariantDifferentialGroupMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e ℚ_[p])
        (U.padicInvariantDifferentialGroupMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹ •
        V.padicInvariantDifferentialGroupMeasure p := by
  let E := rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
    U V e ℚ_[p]
  let μ := U.padicInvariantDifferentialGroupMeasure p
  let ν := V.padicInvariantDifferentialGroupMeasure p
  let target := padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  let c : ℝ≥0 := ‖algebraMap ℚ ℚ_[p]
    (rationalIsometrySkewAdjointDetScalar U V e)‖₊⁻¹
  letI : Measure.IsHaarMeasure μ :=
    U.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  have hmapHaar : Measure.IsHaarMeasure (Measure.map E μ) :=
    E.toMulEquiv.isHaarMeasure_map μ E.continuous E.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map E μ) := hmapHaar
  letI : Measure.IsHaarMeasure ν :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  let d : ℝ≥0 := Measure.haarScalarFactor (Measure.map E μ) ν
  have hglobal : Measure.map E μ = d • ν :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map E μ) ν
  have hlocal : (Measure.map E μ).restrict target = c • ν.restrict target :=
    restrict_map_rationalIsometryPadicInvariantDifferentialGroupMeasure_identityTarget
      U V e p
  have hdMeasure : (d : ℝ≥0∞) • ν.restrict target =
      (c : ℝ≥0∞) • ν.restrict target := by
    have hr := congrArg
      (fun ρ : Measure (V.specialOrthogonalMatrixGroup ℚ_[p]) ↦
        ρ.restrict target) hglobal
    change (Measure.map E μ).restrict target = (d • ν).restrict target at hr
    rw [Measure.restrict_smul] at hr
    exact hr.symm.trans hlocal
  have htarget : IsOpen target :=
    isOpen_padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  have hone : (1 : V.specialOrthogonalMatrixGroup ℚ_[p]) ∈ target :=
    one_mem_padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_locallyCompact
      p (m + 1) V.pairingMatrix V.form_det_ne_zero
  obtain ⟨K, hK, honeK, hKtarget⟩ := exists_compact_subset htarget hone
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hν0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨1, honeK⟩).ne'
  have hνtop : ν K ≠ ∞ := hK.measure_ne_top
  have hrestrict : (ν.restrict target) K = ν K := by
    rw [Measure.restrict_apply hKmeas, Set.inter_eq_left.mpr hKtarget]
  have hdc : d = c :=
    Measure.nnreal_eq_of_smul_eq_smul_of_apply_ne_zero_ne_top_generalIsometry
      (ν.restrict target) K c d (by simpa only [hrestrict])
      (by simpa only [hrestrict]) hdMeasure
  exact hglobal.trans (by rw [hdc])

end RationalQuadraticSpaceMatrix

end
