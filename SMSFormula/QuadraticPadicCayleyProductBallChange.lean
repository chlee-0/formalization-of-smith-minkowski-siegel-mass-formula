import SMSFormula.UltrametricApproximatesLinearImage
import SMSFormula.QuadraticPadicCayleyProductLocalInverse

/-! Local change of variables on coordinate balls for the actual p-adic
Cayley product. The scalar-extended skew-adjoint bases (lower basis times
coordinate directions on the source, higher basis on the target) identify both
spaces with ultrametric coordinate spaces; closed coordinate balls are the
lattice cosets. There the typed actual product sends every small ball exactly
onto the translated image of the ball under its strict derivative, and the
image has Haar measure (Haar modulus of that derivative) times the ball's.
Haar measures and Borel structures are supplied; no chart, section, baseline or
normalization is chosen, and the modulus is not identified with |det|_p or
with the closed density law. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice Metric
open scoped Matrix.Norms.Operator Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

local instance lastBallLowerSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Submodule.topologicalAddGroup _

local instance lastBallHigherSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Submodule.topologicalAddGroup _

local instance lastBallPiIsUltrametricDist (ι : Type*) [Fintype ι] :
    IsUltrametricDist (ι → ℚ_[p]) := by
  refine ⟨fun f g h => ?_⟩
  apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).mpr
  intro i
  exact (IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)).trans
    (max_le_max (dist_le_pi_dist f g i) (dist_le_pi_dist g h i))

set_option backward.isDefEq.respectTransparency false in
/-- Source coordinates: the scalar-extended lower basis and the standard
coordinate directions. -/
def lastCayleyProductSourceCoordinates :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]) :=
  ((skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix).prod
    (Pi.basisFun ℚ_[p] (Fin n))).equivFun.toContinuousLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Target coordinates: the scalar-extended higher basis. -/
def lastCayleyProductTargetCoordinates :
    skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
        (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]) :=
  (skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
    (W.nonisotropicLastExtension a ha).pairingMatrix).equivFun.toContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

/-- The typed actual product read in source and target coordinates. -/
def lastCayleyProductCoordinateValue
    (u : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]) :
    Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
      (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p] :=
  W.lastCayleyProductTargetCoordinates a ha p
    (W.lastCayleyProductFrameValue a ha p S z v
      ((W.lastCayleyProductSourceCoordinates p).symm u))

/-- The coordinate strict derivative: the closed frame equivalence conjugated by
the coordinate equivalences. -/
def lastCayleyProductCoordinateDerivative :=
  (W.lastCayleyProductSourceCoordinates p).symm.trans
    ((W.lastCayleyProductFrameEquiv a ha p S dS z hS hSO Y hY X hX hproduct v hs hv).trans
      (W.lastCayleyProductTargetCoordinates a ha p))

include hs hv in
/-- The coordinate product is strictly differentiable at the base point with
the conjugated frame equivalence as derivative. -/
theorem hasStrictFDerivAt_lastCayleyProductCoordinateValue :
    HasStrictFDerivAt (W.lastCayleyProductCoordinateValue a ha p S z v)
      ((W.lastCayleyProductCoordinateDerivative a ha p S dS z hS hSO Y hY X hX hproduct v hs hv :
        _ →L[ℚ_[p]] _))
      (W.lastCayleyProductSourceCoordinates p (Y,0)) := by
  have hval := W.hasStrictFDerivAt_lastCayleyProductFrameValue_equiv a ha p S dS z hS hSO Y hY X hX
    hproduct v hs hv
  rw [← (W.lastCayleyProductSourceCoordinates p).symm_apply_apply (Y,0)] at hval
  have h := ((W.lastCayleyProductTargetCoordinates a ha p).hasStrictFDerivAt).comp _
    (hval.comp _ (W.lastCayleyProductSourceCoordinates p).symm.hasStrictFDerivAt)
  exact h

variable [MeasurableSpace
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p])]
    [BorelSpace
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p])]
    [MeasurableSpace (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
      (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
      (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p])]

include hs hv in
/-- Local change of variables on coordinate balls for the actual product:
every closed coordinate ball inside a fixed neighbourhood of the base point
is sent exactly onto the translated derivative image of the ball, and its image
has SUPPLIED-Haar measure equal to the Haar modulus of the coordinate derivative
times the ball's measure. -/
theorem lastCayleyProduct_exists_measure_image_closedBall
    (μ : MeasureTheory.Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure]
    (ν : MeasureTheory.Measure (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
      (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]))
    [ν.IsAddHaarMeasure] [ν.IsAddLeftInvariant] :
    ∃ δ > 0, ∀ (x : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n →
        ℚ_[p]) (ρ : ℝ), closedBall x ρ ⊆ ball (W.lastCayleyProductSourceCoordinates p (Y,0)) δ →
      W.lastCayleyProductCoordinateValue a ha p S z v '' closedBall x ρ =
          (fun u ↦ W.lastCayleyProductCoordinateValue a ha p S z v x +
            W.lastCayleyProductCoordinateDerivative a ha p S dS z hS hSO Y hY X hX hproduct v hs hv u) ''
            closedBall 0 ρ ∧
        ν (W.lastCayleyProductCoordinateValue a ha p S z v '' closedBall x ρ) =
          MeasureTheory.Measure.addHaarScalarFactor
            (ν.map (W.lastCayleyProductCoordinateDerivative a ha p S dS z hS hSO Y hY X hX hproduct v
              hs hv).symm) μ * μ (closedBall x ρ) :=
  (W.hasStrictFDerivAt_lastCayleyProductCoordinateValue a ha p S dS z hS hSO Y hY X hX hproduct v
    hs hv).exists_measure_image_closedBall μ ν

end RationalQuadraticSpaceMatrix
