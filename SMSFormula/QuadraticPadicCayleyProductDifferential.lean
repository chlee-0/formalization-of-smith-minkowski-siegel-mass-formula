import SMSFormula.QuadraticPadicCayleyBlockCompatibility

/-! The actual two-variable matrix product and inverse-Cayley coordinate.
The left factor is supplied and differentiable; no section or chart is selected.
This computes derivatives, not injectivity, an inverse or change of variables. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
open scoped Matrix.Norms.Operator Topology RightActions
namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

local instance lastProductSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

/-- The own lower group chart, embedded as actual fixed-last matrices, has
the derivative of the embedded higher chart on the same exact source. -/
theorem hasFDerivAt_lastCayleyLowerMatrix
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    HasFDerivAt
      (fun Z ↦ fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Z))
      ((skewAdjointPadicCayleyForwardDerivative (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)).comp
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap) Y := by
  have hd := (hasFDerivAt_skewAdjointPadicCayleyForwardMatrix
    (W.nonisotropicLastExtension a ha).pairingMatrix p _
    ((W.lastCayley_embedded_source_iff a ha p Y).mpr hY)).comp Y
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap.hasFDerivAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_skewAdjointPadicCayleySource W.pairingMatrix p).mem_nhds hY] with Z hZ
  exact (W.lastCayley_embedded_forward a ha p Z hZ).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]

/-- The product-rule and inverse-Cayley derivative, retaining both variables.
This is a continuous linear map in the ambient matrix coordinates. -/
def lastCayleyProductDerivative
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E) →L[ℚ_[p]]
      Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] :=
  let B := fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y)
  let dB := (skewAdjointPadicCayleyForwardDerivative (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)).comp
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap
  (padicCayleyInverseDerivative p (S * B)).comp
    (S • (dB.comp (ContinuousLinearMap.fst ℚ_[p] _ E)) +
      (dS.comp (ContinuousLinearMap.snd ℚ_[p] _ E)) <• B)

/-- Differentiate the actual full product in the inverse-Cayley coordinates.
The target-domain condition follows from the supplied product equation; the
left factor's derivative is supplied, not constructed from a chosen section. -/
theorem hasFDerivAt_lastCayleyProduct
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasFDerivAt S dS z)
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) :
    HasFDerivAt
      (fun q ↦ padicCayleyInverseMatrix p
        (S q.2 * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1)))
      (W.lastCayleyProductDerivative a ha p (S z) dS Y) (Y,z) := by
  have hl := hS.comp (Y,z) (ContinuousLinearMap.snd ℚ_[p] _ E).hasFDerivAt
  have hr := (W.hasFDerivAt_lastCayleyLowerMatrix a ha p Y hY).comp (Y,z)
    (ContinuousLinearMap.fst ℚ_[p] _ E).hasFDerivAt
  have hi : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) ∈
      padicCayleyInverseDomain p := by
    rw [hproduct]
    exact padicCayleyForwardMatrix_mem_inverseDomain p X.1 hX
  exact (hasFDerivAt_padicCayleyInverseMatrix p _ hi).comp (Y,z) (hl.mul' hr)

set_option backward.isDefEq.respectTransparency false in
/-- The vertical columns of the full derivative are the derivative of the
actual translated Cayley curve, throughout the own lower source. -/
theorem lastCayleyProductDerivative_vertical
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    W.lastCayleyProductDerivative a ha p S dS Y (H,0) =
      padicCayleyRelativeTransitionDerivative p S (W.lastSkewAmbientInclusion a ha p Y)
        (W.lastSkewAmbientInclusion a ha p H) := by
  have hYembed :
      W.lastSkewAmbientInclusion a ha p Y = zeroLastBlockMatrix Y.1 := by
    change (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y :
      Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = _
    exact W.coe_nonisotropicLastSkewAdjointEmbed_apply a ha ℚ_[p] Y
  rw [hYembed]
  dsimp only [lastCayleyProductDerivative]
  rw [← W.lastCayley_embedded_forward a ha p Y hY]
  simp [padicCayleyRelativeTransitionDerivative,
    skewAdjointPadicCayleyForwardDerivative, lastSkewAmbientInclusion]

/-- The horizontal columns keep the actual derivative of the supplied left
factor and the lower group matrix. No horizontal lift is substituted. -/
theorem lastCayleyProductDerivative_horizontal
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (v : E) :
    W.lastCayleyProductDerivative a ha p S dS Y (0,v) =
      padicCayleyInverseDerivative p
        (S * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y))
        (dS v * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y)) := by
  simp [lastCayleyProductDerivative]

/-- The actual full product derivative has exactly the required vertical
columns at general lower and higher chart points. -/
theorem lastCayleyProductDerivative_vertical_eq_frame
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) :
    W.lastCayleyProductDerivative a ha p S dS Y (H,0) =
      (skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY H))).1 := by
  rw [W.lastCayleyProductDerivative_vertical a ha p S dS Y H hY]
  exact W.lastCayleyVerticalProduct_derivative_at a ha p X hX S Y H hY hproduct

end RationalQuadraticSpaceMatrix
