import SMSFormula.QuadraticPadicCayleyArbitraryFrame
import SMSFormula.PadicCayleyTranslatedChartOverlapTangent

/-! Actual vertical multiplication in the chart. At any supplied higher
chart point, right multiplication by the embedded Cayley curve has the
vertical derivative used by the density theorem. The lower parameter here is
zero; this is neither a new product chart nor a nonlinear change of variables. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal NNReal Matrix.Norms.Operator Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)

local instance lastSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance lastSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

set_option backward.isDefEq.respectTransparency false in
/-- The existing lower tangent embedding followed by ambient inclusion.
Continuity uses finite dimension; no new coordinates are introduced. -/
def lastSkewAmbientInclusion :
    skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) →L[ℚ_[p]]
      Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] :=
  (skewAdjointPadicAmbientInclusion (W.nonisotropicLastExtension a ha).pairingMatrix p).comp
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap

/-- The embedded Cayley curve lies in the actual last-vector stabilizer
on its exact source, not merely in the tangent kernel at zero. -/
theorem lastCayley_embedded_fixes
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y ∈
      skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) :
    Matrix.mulVec (skewAdjointPadicCayleyForwardMatrix
      (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)) lastCoordinateVector =
      lastCoordinateVector := by
  let A := (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y).1
  have hz : A *ᵥ lastCoordinateVector = 0 := by
    rw [lastCoordinateVector, Matrix.mulVec_single_one]
    funext i
    exact W.nonisotropicLastSkewAdjointEmbed_mem_fiber a ha ℚ_[p] Y i
  have hm : (1 - A) *ᵥ lastCoordinateVector = lastCoordinateVector := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hz, sub_zero]
  have hi : (1 - A)⁻¹ *ᵥ lastCoordinateVector = lastCoordinateVector := by
    calc
      _ = (1 - A)⁻¹ *ᵥ ((1 - A) *ᵥ lastCoordinateVector) := congrArg _ hm.symm
      _ = _ := by
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hY), Matrix.one_mulVec]
  change ((1 + A) * (1 - A)⁻¹) *ᵥ lastCoordinateVector = _
  rw [← Matrix.mulVec_mulVec, hi, Matrix.add_mulVec, Matrix.one_mulVec, hz, add_zero]

/-- Exact orbit constancy under the actual right-hand stabilizer factor;
the left factor is supplied and may be the value of a section. -/
theorem lastCayley_verticalProduct_orbit
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y ∈
      skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) :
    Matrix.mulVec (S * skewAdjointPadicCayleyForwardMatrix
      (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)) lastCoordinateVector =
      S *ᵥ lastCoordinateVector := by
  rw [← Matrix.mulVec_mulVec, W.lastCayley_embedded_fixes a ha p Y hY]

set_option backward.isDefEq.respectTransparency false in
/-- The exact source condition used above holds on a neighborhood of the
lower identity, by the openness of the source and linear embedding. -/
theorem eventually_lastCayley_embedded_source :
    ∀ᶠ Y in 𝓝 (0 : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])),
      W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y ∈
        skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p := by
  have hopen := (isOpen_skewAdjointPadicCayleySource
    (W.nonisotropicLastExtension a ha).pairingMatrix p).preimage
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap.continuous
  exact hopen.mem_nhds (by simpa only [Set.mem_preimage, map_zero] using
    zero_mem_skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)

/-- The actual group product has locally constant orbit in its lower variable.
This checks the vertical derivative without assuming a fiber parametrization. -/
theorem hasFDerivAt_lastCayleyVerticalProduct_orbit
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) :
    HasFDerivAt (𝕜 := ℚ_[p]) (fun Y ↦ Matrix.mulVec
      (S * skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)) lastCoordinateVector) 0 0 := by
  have he := (W.eventually_lastCayley_embedded_source a ha p).mono
    (fun Y hY ↦ W.lastCayley_verticalProduct_orbit a ha p S Y hY)
  exact (hasFDerivAt_const (S *ᵥ lastCoordinateVector)
    (0 : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))).congr_of_eventuallyEq
      he

include hX in
/-- Chain rule for the actual old inverse-Cayley coordinate of the product,
not a proposed tangent frame. Its source curve is the old embedded Cayley map. -/
theorem hasFDerivAt_lastCayleyVerticalProduct :
    HasFDerivAt
      (fun Y ↦ padicCayleyRelativeTransitionMatrix p
        (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
        (W.lastSkewAmbientInclusion a ha p Y))
      ((padicCayleyRelativeTransitionDerivative p
        (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) 0).comp
        (W.lastSkewAmbientInclusion a ha p)) 0 := by
  have hrel : skewAdjointPadicCayleyForwardMatrix
      (W.nonisotropicLastExtension a ha).pairingMatrix p X * padicCayleyForwardMatrix p 0 ∈
      padicCayleyInverseDomain p := by
    simpa [padicCayleyForwardMatrix] using padicCayleyForwardMatrix_mem_inverseDomain p X.1 hX
  have ht := (hasFDerivAt_padicCayleyRelativeTransitionMatrix p
    (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    0 (zero_mem_padicCayleySource p) hrel)
  have ht' : HasFDerivAt
      (padicCayleyRelativeTransitionMatrix p
        (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X))
      (padicCayleyRelativeTransitionDerivative p
        (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) 0)
      (W.lastSkewAmbientInclusion a ha p 0) := by simpa only [map_zero] using ht
  exact ht'.comp 0 (W.lastSkewAmbientInclusion a ha p).hasFDerivAt

include hX in
set_option backward.isDefEq.respectTransparency false in
/-- The actual product derivative equals precisely the inverse ambient
Cayley differential of the embedded lower differential. Higher X is arbitrary;
only the lower parameter is at its identity. -/
theorem lastCayleyVerticalProduct_derivative
    (H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    padicCayleyRelativeTransitionDerivative p
      (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) 0
      (W.lastSkewAmbientInclusion a ha p H) =
      (skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p 0
            (zero_mem_skewAdjointPadicCayleySource W.pairingMatrix p) H))).1 := by
  have ht := padicCayleyRelativeTransitionDerivative_skewAdjoint
    (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastExtension a ha).form_det_ne_zero
    (skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    0 X (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] H)
    (zero_mem_skewAdjointPadicCayleySource _ p) hX (by simp [skewAdjointPadicCayleyForwardMatrix, padicCayleyForwardMatrix])
  have hinc : W.lastSkewAmbientInclusion a ha p H =
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] H).1 := rfl
  have hzero {k : ℕ} (F : Matrix (Fin k) (Fin k) ℚ)
      (Y : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
      skewAdjointPadicCayleyLeftTrivializedEndomorphism F p 0
          (zero_mem_skewAdjointPadicCayleySource F p) Y = Y + Y := by
    apply Subtype.ext
    simp [coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply, two_smul]
  have hinput :
      skewAdjointPadicCayleyLeftTrivializedEndomorphism
          (W.nonisotropicLastExtension a ha).pairingMatrix p 0
          (zero_mem_skewAdjointPadicCayleySource _ p)
          (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] H) =
        W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p 0
            (zero_mem_skewAdjointPadicCayleySource _ p) H) := by
    rw [hzero, hzero]
    exact ((W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).map_add H H).symm
  simp only [ZeroMemClass.coe_zero] at ht
  rw [hinc, ht, skewAdjointPadicCayleyTransitionTangentEquiv_apply, hinput]

end RationalQuadraticSpaceMatrix
