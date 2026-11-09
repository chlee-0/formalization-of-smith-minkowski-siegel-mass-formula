import SMSFormula.PadicCayleyStrictDifferential
import SMSFormula.QuadraticPadicCayleyProductTransverse

/-! Strict differentiability of the actual p-adic Cayley product. The
Cayley maps are analytic, so their already computed derivatives are strict; a
supplied strictly differentiable left factor then makes the full product
strictly differentiable with the same derivative. No chart or section is built. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
open scoped Matrix.Norms.Operator Topology

/-- A map into a normed subgroup has a strict derivative once its ambient
values do, with a derivative landing in the subgroup. Norms are the
ambient norms; no projection or complement is used. -/
theorem hasStrictFDerivAt_subtype_of_coe
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {K : Type*} [SetLike K F] [AddSubgroupClass K F] [SMulMemClass K 𝕜 F] {s : K}
    {f : E → s} {f' : E →L[𝕜] s} {g' : E →L[𝕜] F} {x : E}
    (hg : ∀ v, ((f' v : s) : F) = g' v)
    (h : HasStrictFDerivAt (fun y ↦ (f y : F)) g' x) : HasStrictFDerivAt f f' x := by
  rw [hasStrictFDerivAt_iff_isLittleO] at h ⊢
  refine (Asymptotics.isLittleO_norm_left).mp ?_
  refine ((Asymptotics.isLittleO_norm_left).mpr h).congr_left (fun q ↦ ?_)
  rw [← hg]
  rfl

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

local instance lastStrictProductSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

set_option backward.isDefEq.respectTransparency false in
/-- The own lower group chart, embedded as fixed-last matrices, has the
embedded derivative in the strict sense on the same exact source. -/
theorem hasStrictFDerivAt_lastCayleyLowerMatrix
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    HasStrictFDerivAt
      (fun Z ↦ fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Z))
      ((skewAdjointPadicCayleyForwardDerivative (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)).comp
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap) Y := by
  have hd := (hasStrictFDerivAt_skewAdjointPadicCayleyForwardMatrix
    (W.nonisotropicLastExtension a ha).pairingMatrix p _
    ((W.lastCayley_embedded_source_iff a ha p Y).mpr hY)).comp Y
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]).toContinuousLinearMap.hasStrictFDerivAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_skewAdjointPadicCayleySource W.pairingMatrix p).mem_nhds hY] with Z hZ
  exact W.lastCayley_embedded_forward a ha p Z hZ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]

/-- The actual full product in inverse-Cayley coordinates has the already
computed derivative in the strict sense, for a supplied strictly
differentiable left factor. The derivative is unchanged. -/
theorem hasStrictFDerivAt_lastCayleyProduct
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasStrictFDerivAt S dS z)
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) :
    HasStrictFDerivAt
      (fun q ↦ padicCayleyInverseMatrix p
        (S q.2 * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1)))
      (W.lastCayleyProductDerivative a ha p (S z) dS Y) (Y,z) := by
  have hl := hS.comp (Y,z) (ContinuousLinearMap.snd ℚ_[p] _ E).hasStrictFDerivAt
  have hr := (W.hasStrictFDerivAt_lastCayleyLowerMatrix a ha p Y hY).comp (Y,z)
    (ContinuousLinearMap.fst ℚ_[p] _ E).hasStrictFDerivAt
  have hi : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) ∈
      padicCayleyInverseDomain p := by
    rw [hproduct]
    exact padicCayleyForwardMatrix_mem_inverseDomain p X.1 hX
  exact (hasStrictFDerivAt_padicCayleyInverseMatrix p _ hi).comp (Y,z) (hl.mul' hr)

end RationalQuadraticSpaceMatrix
