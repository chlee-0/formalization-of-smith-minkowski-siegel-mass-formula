import SMSFormula.QuadraticPadicCayleyProductStrict
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The nonlinear local inverse of the actual p-adic Cayley product.
Along the lower source and supplied horizontal directions, the actual product
lies in the higher Lie algebra near the base point, has the closed frame
bijection as strict derivative, and mathlib's inverse function theorem over the
complete field Q_p gives an open partial homeomorphism. Only the germ at the base
point is meaningful: away from the eventual membership set the typed value is
the junk value 0 and no statement is made there. No chart, section, baseline,
Haar normalization or integrated change of variables is asserted. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
open scoped Matrix.Norms.Operator Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
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

local instance lastInverseLowerSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

local instance lastInverseHigherSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

local instance lastInverseLowerSkewLiteralIsUniformAddGroup :
    IsUniformAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  IsUniformAddGroup.comap
    (skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule.subtype.toAddMonoidHom

/-- The actual product along the lower source and the supplied horizontal
directions, in ambient inverse-Cayley coordinates. -/
def lastCayleyProductFrameAmbient
    (q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] :=
  padicCayleyInverseMatrix p (S (z + ∑ i, q.2 i • v i) *
    fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1))

/-- The supplied source directions, as a continuous linear map. -/
def lastCayleyProductFrameSourceCLM :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E) :=
  (ContinuousLinearMap.id ℚ_[p] _).prodMap
    (Fintype.linearCombination ℚ_[p] v).toContinuousLinearMap

theorem lastCayleyProductFrameSourceCLM_apply
    (q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) :
    lastCayleyProductFrameSourceCLM W p v q = (q.1, ∑ i, q.2 i • v i) := rfl

include hS hY hX hproduct in
/-- The already computed derivative, read on the supplied frame. -/
theorem hasStrictFDerivAt_lastCayleyProductFrameAmbient :
    HasStrictFDerivAt (W.lastCayleyProductFrameAmbient p S z v)
      ((W.lastCayleyProductDerivative a ha p (S z) dS Y).comp
        (lastCayleyProductFrameSourceCLM W p v)) (Y,0) := by
  have hσ : HasStrictFDerivAt
      (fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p]) ↦ (q.1, z + ∑ i, q.2 i • v i))
      (lastCayleyProductFrameSourceCLM W p v) (Y,0) := by
    have h := ((lastCayleyProductFrameSourceCLM W p v).hasStrictFDerivAt
      (x := ((Y, 0) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])))).const_add
      ((0 : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])), z)
    convert h using 1
    funext q
    rw [lastCayleyProductFrameSourceCLM_apply]
    ext
    · simp
    · simp [add_comm]
  have hP := W.hasStrictFDerivAt_lastCayleyProduct a ha p S dS z hS Y hY X hX hproduct
  have e : ((Y, z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i) :
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E) =
      (Y,z) := by simp
  rw [← e] at hP
  exact hP.comp (Y,0) hσ

include hS hSO hY hX hproduct in
/-- Near the base point the actual frame product lies in the higher Lie
algebra. This is proved from local SO-values, not assumed. -/
theorem lastCayleyProductFrameAmbient_eventually_mem :
    ∀ᶠ q in 𝓝 ((Y, 0) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])),
      W.lastCayleyProductFrameAmbient p S z v q ∈
        (skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule := by
  have hσ : Filter.Tendsto
      (fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p]) ↦ (q.1, z + ∑ i, q.2 i • v i)) (𝓝 (Y,0)) (𝓝 (Y,z)) := by
    have hc : Continuous
        (fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
          (Fin n → ℚ_[p]) ↦ (q.1, z + ∑ i, q.2 i • v i)) := by fun_prop
    simpa using hc.tendsto (Y,0)
  filter_upwards [hσ.eventually (W.lastCayleyProduct_eventually_specialOrthogonal a ha p S dS z
    hS.hasFDerivAt hSO Y hY X hX hproduct)] with q hq
  exact (mem_ker_skewAdjointOperator_iff _ _).mp
    (skewAdjointOperator_padicCayleyInverseMatrix_eq_zero
      (W.nonisotropicLastExtension a ha).pairingMatrix p ⟨_, hq.1⟩ hq.2)

/-- The actual frame product typed in the higher Lie algebra. Only its germ
at the base point is used; elsewhere the junk value 0 carries no content. -/
def lastCayleyProductFrameValue
    (q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) :
    skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) := by
  classical
  exact if h : W.lastCayleyProductFrameAmbient p S z v q ∈
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule
    then ⟨_, h⟩ else 0

include hS hSO hY hX hproduct in
/-- On a neighbourhood of the base point the typed value is the actual product. -/
theorem lastCayleyProductFrameValue_eventually_eq :
    ∀ᶠ q in 𝓝 ((Y, 0) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])),
      ((W.lastCayleyProductFrameValue a ha p S z v q :
        skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
        Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = W.lastCayleyProductFrameAmbient p S z v q := by
  filter_upwards [W.lastCayleyProductFrameAmbient_eventually_mem a ha p S dS z hS hSO Y hY X hX
    hproduct v] with q hq
  simp only [lastCayleyProductFrameValue, dif_pos hq]

/-- The closed frame bijection, as a continuous linear map into the Lie algebra. -/
def lastCayleyProductFrameCLM :=
  (W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS.hasFDerivAt hSO Y hY X hX
    hproduct).comp (lastCayleyProductFrameSourceCLM W p v)

theorem lastCayleyProductFrameCLM_coe_linearMap :
    (W.lastCayleyProductFrameCLM a ha p S dS z hS hSO Y hY X hX hproduct v :
      _ →ₗ[ℚ_[p]] _) =
      W.lastCayleyProductFrameMap a ha p S dS z hS.hasFDerivAt hSO Y hY X hX hproduct v := rfl

/-- The typed actual product has the frame map as strict derivative. -/
theorem hasStrictFDerivAt_lastCayleyProductFrameValue :
    HasStrictFDerivAt (W.lastCayleyProductFrameValue a ha p S z v)
      (W.lastCayleyProductFrameCLM a ha p S dS z hS hSO Y hY X hX hproduct v) (Y,0) := by
  refine hasStrictFDerivAt_subtype_of_coe (g' := (W.lastCayleyProductDerivative a ha p (S z) dS Y).comp
      (lastCayleyProductFrameSourceCLM W p v)) (fun _ ↦ rfl) ?_
  refine (W.hasStrictFDerivAt_lastCayleyProductFrameAmbient a ha p S dS z hS Y hY X hX hproduct
    v).congr_of_eventuallyEq ?_
  filter_upwards [W.lastCayleyProductFrameValue_eventually_eq a ha p S dS z hS hSO Y hY X hX
    hproduct v] with q hq
  exact hq.symm

variable (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
    lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

set_option backward.isDefEq.respectTransparency false in
/-- The closed frame bijection as a continuous linear equivalence. Continuity
is automatic in finite dimension over the complete field Q_p. -/
def lastCayleyProductFrameEquiv :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) ≃L[ℚ_[p]]
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) :=
  (LinearEquiv.ofBijective _
    (W.lastCayleyProductFrameMap_bijective a ha p S dS z hS.hasFDerivAt hSO Y hY X hX hproduct hs
      v hv)).toContinuousLinearEquiv

theorem lastCayleyProductFrameEquiv_coe :
    ((W.lastCayleyProductFrameEquiv a ha p S dS z hS hSO Y hY X hX hproduct v hs hv :
      _ →L[ℚ_[p]] _)) = W.lastCayleyProductFrameCLM a ha p S dS z hS hSO Y hY X hX hproduct v :=
  ContinuousLinearMap.ext fun _ ↦ rfl

include hs hv in
/-- The typed actual product has an invertible strict derivative at the base point. -/
theorem hasStrictFDerivAt_lastCayleyProductFrameValue_equiv :
    HasStrictFDerivAt (W.lastCayleyProductFrameValue a ha p S z v)
      ((W.lastCayleyProductFrameEquiv a ha p S dS z hS hSO Y hY X hX hproduct v hs hv :
        _ →L[ℚ_[p]] _)) (Y,0) := by
  rw [W.lastCayleyProductFrameEquiv_coe]
  exact W.hasStrictFDerivAt_lastCayleyProductFrameValue a ha p S dS z hS hSO Y hY X hX hproduct v

set_option backward.isDefEq.respectTransparency false in
include hs hv in
/-- Nonlinear local inverse of the actual product, from mathlib's inverse function
theorem over Q_p. The partial homeomorphism is the typed actual product on its
source; near the base point it agrees with the ambient inverse-Cayley product,
sends the base point to the point X, and its inverse has the inverse frame
equivalence as strict derivative. No measure transport is asserted. -/
theorem lastCayleyProduct_exists_localInverse :
    ∃ e : OpenPartialHomeomorph
        (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
          (Fin n → ℚ_[p]))
        (skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])),
      (Y,0) ∈ e.source ∧ ⇑e = W.lastCayleyProductFrameValue a ha p S z v ∧
      e (Y,0) = X ∧
      (∀ᶠ q in 𝓝 (Y,0), q ∈ e.source ∧
        ((e q : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
          Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = W.lastCayleyProductFrameAmbient p S z v q) ∧
      HasStrictFDerivAt e.symm
        (((W.lastCayleyProductFrameEquiv a ha p S dS z hS hSO Y hY X hX hproduct v hs hv).symm :
          _ →L[ℚ_[p]] _)) X := by
  haveI : CompleteSpace
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])) := FiniteDimensional.complete ℚ_[p] _
  have hf := W.hasStrictFDerivAt_lastCayleyProductFrameValue_equiv a ha p S dS z hS hSO Y hY X hX
    hproduct v hs hv
  have hbase : W.lastCayleyProductFrameValue a ha p S z v (Y,0) = X := by
    have hmem := (W.lastCayleyProductFrameValue_eventually_eq a ha p S dS z hS hSO Y hY X hX
      hproduct v).self_of_nhds
    apply Subtype.ext
    rw [hmem]
    change padicCayleyInverseMatrix p (S (z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i) *
      fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y)) = X.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [hproduct]
    exact padicCayleyInverseMatrix_forward p X.1 hX
  refine ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, rfl, hbase, ?_, ?_⟩
  · filter_upwards [(hf.toOpenPartialHomeomorph _).open_source.mem_nhds
      hf.mem_toOpenPartialHomeomorph_source,
      W.lastCayleyProductFrameValue_eventually_eq a ha p S dS z hS hSO Y hY X hX hproduct v]
      with q hq hq'
    exact ⟨hq, hq'⟩
  · have h := hf.to_localInverse
    rw [hbase] at h
    exact h

end RationalQuadraticSpaceMatrix
