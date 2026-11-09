import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeRadialSector
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleLocalInverse
import SMSFormula.SpecialOrthogonalRealIdentityTangentDetFactorization

/-!
# Identity-model north-pole product transition

This file composes the lower-rank/north-pole product parametrization with the
higher-rank identity-chart coordinate map.  It identifies the derivative at
the identity with the explicit tangent unsplitting equivalence and computes
its determinant relative to the fixed rationally normalized bases.

The exact source neighborhood is the part of the product domain whose
group-valued product lies in the higher identity chart.
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

open Matrix Metric Set

namespace PositiveDefiniteIntegralLattice

private theorem basis_det_inv
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    (A D : Module.Basis ι ℝ E) :
    D.det A = (A.det D)⁻¹ := by
  rw [← Module.Basis.det_basis A D,
    ← Module.Basis.det_basis D A]
  have heq :
      (A.equiv D (Equiv.refl ι)).symm =
        D.equiv A (Equiv.refl ι) := by
    apply LinearEquiv.ext
    intro x
    apply (A.equiv D (Equiv.refl ι)).injective
    simp
  rw [← heq, ← LinearEquiv.coe_det, LinearEquiv.det_symm]
  simp

private theorem basis_det_map_both
    {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E']
    (A D : Module.Basis ι ℝ E) (e : E ≃ₗ[ℝ] E') :
    (A.map e).det (D.map e) = A.det D := by
  rw [Module.Basis.det_map]
  congr 1
  ext i
  simp

noncomputable def
    identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
    (n : ℕ) :
    identitySpecialOrthogonalMappedTangent n ≃L[ℝ]
      identitySpecialOrthogonalTangent n := by
  letI : IsUniformAddGroup (identitySpecialOrthogonalMappedTangent n) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  letI : IsUniformAddGroup (identitySpecialOrthogonalTangent n) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  letI : IsBoundedSMul ℝ (identitySpecialOrthogonalMappedTangent n) :=
    NormedSpace.toIsBoundedSMul
  letI : IsBoundedSMul ℝ (identitySpecialOrthogonalTangent n) :=
    NormedSpace.toIsBoundedSMul
  let mappedScalar : ContinuousSMul ℝ (identitySpecialOrthogonalMappedTangent n) :=
    IsBoundedSMul.continuousSMul
  let literalScalar : ContinuousSMul ℝ (identitySpecialOrthogonalTangent n) :=
    IsBoundedSMul.continuousSMul
  let mappedGroup : IsTopologicalAddGroup (identitySpecialOrthogonalMappedTangent n) :=
    IsUniformAddGroup.to_topologicalAddGroup
  let literalGroup : IsTopologicalAddGroup (identitySpecialOrthogonalTangent n) :=
    IsUniformAddGroup.to_topologicalAddGroup
  exact @LinearEquiv.toContinuousLinearEquiv ℝ _
    (identitySpecialOrthogonalMappedTangent n) _ _ _ mappedGroup mappedScalar
    (identitySpecialOrthogonalTangent n) _ _ _ literalGroup literalScalar _ _ _ _
    (identitySpecialOrthogonalMappedIdentityTangentEquiv n)

noncomputable def
    identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv
    (n : ℕ) :
    (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
    ).prodCongr
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))

noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv
    (n : ℕ) :
    (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        identitySpecialOrthogonalMappedTangent (n + 1) :=
  (identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv n).trans
    ((identitySpecialOrthogonalTangentContinuousLinearEquiv n).symm.trans
      (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
        (n + 1)).symm)

noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
    (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :=
  (identitySpecialOrthogonalTangentProductBasis n).map
    (identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv n
      ).symm.toLinearEquiv

noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis
    (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalMappedTangent (n + 1)) :=
  skewAdjointScalarExtensionFinBasis (K := ℝ)
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)

noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
    (n : ℕ) : ℝ :=
  (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).det
    ((identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
        ).toLinearEquiv)

def identitySpecialOrthogonalNorthPoleProductTransition (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalMappedTangent (n + 1) :=
  specialFormPreservingSmoothRealForwardCoordinate
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (identitySpecialOrthogonalNorthPoleProductMatrix n p)

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductTransition_zero (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransition n 0 = 0 := by
  rw [identitySpecialOrthogonalNorthPoleProductTransition,
    identitySpecialOrthogonalNorthPoleProductMatrix_zero]
  simpa using
    specialFormPreservingSmoothRealForwardCoordinate_one_add
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      (0 : identitySpecialOrthogonalMappedTangent (n + 1))

theorem identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis_map (n : ℕ) :
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).map
        (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
          (n + 1)).toLinearEquiv =
      identitySpecialOrthogonalFixedTangentBasis (n + 1) := by
  apply DFunLike.ext _ _
  intro index
  rfl

theorem
    identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis_map
    (n : ℕ) :
    ((identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
          ).toLinearEquiv).map
        (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
          (n + 1)).toLinearEquiv =
      (identitySpecialOrthogonalTangentProductBasis n).map
        (identitySpecialOrthogonalTangentContinuousLinearEquiv n
          ).symm.toLinearEquiv := by
  apply DFunLike.ext _ _
  intro i
  simp [identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis,
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv,
    identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv]

theorem identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_eq (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n =
      (identitySpecialOrthogonalTangentSplitDetScalar n)⁻¹ := by
  let H := identitySpecialOrthogonalFixedTangentBasis (n + 1)
  let A := identitySpecialOrthogonalTangentProductBasis n
  let e := identitySpecialOrthogonalTangentContinuousLinearEquiv n
  have hmap :
      identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n = H.det (A.map e.symm.toLinearEquiv) := by
    rw [identitySpecialOrthogonalNorthPoleProductTransitionDetScalar, ← basis_det_map_both
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n)
      ((identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
          ).toLinearEquiv)
      (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
        (n + 1)).toLinearEquiv,
      identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis_map,
      identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis_map]
  rw [hmap, basis_det_inv (A.map e.symm.toLinearEquiv) H]
  rw [← basis_det_map_both
    (A.map e.symm.toLinearEquiv) H e.toLinearEquiv]
  rw [identitySpecialOrthogonalTangentSplitDetScalar,
    identitySpecialOrthogonalTangentSplitTransportedBasis]
  apply congrArg Inv.inv
  have hbasis :
      (A.map e.symm.toLinearEquiv).map e.toLinearEquiv = A := by
    apply DFunLike.ext _ _
    intro i
    simp
  rw [hbasis]

theorem identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n ≠ 0 := by
  rw [identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_eq]
  exact inv_ne_zero
    (identitySpecialOrthogonalTangentSplitDetScalar_ne_zero n)

theorem abs_identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
    (n : ℕ) :
    |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| =
      |identitySpecialOrthogonalTangentSplitDetScalar n|⁻¹ := by
  rw [identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_eq,
    abs_inv]

theorem contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition (n : ℕ) :
    ContDiffOn ℝ ∞ (identitySpecialOrthogonalNorthPoleProductTransition n)
      (identitySpecialOrthogonalNorthPoleProductDomainSet n) := by
  exact
    (contDiff_specialFormPreservingSmoothRealForwardCoordinate
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      ).comp_contDiffOn
        (contDiffOn_identitySpecialOrthogonalNorthPoleProductMatrix n)

def identitySpecialOrthogonalNorthPoleProductMappedGroup (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 1)
    (identitySpecialOrthogonalNorthPoleProduct n p)

theorem identitySpecialOrthogonalNorthPoleProductMappedGroup_coe (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    (identitySpecialOrthogonalNorthPoleProductMappedGroup n p).1.1.1 =
      identitySpecialOrthogonalNorthPoleProductMatrix n p.1 := by
  rw [identitySpecialOrthogonalNorthPoleProductMappedGroup,
    coe_identitySpecialOrthogonalLiteralIdentityGroupToMapped,
    coe_identitySpecialOrthogonalNorthPoleProduct]

theorem identitySpecialOrthogonalNorthPoleProductMappedGroup_continuous (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleProductMappedGroup n) :=
  (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n + 1)).comp
      (continuous_identitySpecialOrthogonalNorthPoleProduct n)

def identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
    (n : ℕ) :
    Set (identitySpecialOrthogonalNorthPoleProductDomain n) :=
  identitySpecialOrthogonalNorthPoleProductMappedGroup n ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).source

theorem
    isOpen_identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
    (n : ℕ) :
    IsOpen
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet n) :=
  (specialFormPreservingSmoothRealIdentityChart
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm
    identityRationalForm_det_ne_zero).open_source.preimage
      (identitySpecialOrthogonalNorthPoleProductMappedGroup_continuous n)

def identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet (n : ℕ) :
    Set (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :=
  Subtype.val '' identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet n

theorem identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :=
  (isOpen_identitySpecialOrthogonalNorthPoleProductDomainSet n
    ).isOpenMap_subtype_val _
      (isOpen_identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
        n)

theorem identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n ⊆
      identitySpecialOrthogonalNorthPoleProductDomainSet n := by
  rintro p ⟨q, -, rfl⟩
  exact q.2

theorem identitySpecialOrthogonalNorthPoleProductMappedGroup_zero (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMappedGroup n
        ⟨0, zero_mem_identitySpecialOrthogonalNorthPoleProductDomainSet n⟩ =
      1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [identitySpecialOrthogonalNorthPoleProductMappedGroup_coe,
    identitySpecialOrthogonalNorthPoleProductMatrix_zero]
  rfl

theorem
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_zero_mem
    (n : ℕ) :
    (0 : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n := by
  let p :
      identitySpecialOrthogonalNorthPoleProductDomain n :=
    ⟨0, zero_mem_identitySpecialOrthogonalNorthPoleProductDomainSet n⟩
  refine ⟨p, ?_, rfl⟩
  change identitySpecialOrthogonalNorthPoleProductMappedGroup n p ∈
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).source
  rw [show identitySpecialOrthogonalNorthPoleProductMappedGroup n p = 1 by
    exact identitySpecialOrthogonalNorthPoleProductMappedGroup_zero n]
  exact self_mem_specialFormPreservingSmoothRealChart_source
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero 1

theorem identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductDomain n)
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet n) :
    identitySpecialOrthogonalNorthPoleProductTransition n p.1 =
      specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (identitySpecialOrthogonalNorthPoleProductMappedGroup n p) := by
  rw [specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
    _ _ _ _ hp]
  exact congrArg
    (specialFormPreservingSmoothRealForwardCoordinate
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero)
    (identitySpecialOrthogonalNorthPoleProductMappedGroup_coe n p).symm

theorem contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition_higherChartSource (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalNorthPoleProductTransition n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :=
  (contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition n).mono
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset n)

end PositiveDefiniteIntegralLattice
