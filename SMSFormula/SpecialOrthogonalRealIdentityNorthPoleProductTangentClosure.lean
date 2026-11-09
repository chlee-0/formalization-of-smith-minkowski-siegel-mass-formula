import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductPointwiseDerivative

/-!
# Tangent closure of the identity north-pole product derivative

This file proves that the left-trivialized derivative of the north-pole
product parametrization takes values in the higher-rank identity
special-orthogonal tangent space.  The proof differentiates the orthogonality
identity of the group-valued product, rather than expanding the section
blocks.
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

namespace PositiveDefiniteIntegralLattice

open Matrix MeasureTheory Topology

variable (n : ℕ)

/-- The represented north-pole product matrix is orthogonal on its exact
domain. -/
theorem identitySpecialOrthogonalNorthPoleProductMatrix_transpose_mul_self
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalNorthPoleProductMatrix n p)ᵀ *
        identitySpecialOrthogonalNorthPoleProductMatrix n p =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  let ps : identitySpecialOrthogonalNorthPoleProductDomain n := ⟨p, hp⟩
  let g : identitySpecialOrthogonalGroup n :=
    identitySpecialOrthogonalNorthPoleProduct n ps
  have hg := g.1.2
  change g.1.1.1ᵀ * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
      g.1.1.1 = 1 at hg
  simpa [g, ps, coe_identitySpecialOrthogonalNorthPoleProduct, Matrix.mul_one] using hg

/-- The represented north-pole product matrix has determinant one on its
exact domain. -/
theorem identitySpecialOrthogonalNorthPoleProductMatrix_det
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalNorthPoleProductMatrix n p).det = 1 := by
  let ps : identitySpecialOrthogonalNorthPoleProductDomain n := ⟨p, hp⟩
  let g : identitySpecialOrthogonalGroup n :=
    identitySpecialOrthogonalNorthPoleProduct n ps
  have hg :=
    (mem_specialFormPreservingMatrixSubgroup_iff
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) g.1).mp g.2
  simpa [g, ps, coe_identitySpecialOrthogonalNorthPoleProduct] using hg

/-- On the exact product domain, the nonsingular inverse used by left
trivialization is the transpose. -/
theorem identitySpecialOrthogonalNorthPoleProductMatrix_nonsing_inv_eq_transpose
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ =
      (identitySpecialOrthogonalNorthPoleProductMatrix n p)ᵀ := by
  let M := identitySpecialOrthogonalNorthPoleProductMatrix n p
  have hdet : IsUnit M.det := by
    rw [identitySpecialOrthogonalNorthPoleProductMatrix_det n hp]
    exact isUnit_one
  have horth : Mᵀ * M = 1 :=
    identitySpecialOrthogonalNorthPoleProductMatrix_transpose_mul_self n hp
  calc
    M⁻¹ = 1 * M⁻¹ := by rw [Matrix.one_mul]
    _ = (Mᵀ * M) * M⁻¹ := by rw [horth]
    _ = Mᵀ * (M * M⁻¹) := by rw [Matrix.mul_assoc]
    _ = Mᵀ := by rw [Matrix.mul_nonsing_inv M hdet, Matrix.mul_one]

/-- Differentiating `Mᵀ M = 1` on the open product domain gives the usual
infinitesimal orthogonality equation. -/
theorem identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_orthogonality
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (q :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p q)ᵀ *
          identitySpecialOrthogonalNorthPoleProductMatrix n p +
        (identitySpecialOrthogonalNorthPoleProductMatrix n p)ᵀ *
          identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p q =
      0 := by
  let M :=
    fun y :
        identitySpecialOrthogonalMappedTangent n ×
          EuclideanSpace ℝ (Fin n) =>
      identitySpecialOrthogonalNorthPoleProductMatrix n y
  let D := identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p
  have hM : HasFDerivAt M D p :=
    hasFDerivAt_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise n hp
  have hMT :
      HasFDerivAt (fun y => (M y)ᵀ)
        ((Matrix.transposeContinuousLinearMap
          (K := ℝ) (ι := Fin (n + 1))).comp D) p :=
    (Matrix.transposeContinuousLinearMap
      (K := ℝ) (ι := Fin (n + 1))).hasFDerivAt.comp p hM
  have hprod := hMT.mul' hM
  have heq :
      (fun y => (M y)ᵀ * M y) =ᶠ[𝓝 p]
        (fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) := by
    filter_upwards
      [(isOpen_identitySpecialOrthogonalNorthPoleProductDomainSet n).mem_nhds hp]
      with y hy
    exact identitySpecialOrthogonalNorthPoleProductMatrix_transpose_mul_self n hy
  have hderiv :=
    (hprod.congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_const
        (x := p)
        (c := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)))
  have hq := congrArg (fun L => L q) hderiv
  simpa [M, D, add_comm] using hq

/-- The ambient left-trivialized product derivative is a skew-adjoint
higher-rank identity tangent vector. -/
theorem identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_mem_tangent
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (q :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative n p q ∈
      identitySpecialOrthogonalTangent (n + 1) := by
  apply (LieAlgebra.Orthogonal.mem_so
    (Fin (n + 1)) ℝ
    (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
      n p q)).mpr
  rw [identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply]
  rw [identitySpecialOrthogonalNorthPoleProductMatrix_nonsing_inv_eq_transpose n hp]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_left
    (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_orthogonality n hp q)

/-- The left-trivialized product derivative, with its genuine
special-orthogonal tangent codomain. -/
def identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
    (p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n))
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) →L[ℝ]
      identitySpecialOrthogonalTangent (n + 1) :=
  (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative n p).codRestrict
    (identitySpecialOrthogonalTangent (n + 1))
    (fun q =>
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_mem_tangent
        n hp q)

@[simp]
theorem coe_identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (q :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
        n p hp q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative n p q :=
  rfl

/-- Composition of the tangent-valued derivative with the consecutive-rank
tangent split. -/
def identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
    (p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n))
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalTangentContinuousLinearEquiv n).toContinuousLinearMap.comp
    (identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
      n p hp)

/-- The tangent split recovers the ambient block extractor. -/
theorem identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_ambient
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (q :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :
    (((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp q).1 : Matrix (Fin n) (Fin n) ℝ),
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp q).2) =
      identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap n
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative n p q) := by
  symm
  exact identitySpecialOrthogonalAmbientTangentSplit_eq_tangentSplit n
    (identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
      n p hp q)

/-- The tangent-valued split has the same lower/mixed/transverse block
decomposition as the ambient extractor. -/
theorem identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_block_decomposition
    {p :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (H : identitySpecialOrthogonalMappedTangent n)
    (h : EuclideanSpace ℝ (Fin n)) :
    (((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp (H, h)).1 : Matrix (Fin n) (Fin n) ℝ),
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp (H, h)).2) =
      (identitySpecialOrthogonalLowerChartMovingDerivative n p.1 H +
          identitySpecialOrthogonalNorthPoleProductMixedDerivative n p h,
        identitySpecialOrthogonalNorthPoleProductTransverseDerivative n p h) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_ambient
      n hp]
  exact
    identitySpecialOrthogonalNorthPoleProductLeftTrivialized_block_decomposition
      n hp H h

end PositiveDefiniteIntegralLattice
