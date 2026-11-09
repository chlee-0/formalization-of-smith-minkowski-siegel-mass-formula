import SMSFormula.QuadraticPadicCayleyVerticalProduct

/-! Compatibility of the lower embedding with both Cayley maps and
full differentials. Exact source equivalence, no new chart or Haar. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
open scoped Matrix.Norms.Operator
namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}

private theorem one_add_zeroLast {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) :
    1 + zeroLastBlockMatrix A = fixLastBlockMatrix (1 + A) := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [fixLastBlockMatrix, Matrix.one_apply, eq_comm]

private theorem one_sub_zeroLast {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) :
    1 - zeroLastBlockMatrix A = fixLastBlockMatrix (1 - A) := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [fixLastBlockMatrix, Matrix.one_apply, eq_comm]

private theorem fixLast_inv {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    (fixLastBlockMatrix A)⁻¹ = fixLastBlockMatrix A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← fixLastBlockMatrix_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    fixLastBlockMatrix_one]

private theorem fixLast_mul_zeroLast {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) :
    fixLastBlockMatrix A * zeroLastBlockMatrix B = zeroLastBlockMatrix (A * B) := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, fixLastBlockMatrix]

private theorem zeroLast_mul_fixLast {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) :
    zeroLastBlockMatrix A * fixLastBlockMatrix B = zeroLastBlockMatrix (A * B) := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, fixLastBlockMatrix]

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

/-- The source is exactly the lower group's own old Cayley source. -/
theorem lastCayley_embedded_source_iff
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y ∈
      skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p ↔
    Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p := by
  change IsUnit (1 - zeroLastBlockMatrix Y.1) ↔ IsUnit (1 - Y.1)
  rw [one_sub_zeroLast, Matrix.isUnit_iff_isUnit_det, fixLastBlockMatrix_det,
    Matrix.isUnit_iff_isUnit_det]

/-- The actual embedded Cayley matrix is the fixed-last group embedding
of the lower Cayley matrix, throughout the lower group's own old source. -/
theorem lastCayley_embedded_forward
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y) =
      fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) := by
  change (1 + zeroLastBlockMatrix Y.1) * (1 - zeroLastBlockMatrix Y.1)⁻¹ = _
  rw [one_add_zeroLast, one_sub_zeroLast, fixLast_inv _ hY, ← fixLastBlockMatrix_mul]
  rfl

/-- The matrix compatibility is equality of the actual old group points,
using the last-extension stabilizer embedding and point-to-group maps. -/
theorem lastCayley_embedded_group
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    specialOrthogonalMatrixSetToSpecialSubgroup
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])
      (skewAdjointPadicCayleySpecialOrthogonal (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        ⟨W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y,
          (W.lastCayley_embedded_source_iff a ha p Y).mpr hY⟩) =
    W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p]
      (specialOrthogonalMatrixSetToSpecialSubgroup (W.specialOrthogonalMappedFormMatrix ℚ_[p])
        (skewAdjointPadicCayleySpecialOrthogonal W.pairingMatrix p W.form_det_ne_zero ⟨Y,hY⟩)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact W.lastCayley_embedded_forward a ha p Y hY

/-- Full lower and ambient left-trivialized derivatives commute with the
embedding at every lower source point. No evaluation at zero is used. -/
theorem lastCayley_embedded_differential
    (Y H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p) :
    skewAdjointPadicCayleyLeftTrivializedEndomorphism
      (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y)
      ((W.lastCayley_embedded_source_iff a ha p Y).mpr hY)
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] H) =
    W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
      (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY H) := by
  apply Subtype.ext
  simp only [skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply,
    coe_skewAdjointPadicCayleyLeftTrivializedPoint, coe_nonisotropicLastSkewAdjointEmbed_apply]
  rw [one_add_zeroLast, one_sub_zeroLast,
    fixLast_inv _ (isUnit_one_add_of_mem_skewAdjointPadicCayleySource W.pairingMatrix p W.form_det_ne_zero Y hY),
    fixLast_inv _ hY, fixLast_mul_zeroLast, zeroLast_mul_fixLast]
  simp only [two_smul, zeroLastBlockMatrix_add]

/-- Actual vertical product derivative at a general lower source point.
The supplied product relation identifies the exact old higher coordinate X. -/
theorem lastCayleyVerticalProduct_derivative_at
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (hproduct : S * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) :
    padicCayleyRelativeTransitionDerivative p S (W.lastSkewAmbientInclusion a ha p Y)
      (W.lastSkewAmbientInclusion a ha p H) =
      (skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY H))).1 := by
  have ht := padicCayleyRelativeTransitionDerivative_skewAdjoint
    (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastExtension a ha).form_det_ne_zero S
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y) X
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] H)
    ((W.lastCayley_embedded_source_iff a ha p Y).mpr hY) hX
    (by rw [W.lastCayley_embedded_forward a ha p Y hY]; exact hproduct)
  refine ht.trans ?_
  change (skewAdjointPadicCayleyLeftTrivializedInverse _ p X _).1 = _
  congr 2
  exact W.lastCayley_embedded_differential a ha p Y H hY

/-- Chain rule on the actual multiplication/inverse-Cayley expression,
at any supplied compatible lower/higher points. No product chart is asserted. -/
theorem hasFDerivAt_lastCayleyVerticalProduct_at
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (hproduct : S * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X) :
    HasFDerivAt
      (fun Z ↦ padicCayleyRelativeTransitionMatrix p S (W.lastSkewAmbientInclusion a ha p Z))
      ((padicCayleyRelativeTransitionDerivative p S (W.lastSkewAmbientInclusion a ha p Y)).comp
        (W.lastSkewAmbientInclusion a ha p)) Y := by
  have hs : W.lastSkewAmbientInclusion a ha p Y ∈ padicCayleySource p :=
    (W.lastCayley_embedded_source_iff a ha p Y).mpr hY
  have ht : S * padicCayleyForwardMatrix p (W.lastSkewAmbientInclusion a ha p Y) ∈
      padicCayleyInverseDomain p := by
    change S * skewAdjointPadicCayleyForwardMatrix
      (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] Y) ∈ _
    rw [W.lastCayley_embedded_forward a ha p Y hY, hproduct]
    exact padicCayleyForwardMatrix_mem_inverseDomain p X.1 hX
  exact (hasFDerivAt_padicCayleyRelativeTransitionMatrix p S _ hs ht).comp Y
    (W.lastSkewAmbientInclusion a ha p).hasFDerivAt

end RationalQuadraticSpaceMatrix
