import SMSFormula.RationalCliffordSpinBlockIntrinsicStabilizer
import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange
import SMSFormula.MatrixCongruence
import SMSFormula.QuadraticReflection

/-!
# Field-valued nonisotropic block shells

For a positive-rank rational quadratic carrier `W`, the special-orthogonal
group of `W orthogonal_sum <a>` acts transitively on the nonzero shell of the
last coordinate.  The determinant correction is a reflection in an
anisotropic vector of the complement, so it fixes the last coordinate.

Fieldwise surjectivity of intrinsic general Spin onto special orthogonal then
lifts the same orbit statement to the existing intrinsic GSpin carrier.  No
adelic product, cutoff, measure, or Fourier statement occurs here.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The nonzero quadratic shell through the added final coordinate. -/
def nonisotropicLastQuadraticShell
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    Set (Fin (n + 1) → K) :=
  {v | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K v =
    algebraMap ℚ K a}

@[simp]
theorem lastCoordinateVector_mem_nonisotropicLastQuadraticShell
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    (lastCoordinateVector : Fin (n + 1) → K) ∈
      W.nonisotropicLastQuadraticShell a ha K := by
  change (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K
      (lastCoordinateVector : Fin (n + 1) → K) = algebraMap ℚ K a
  rw [show (lastCoordinateVector : Fin (n + 1) → K) =
      nonisotropicLastLineInclude (n := n) 1 by
    ext i
    cases i using Fin.lastCases <;>
      simp [lastCoordinateVector, nonisotropicLastLineInclude]]
  rw [W.nonisotropicLastExtension_quadraticForm_line]
  simp

/-- Scalar extension of the nonzero block shell. -/
def nonisotropicLastQuadraticShellMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    W.nonisotropicLastQuadraticShell a ha A →
      W.nonisotropicLastQuadraticShell a ha B :=
  fun v => ⟨fun i => f (v.1 i), by
    change (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm B
        (fun i => f (v.1 i)) = algebraMap ℚ B a
    have hmap := commutativeScalarExtensionQuadraticForm_map
      (W.nonisotropicLastExtension a ha) A f v.1
    rw [hmap, v.2]
    exact f.commutes a⟩

@[simp]
theorem coe_nonisotropicLastQuadraticShellMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (v : W.nonisotropicLastQuadraticShell a ha A) :
    (W.nonisotropicLastQuadraticShellMap a ha f v).1 = fun i => f (v.1 i) :=
  rfl

/-- The represented action of an intrinsic GSpin point on the final
coordinate, as a point of the nonzero block shell. -/
def CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint K) :
    W.nonisotropicLastQuadraticShell a ha K := by
  letI : Invertible (2 : K) := rationalAlgebraInvertibleTwo K
  let V := W.nonisotropicLastExtension a ha
  let v : Fin (n + 1) → K := z.matrixGroup.1.1.1 *ᵥ lastCoordinateVector
  refine ⟨v, ?_⟩
  let Q := V.commutativeScalarExtensionQuadraticForm K
  change Q v = algebraMap ℚ K a
  let L : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    Matrix.toLin' z.matrixGroup.1.1.1
  have hform :=
    (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) z.matrixGroup.1.1).mp
      z.matrixGroup.1.2
  have hmatrix : QuadraticForm.toMatrix' (Q.comp L) = QuadraticForm.toMatrix' Q := by
    rw [QuadraticForm.toMatrix'_comp, V.commutativeScalarExtensionQuadraticForm_toMatrix']
    rw [show LinearMap.toMatrix' L = z.matrixGroup.1.1.1 by
      dsimp only [L]
      exact LinearMap.toMatrix'_toLin' _]
    simpa [commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using hform
  have hassoc : (Q.comp L).associated = Q.associated := by
    exact (LinearMap.toMatrix₂' K).injective hmatrix
  have hlast : Q (lastCoordinateVector : Fin (n + 1) → K) = algebraMap ℚ K a :=
    W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha K
  calc
    Q v = (Q.comp L) lastCoordinateVector := rfl
    _ = (Q.comp L).associated lastCoordinateVector lastCoordinateVector :=
      ((Q.comp L).associated_eq_self_apply ℕ lastCoordinateVector).symm
    _ = Q.associated lastCoordinateVector lastCoordinateVector :=
      congrArg (fun b => b lastCoordinateVector lastCoordinateVector) hassoc
    _ = Q lastCoordinateVector := Q.associated_eq_self_apply ℕ lastCoordinateVector
    _ = algebraMap ℚ K a := hlast

/-- The intrinsic shell orbit map commutes with arbitrary scalar extension.
This is the rational-diagonal compatibility needed before assembling local
or adelic shell points. -/
@[simp]
theorem CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    W.nonisotropicLastQuadraticShellMap a ha f
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha A z) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha B
        (CliffordGeneralSpinIntrinsicPoint.mapGroupHom
          (W.nonisotropicLastExtension a ha) f z) := by
  apply Subtype.ext
  funext i
  simp only [coe_nonisotropicLastQuadraticShellMap]
  dsimp only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
    CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe,
    CliffordGeneralSpinIntrinsicPoint.mapGroupHom_apply,
    CliffordGeneralSpinIntrinsicPoint.map_matrixPoint,
    specialOrthogonalMatrixPointMap_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [show f (lastCoordinateVector x) = lastCoordinateVector x by
    cases x using Fin.lastCases <;> simp [lastCoordinateVector]]

/-- Over a rational field, every point of the nonzero block shell is the
last column of a special-orthogonal matrix.  Positive complement rank is the
exact hypothesis needed for the determinant-correcting reflection. -/
theorem exists_specialOrthogonal_mulVec_last_eq_of_mem_shell
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (v : Fin (n + 1) → K)
    (hv : v ∈ W.nonisotropicLastQuadraticShell a ha K) :
    ∃ g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup K,
      g.1.1.1 *ᵥ lastCoordinateVector = v := by
  classical
  let V := W.nonisotropicLastExtension a ha
  let B := V.specialOrthogonalMappedFormMatrix K
  let e : Fin (n + 1) → K := lastCoordinateVector
  have hBsymm : B.IsSymm := by
    dsimp [B, V, specialOrthogonalMappedFormMatrix]
    exact (W.nonisotropicLastExtension a ha).form_symm.map (algebraMap ℚ K)
  have hBdet : B.det ≠ 0 :=
    (V.specialOrthogonalMappedFormMatrix_det_isUnit K).ne_zero
  have hgram {rank : ℕ} (matrix : Matrix (Fin rank) (Fin rank) K)
      (vector : Fin rank → K) :
      matrix.toQuadraticMap' vector = PositiveDefiniteIntegralLattice.gramQuadraticValue matrix vector := by
    change Matrix.toQuadraticForm' matrix vector = _
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', PositiveDefiniteIntegralLattice.gramQuadraticValue]
  have heq : PositiveDefiniteIntegralLattice.gramQuadraticValue B e = algebraMap ℚ K a := by
    have he := W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha K
    change B.toQuadraticMap' e = algebraMap ℚ K a at he
    exact (hgram B e).symm.trans he
  have hvq : PositiveDefiniteIntegralLattice.gramQuadraticValue B v = algebraMap ℚ K a := by
    change B.toQuadraticMap' v = algebraMap ℚ K a at hv
    exact (hgram B v).symm.trans hv
  have he_ne : PositiveDefiniteIntegralLattice.gramQuadraticValue B e ≠ 0 := by
    rw [heq]
    exact (map_ne_zero (algebraMap ℚ K)).2 ha
  obtain ⟨T, hTform, hTe⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramIsometry_mulVec_eq_of_same_nonzero_value
      (by norm_num) B hBsymm hBdet e v (heq.trans hvq.symm) he_ne
  have hTdet_sq : T.1.det ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hTform
    simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
    apply mul_right_cancel₀ hBdet
    calc
      T.1.det ^ 2 * B.det = T.1.det * B.det * T.1.det := by ring
      _ = B.det := hdet
      _ = 1 * B.det := by ring
  by_cases hTdet : T.1.det = 1
  · let p : V.specialOrthogonalMatrixPoint K := ⟨T.1, hTform, hTdet⟩
    refine ⟨V.specialOrthogonalMatrixPointToGroup K p, ?_⟩
    exact hTe
  · have hTdet_neg : T.1.det = -1 := by
      have hfactor : (T.1.det - 1) * (T.1.det + 1) = 0 := by
        calc
          (T.1.det - 1) * (T.1.det + 1) = T.1.det ^ 2 - 1 := by ring
          _ = 0 := by rw [hTdet_sq]; ring
      rcases mul_eq_zero.mp hfactor with hminus | hplus
      · exact (hTdet (sub_eq_zero.mp hminus)).elim
      · exact eq_neg_of_add_eq_zero_left hplus
    let C := W.specialOrthogonalMappedFormMatrix K
    have hCsymm : C.IsSymm := by
      dsimp [C, specialOrthogonalMappedFormMatrix]
      exact W.form_symm.map (algebraMap ℚ K)
    have hCdet : C.det ≠ 0 :=
      (W.specialOrthogonalMappedFormMatrix_det_isUnit K).ne_zero
    obtain ⟨c, hc, u, hu⟩ :=
      PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_ne_zero
        C hCsymm hCdet (by norm_num)
    let w : Fin (n + 1) → K := nonisotropicLastComplementInclude u
    have hwq : PositiveDefiniteIntegralLattice.gramQuadraticValue B w = c := by
      have hcomp :=
        W.nonisotropicLastExtension_quadraticForm_complement a ha K u
      have huq : W.commutativeScalarExtensionQuadraticForm K u = c := by
        change C.toQuadraticMap' u = c
        exact (hgram C u).trans hu
      have hvalue : B.toQuadraticMap' w = c := hcomp.trans huq
      exact (hgram B w).symm.trans hvalue
    have hw : PositiveDefiniteIntegralLattice.gramQuadraticValue B w ≠ 0 := by
      rw [hwq]
      exact hc
    let Rmat := PositiveDefiniteIntegralLattice.gramReflectionMatrix B w
    let R : GL (Fin (n + 1)) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Rmat
        (PositiveDefiniteIntegralLattice.gramReflectionMatrix_det_ne_zero B hBsymm hBdet w hw)
    have hRform : R.1ᵀ * B * R.1 = B := by
      exact PositiveDefiniteIntegralLattice.gramReflectionMatrix_preserves B hBsymm w hw
    have hRdet : R.1.det = -1 := by
      exact PositiveDefiniteIntegralLattice.gramReflectionMatrix_det B w hw
    have hdot : Matrix.mulVec B w ⬝ᵥ e = 0 := by
      dsimp [B, V, w, e]
      rw [W.nonisotropicLastExtension_mappedFormMatrix]
      simp only [dotProduct, Matrix.mulVec]
      rw [Finset.sum_eq_single (Fin.last n)]
      · rw [Fin.sum_univ_castSucc]
        simp [nonisotropicLastBlockMatrix, lastCoordinateVector,
          nonisotropicLastComplementInclude]
      · intro j _ hj
        simp [lastCoordinateVector, hj]
      · simp
    have hRe : R.1 *ᵥ e = e := by
      change Matrix.mulVec (PositiveDefiniteIntegralLattice.gramReflectionMatrix B w) e = e
      rw [PositiveDefiniteIntegralLattice.gramReflectionMatrix_mulVec, hdot]
      simp
    let S : GL (Fin (n + 1)) K := T * R
    have hSform : S.1ᵀ * B * S.1 = B := by
      change (T.1 * R.1)ᵀ * B * (T.1 * R.1) = B
      rw [Matrix.transpose_mul]
      calc
        (R.1ᵀ * T.1ᵀ) * B * (T.1 * R.1) =
            R.1ᵀ * (T.1ᵀ * B * T.1) * R.1 := by noncomm_ring
        _ = B := by rw [hTform, hRform]
    have hSdet : S.1.det = 1 := by
      change (T.1 * R.1).det = 1
      rw [Matrix.det_mul, hTdet_neg, hRdet]
      ring
    have hSe : S.1 *ᵥ e = v := by
      change (T.1 * R.1) *ᵥ e = v
      rw [← Matrix.mulVec_mulVec, hRe, hTe]
    let p : V.specialOrthogonalMatrixPoint K := ⟨S.1, hSform, hSdet⟩
    refine ⟨V.specialOrthogonalMatrixPointToGroup K p, ?_⟩
    exact hSe

/-- The existing intrinsic GSpin group is transitive on the nonzero block
shell over every characteristic-zero rational field. -/
theorem CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    Function.Surjective
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha K) := by
  intro v
  obtain ⟨g, hg⟩ :=
    W.exists_specialOrthogonal_mulVec_last_eq_of_mem_shell
      a ha K v.1 v.2
  obtain ⟨z, hz⟩ :=
    CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
      (W.nonisotropicLastExtension a ha) K g
  refine ⟨z, Subtype.ext ?_⟩
  dsimp only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap]
  change z.matrixGroup = g at hz
  rw [hz]
  exact hg

/-- The fiber of the field-valued GSpin shell orbit map above the last
coordinate is exactly the complement stabilizer. -/
theorem CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_eq_last_iff
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint K) :
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha K z =
        ⟨lastCoordinateVector,
          W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha K⟩ ↔
      z ∈ W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha K := by
  rw [W.mem_nonisotropicLastComplementGeneralSpinStabilizerSubgroup_iff]
  constructor
  · intro hz
    apply Subtype.ext_iff.mp at hz
    unfold IsNonisotropicLastBlockGeneralSpinFixedPoint
    unfold FixesLastCoordinate
    simpa only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
      CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using hz
  · intro hz
    apply Subtype.ext
    unfold IsNonisotropicLastBlockGeneralSpinFixedPoint at hz
    unfold FixesLastCoordinate at hz
    simpa only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
      CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using hz

/-- Rational specialization of fieldwise intrinsic GSpin shell
transitivity. -/
theorem CliffordGeneralSpinIntrinsicPoint.rational_nonisotropicLastShellOrbitMap_surjective
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Function.Surjective
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha ℚ) :=
  CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
    W a ha ℚ

end RationalQuadraticSpaceMatrix
