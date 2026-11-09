import SMSFormula.QuadraticPadicCayleyLocalVolume
import SMSFormula.QuadraticSquareBranchRelativeTopForm

/-! The local Leray measure is the square-branch fiber measure. The
anisotropic complement of the last coordinate vector is read in lower
coordinates (`lastOrthogonalLowerEquiv`), and the square-branch fiber
measure at `x_old` for the value `a`, built on the unit Haar of those
coordinates, integrates tests of the lower coordinates against the branch
Jacobian `‖2 a y_last‖⁻¹`. On every sufficiently small exact rectangle whose
base orbit point has its last coordinate in the unit-square source, the orbit
points lie on that branch with `‖y_last‖ = ‖s‖`, so the local orbit identity
reads

`∫_{Cayley image} g(lower(h x_old)) d(higher Haar) = |r| · (lower Haar)(lower chart image) · ∫ 1_{φ(B)} g ∘ lower d(fiber measure)`.

The fiber measure carries the isometry transport already proved for the
square branch, which is the invariance input for the orbit counting. No chart,
section, square root or baseline is chosen: the unit-square branch and its
chart are the ones. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
variable (p : ℕ) [Fact (Nat.Prime p)]

section LowerCoordinates

/-- The zero-extended lower coordinates are orthogonal to the last vector. -/
theorem snoc_zero_mem_lastOrthogonal (w : Fin n → ℚ_[p]) :
    (Fin.snoc w 0 : Fin (n+1) → ℚ_[p]) ∈
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal
        lastCoordinateVector := by
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
  rw [QuadraticMap.mem_anisotropicOrthogonal_iff]
  change q.associated lastCoordinateVector (Fin.snoc w 0) = 0
  have hp : q.polarBilin lastCoordinateVector (Fin.snoc w 0 : Fin (n+1) → ℚ_[p]) = 0 := by
    rw [W.nonisotropicLastExtension_polar_last]
    simp
  have h := congrArg (fun B : LinearMap.BilinForm ℚ_[p] (Fin (n+1) → ℚ_[p]) ↦
    B lastCoordinateVector (Fin.snoc w 0)) (q.two_nsmul_associated ℕ)
  simp only [two_smul, LinearMap.add_apply] at h
  rw [hp] at h
  exact add_self_eq_zero.mp h

/-- The anisotropic complement of the last vector in lower coordinates. -/
def lastOrthogonalLowerEquiv :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal
        lastCoordinateVector ≃L[ℚ_[p]] (Fin n → ℚ_[p]) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z i ↦ z.1 i.castSucc
      invFun := fun w ↦ ⟨Fin.snoc w 0, W.snoc_zero_mem_lastOrthogonal a ha p w⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun z ↦ Subtype.ext (funext fun i ↦ by
        cases i using Fin.lastCases with
        | last => simp [W.lastOrthogonal_coordinate_zero a ha z]
        | cast i => simp)
      right_inv := fun w ↦ funext fun i ↦ by simp }

@[simp] theorem lastOrthogonalLowerEquiv_apply
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal
        lastCoordinateVector) (i : Fin n) :
    W.lastOrthogonalLowerEquiv a ha p z i = z.1 i.castSucc := rfl

@[simp] theorem lastOrthogonalLowerEquiv_symm_apply (w : Fin n → ℚ_[p]) :
    ((W.lastOrthogonalLowerEquiv a ha p).symm w).1 = Fin.snoc w 0 := rfl

/-- The quadratic value splits along the last coordinate. -/
theorem nonisotropicLastExtension_quadratic_split (y : Fin (n+1) → ℚ_[p]) :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y =
      (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
          (Fin.snoc (fun i ↦ y i.castSucc) 0) +
        y (Fin.last n) * y (Fin.last n) * algebraMap ℚ ℚ_[p] a := by
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
  have hy : y = Fin.snoc (fun i ↦ y i.castSucc) 0 + y (Fin.last n) • lastCoordinateVector := by
    ext i
    cases i using Fin.lastCases <;> simp [lastCoordinateVector]
  have hpol : QuadraticMap.polar q (Fin.snoc (fun i ↦ y i.castSucc) 0)
      (y (Fin.last n) • lastCoordinateVector) = 0 := by
    rw [QuadraticMap.polar_smul_right, ← QuadraticMap.polarBilin_apply_apply,
      W.nonisotropicLastExtension_polar_normal]
    simp
  have hadd : q (Fin.snoc (fun i ↦ y i.castSucc) 0 + y (Fin.last n) • lastCoordinateVector) =
      q (Fin.snoc (fun i ↦ y i.castSucc) 0) + q (y (Fin.last n) • lastCoordinateVector) +
        QuadraticMap.polar q (Fin.snoc (fun i ↦ y i.castSucc) 0)
          (y (Fin.last n) • lastCoordinateVector) := by
    rw [QuadraticMap.polar]; ring
  conv_lhs => rw [hy]
  change q _ = _
  rw [hadd, hpol, add_zero, QuadraticMap.map_smul, W.nonisotropicLastExtension_quadratic_last,
    smul_eq_mul]

local instance lbPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance lbPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The branch point has the transverse point's lower coordinates. -/
theorem padicSquareBranchFiberMap_lower (value : ℚ_[p])
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain
      p lastCoordinateVector value) (i : Fin n) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap
      p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value z).1
        i.castSucc = z.1.1 i.castSucc := by
  simp [padicSquareBranchFiberMap, lastCoordinateVector]

/-- The fiber measure in lower coordinates: built on the unit Haar of the
lower coordinates, it integrates every measurable test of the lower coordinates
against the branch Jacobian over the branch domain. -/
theorem lintegral_lastSquareBranchFiberMeasure_lower (value : ℚ_[p])
    (f : (Fin n → ℚ_[p]) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f (fun i ↦ y.1 i.castSucc)
        ∂((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
          p lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) value =
      ∫⁻ w in (W.lastOrthogonalLowerEquiv a ha p).symm ⁻¹'
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain
            p lastCoordinateVector value,
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberJacobianInverse
            p lastCoordinateVector value ((W.lastOrthogonalLowerEquiv a ha p).symm w) * f w
        ∂(Padic.unitHaar p (Fin n)) := by
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
  let e := W.lastOrthogonalLowerEquiv a ha p
  have hlowerm : Measurable (fun y : {vector : Fin (n+1) → ℚ_[p] // q vector = value} ↦
      f (fun i ↦ y.1 i.castSucc)) :=
    hf.comp (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply _).comp measurable_subtype_coe)
  rw [QuadraticMap.lintegral_padicSquareBranchFiberMeasure p _ _ _ _ _ _ hlowerm]
  have hdom : MeasurableSet (q.padicSquareBranchFiberDomain p lastCoordinateVector value) :=
    (q.isOpen_padicSquareBranchFiberDomain p lastCoordinateVector value).measurableSet
  have hF : Measurable (fun t : q.anisotropicOrthogonal lastCoordinateVector ↦
      q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector value t * f (e t)) :=
    (q.measurable_padicSquareBranchFiberJacobianInverse p lastCoordinateVector value).mul
      (hf.comp e.continuous.measurable)
  calc _ = ∫⁻ z : q.padicSquareBranchFiberDomain p lastCoordinateVector value,
        (fun t : q.anisotropicOrthogonal lastCoordinateVector ↦
          q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector value t * f (e t)) z.1
        ∂Measure.comap Subtype.val (Measure.map e.symm (Padic.unitHaar p (Fin n))) := by
        apply lintegral_congr
        intro z
        congr 2
        funext i
        exact W.padicSquareBranchFiberMap_lower a ha p value z i
    _ = ∫⁻ t in q.padicSquareBranchFiberDomain p lastCoordinateVector value,
        q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector value t * f (e t)
        ∂Measure.map e.symm (Padic.unitHaar p (Fin n)) := by
        exact lintegral_subtype_comap hdom (fun t : q.anisotropicOrthogonal lastCoordinateVector ↦
          q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector value t * f (e t))
    _ = _ := by
        rw [setLIntegral_map hdom hF e.symm.continuous.measurable]
        simp only [ContinuousLinearEquiv.apply_symm_apply]
        rfl

end LowerCoordinates

/-- Squares of unit-square source points lie in the target. -/
theorem _root_.Rat.sq_mem_padicUnitSquareScalarTarget {t : ℚ_[p]}
    (ht : t ∈ Rat.padicUnitSquareScalarSource p) : t ^ 2 ∈ Rat.padicUnitSquareScalarTarget p := by
  obtain ⟨u, hu, rfl⟩ := ht
  exact ⟨Rat.unitSquareIdentityChart ℚ_[p] u, (Rat.unitSquareIdentityChart ℚ_[p]).map_source hu,
    by rw [Rat.unitSquareIdentityChart_apply]; rfl⟩

/-- The identity base value lies in the unit-square source. -/
theorem _root_.Rat.one_mem_padicUnitSquareScalarSource :
    (1 : ℚ_[p]) ∈ Rat.padicUnitSquareScalarSource p :=
  ⟨1, Rat.one_mem_unitSquareIdentityChart_source _, rfl⟩

/-- Special-orthogonal matrices preserve the quadratic value. -/
theorem commutativeScalarExtensionQuadraticForm_mulVec_of_mem
    (V : RationalQuadraticSpaceMatrix (n+1)) {M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]}
    (hM : M ∈ specialOrthogonalMatrixSet (V.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (y : Fin (n+1) → ℚ_[p]) :
    V.commutativeScalarExtensionQuadraticForm ℚ_[p] (M *ᵥ y) =
      V.commutativeScalarExtensionQuadraticForm ℚ_[p] y := by
  simp only [commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
  exact gramQuadraticValue_mulVec_of_congr _ _
    (Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM.2]; exact one_ne_zero))
    ((Matrix.formPreservingConstraint_eq_zero_iff _ _).mp hM.1) y

section OrbitBranch

local instance obPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance obPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance obSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance obSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance obLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance obLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance obGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance obGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance obLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance obLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance obLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance obLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance obHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance obHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
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

set_option maxHeartbeats 1600000 in
include hSs hSO hproduct hs hv in
/-- The local Leray measure is the square-branch fiber measure: when the base
orbit point's last coordinate lies in the unit-square source, on every
sufficiently small horizontal ball the Leray factor times the lower unit
Haar on the orbit image is the fiber measure at `x_old` for the value `a`
(read in lower coordinates). -/
theorem lastCayleyProduct_exists_forall_leray_eq_fiberMeasure
    (hsrc : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ g : (Fin n → ℚ_[p]) → ℝ≥0∞, Measurable g →
        (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
            ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
              lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
          ∫⁻ y in lastCayleyHorizontalLower p S z v '' closedBall 0 r, g y ∂(Padic.unitHaar p (Fin n)) =
        ∫⁻ y, (lastCayleyHorizontalLower p S z v '' closedBall 0 r).indicator g
            (fun i ↦ y.1 i.castSucc)
          ∂((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
                p lastCoordinateVector
                (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
                (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n)))
                (algebraMap ℚ ℚ_[p] a) := by
  classical
  set q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] with hq
  set e := W.lastOrthogonalLowerEquiv a ha p with he
  set s := ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) with hsdef
  have ha' : algebraMap ℚ ℚ_[p] a ≠ 0 := (map_ne_zero _).mpr ha
  obtain ⟨δ4, hδ4, hH⟩ := lastCayleyHorizontalLower_exists_forall_lintegral_image p v hv hSs
  -- the orbit point, continuous at the base coefficient
  set yv : (Fin n → ℚ_[p]) → (Fin (n+1) → ℚ_[p]) :=
    fun c ↦ S (z + ∑ i, c i • v i) *ᵥ lastCoordinateVector with hyv
  have hlin : Tendsto (fun c : Fin n → ℚ_[p] ↦ z + ∑ i, c i • v i) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun c : Fin n → ℚ_[p] ↦ z + ∑ i, c i • v i) := by fun_prop
    simpa using hc.tendsto 0
  have hy0 : yv 0 (Fin.last n) = s := by
    simp only [hyv, hsdef, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
      cayleyOrbitVectorEquiv_apply]
    rw [← hproduct, ← Matrix.mulVec_mulVec, show fixLastBlockMatrix
        (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) *ᵥ
        (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]
  have hylast : Tendsto (fun c ↦ yv c (Fin.last n)) (𝓝 0) (𝓝 s) := by
    rw [← hy0]
    have hS : Tendsto (fun c : Fin n → ℚ_[p] ↦ S (z + ∑ i, c i • v i)) (𝓝 0) (𝓝 (S z)) :=
      hSs.continuousAt.tendsto.comp hlin
    have hmv0 : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] ↦
        M *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) :=
      continuous_id.matrix_mulVec continuous_const
    have hmv : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] ↦
        (M *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) (Fin.last n)) :=
      (continuous_apply (Fin.last n)).comp hmv0
    have h0 : S z = S (z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i) := by simp
    rw [h0] at hS
    exact (hmv.tendsto _).comp hS
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hN : {c : Fin n → ℚ_[p] | S (z + ∑ i, c i • v i) ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) ∧
      yv c (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p ∧
      ‖yv c (Fin.last n) - s‖ < ‖s‖} ∈ 𝓝 0 := by
    refine (hlin.eventually hSO).and ((hylast.eventually
      ((Rat.isOpen_padicUnitSquareScalarSource p).mem_nhds hsrc)).and ?_)
    have := hylast.eventually (Metric.ball_mem_nhds s hspos)
    filter_upwards [this] with c hc
    simpa [Metric.mem_ball, dist_eq_norm] using hc
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨min δ4 ε, lt_min hδ4 hε, fun r hr hrδ g hg ↦ ?_⟩
  have hr4 : r < δ4 := hrδ.trans_le (min_le_left _ _)
  have hr3 : r < ε := hrδ.trans_le (min_le_right _ _)
  obtain ⟨-, hcontφ, -⟩ := hH r hr hr4
  set D := lastCayleyHorizontalLower p S z v '' closedBall 0 r with hD
  have hDm : MeasurableSet D :=
    ((isCompact_closedBall (0 : Fin n → ℚ_[p]) r).image_of_continuousOn hcontφ).isClosed.measurableSet
  -- on the image the orbit points lie on the branch with the base norm
  have hpt : ∀ w ∈ D, e.symm w ∈ q.padicSquareBranchFiberDomain p lastCoordinateVector
        (algebraMap ℚ ℚ_[p] a) ∧
      q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector (algebraMap ℚ ℚ_[p] a)
        (e.symm w) = (‖2 * algebraMap ℚ ℚ_[p] a * s‖₊ : ℝ≥0∞)⁻¹ := by
    rintro w ⟨c, hc, rfl⟩
    obtain ⟨hSOc, hsrcc, hnormc⟩ := hεN (closedBall_subset_ball hr3 hc)
    set y := yv c with hy
    have hval : q y = algebraMap ℚ ℚ_[p] a := by
      rw [hy, hyv]
      change q (S (z + ∑ i, c i • v i) *ᵥ lastCoordinateVector) = _
      rw [commutativeScalarExtensionQuadraticForm_mulVec_of_mem p _ hSOc,
        W.nonisotropicLastExtension_quadratic_last]
    have hsplit := W.nonisotropicLastExtension_quadratic_split a ha p y
    have hparam : (algebraMap ℚ ℚ_[p] a -
        q.orthogonalRestriction lastCoordinateVector
          (e.symm (lastCayleyHorizontalLower p S z v c))) / q lastCoordinateVector =
        y (Fin.last n) ^ 2 := by
      rw [QuadraticMap.orthogonalRestriction_apply, W.nonisotropicLastExtension_quadratic_last]
      change (algebraMap ℚ ℚ_[p] a - q (Fin.snoc (fun i ↦ y i.castSucc) 0)) / _ = _
      rw [div_eq_iff ha']
      have : q (Fin.snoc (fun i ↦ y i.castSucc) 0) =
          algebraMap ℚ ℚ_[p] a - y (Fin.last n) * y (Fin.last n) * algebraMap ℚ ℚ_[p] a := by
        have hval' := hval
        rw [hsplit] at hval'
        linear_combination hval'
      rw [this]; ring
    have hdomc : e.symm (lastCayleyHorizontalLower p S z v c) ∈
        q.padicSquareBranchFiberDomain p lastCoordinateVector (algebraMap ℚ ℚ_[p] a) := by
      change (algebraMap ℚ ℚ_[p] a - q.orthogonalRestriction lastCoordinateVector
        (e.symm (lastCayleyHorizontalLower p S z v c))) / q lastCoordinateVector ∈
          Rat.padicUnitSquareScalarTarget p
      rw [hparam]
      exact Rat.sq_mem_padicUnitSquareScalarTarget p hsrcc
    refine ⟨hdomc, ?_⟩
    have hinv : Rat.padicUnitSquareTargetSupportedInverse p (y (Fin.last n) ^ 2) = y (Fin.last n) := by
      rw [Rat.padicUnitSquareTargetSupportedInverse_eq p (Rat.sq_mem_padicUnitSquareScalarTarget p hsrcc),
        Rat.padicUnitSquareScalarInverse_sq p hsrcc]
    have hnorm : ‖y (Fin.last n)‖ = ‖s‖ := Padic.norm_eq_of_norm_sub_lt_right hnormc
    unfold padicSquareBranchFiberJacobianInverse
    rw [hparam, hinv, W.nonisotropicLastExtension_quadratic_last]
    have hnn : ‖2 * algebraMap ℚ ℚ_[p] a * y (Fin.last n)‖₊ = ‖2 * algebraMap ℚ ℚ_[p] a * s‖₊ := by
      rw [nnnorm_mul, nnnorm_mul (2 * algebraMap ℚ ℚ_[p] a) s]
      congr 1
      exact Subtype.ext hnorm
    rw [hnn]
  have hDdom : D ⊆ e.symm ⁻¹' q.padicSquareBranchFiberDomain p lastCoordinateVector
      (algebraMap ℚ ℚ_[p] a) := fun w hw ↦ (hpt w hw).1
  rw [W.lintegral_lastSquareBranchFiberMeasure_lower a ha p _ _ (hg.indicator hDm)]
  have hind : ∀ w, q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector
      (algebraMap ℚ ℚ_[p] a) (e.symm w) * D.indicator g w =
      D.indicator (fun w ↦ q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector
        (algebraMap ℚ ℚ_[p] a) (e.symm w) * g w) w := by
    intro w
    by_cases hw : w ∈ D
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
  have hL : (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
      ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
        lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) =
      (‖2 * algebraMap ℚ ℚ_[p] a * s‖₊ : ℝ≥0∞)⁻¹ := by
    rw [← hsdef, nnnorm_div, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, one_div]
    exact ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr
      (mul_ne_zero (mul_ne_zero two_ne_zero ha') hs))
  rw [lintegral_congr hind]
  rw [setLIntegral_indicator hDm, Set.inter_eq_left.mpr hDdom,
    setLIntegral_congr_fun hDm (f := fun w ↦ q.padicSquareBranchFiberJacobianInverse p
        lastCoordinateVector (algebraMap ℚ ℚ_[p] a) (e.symm w) * g w)
      (g := fun w ↦ (‖2 * algebraMap ℚ ℚ_[p] a * s‖₊ : ℝ≥0∞)⁻¹ * g w)
      (fun w hw ↦ by dsimp only; rw [(hpt w hw).2]),
    lintegral_const_mul _ hg, hL]


set_option maxHeartbeats 1600000 in
include hSs hSO hY hproduct hs hv in
/-- Local orbit identity against the square-branch fiber measure: when the
base orbit point's last coordinate lies in the unit-square source, on every
sufficiently small exact rectangle the higher group-Haar integral of
`g(lower(h x_old))` over the Cayley image equals `|r|` times the lower group-Haar
mass of the lower chart image times the integral of `1_{φ(B)} · g` in lower
coordinates against the square-branch fiber measure at `x_old` for the value
`a`, built on the unit Haar of the lower coordinates. -/
theorem lastCayleyProduct_exists_forall_lintegral_orbit_fiberMeasure
    (hsrc : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ g : (Fin n → ℚ_[p]) → ℝ≥0∞, Measurable g →
        ∫⁻ x in Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))),
            g (fun j ↦ ((x.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ
              lastCoordinateVector) j.castSucc)
            ∂(padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
              ((fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦
                  ((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 X').1)) ''
                (Subtype.val ⁻¹' ((skewAdjointPadicCoordinateEquiv W.pairingMatrix p) ⁻¹'
                  closedBall (skewAdjointPadicCoordinateEquiv W.pairingMatrix p Y) r))) *
            ∫⁻ y, (lastCayleyHorizontalLower p S z v '' closedBall 0 r).indicator g
                (fun i ↦ y.1 i.castSucc)
              ∂((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
                p lastCoordinateVector
                (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
                (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n)))
                (algebraMap ℚ ℚ_[p] a) := by
  obtain ⟨δ0, hδ0, horbit⟩ := W.lastCayleyProduct_exists_forall_lintegral_orbit p a ha S dS z hSs
    hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ1, hδ1, hLF⟩ := W.lastCayleyProduct_exists_forall_leray_eq_fiberMeasure a ha p S dS z hSs
    hSO Y X hX hproduct v hs hv hsrc
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun r hr hrδ g hg ↦ ?_⟩
  rw [horbit r hr (hrδ.trans_le (min_le_left _ _)) g hg,
    ← hLF r hr (hrδ.trans_le (min_le_right _ _)) g hg]
  ring

end OrbitBranch

end RationalQuadraticSpaceMatrix
