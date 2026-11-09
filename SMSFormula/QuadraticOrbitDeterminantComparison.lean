import SMSFormula.QuadraticOrbitRelativeTopForm
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# The group/stabilizer determinant comparison in the supplied block

Use the lower tangent embedding and explicit orbit lift. Their sum is
an isomorphism; no complement, basis, chart or group section is selected.
The fixed group forms retain their coordinate change determinant.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
variable (K : Type*) [Field K] [CharZero K]

/-- The old orbit lift of the old last-coordinate tangent. -/
def lastOrbitLift : (Fin n → K) →ₗ[K]
    skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K) where
  toFun y := (W.nonisotropicLastExtension a ha).orbitPolarTangentLiftLinearMap K
    lastCoordinateVector (W.nonisotropicLastPolarTangent a ha y)
  map_add' y z := by
    change (W.nonisotropicLastExtension a ha).orbitPolarTangentLiftLinearMap K
      lastCoordinateVector (W.nonisotropicLastPolarTangent a ha (y+z)) = _
    rw [show W.nonisotropicLastPolarTangent a ha (y+z) =
      W.nonisotropicLastPolarTangent a ha y + W.nonisotropicLastPolarTangent a ha z by
        apply Subtype.ext; ext i; cases i using Fin.lastCases <;> simp [nonisotropicLastPolarTangent]]
    exact map_add _ _ _
  map_smul' c y := by
    rw [show W.nonisotropicLastPolarTangent a ha (c • y) =
      c • W.nonisotropicLastPolarTangent a ha y by
        apply Subtype.ext; ext i; cases i using Fin.lastCases <;> simp [nonisotropicLastPolarTangent]]
    exact map_smul _ _ _

theorem lastOrbitLift_mulVec (y : Fin n → K) :
    mulVec (W.lastOrbitLift a ha K y).1 lastCoordinateVector = Fin.snoc y 0 := by
  have h := (W.nonisotropicLastExtension a ha).orbitPolarTangentLinearMap_lift K
    lastCoordinateVector
    (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
    (W.nonisotropicLastPolarTangent a ha y)
  exact congrArg Subtype.val h

/-- Upper entries of the actual final column. -/
def lastOrbitProjection :
    skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K) →ₗ[K]
        (Fin n → K) where
  toFun A i := A.1 i.castSucc (Fin.last n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lastOrbitProjection_lift (y : Fin n → K) :
    W.lastOrbitProjection a ha K (W.lastOrbitLift a ha K y) = y := by
  have h := W.lastOrbitLift_mulVec a ha K y
  rw [lastCoordinateVector, mulVec_single_one] at h
  funext i
  simpa [lastOrbitProjection] using congrFun h i.castSucc

theorem lastOrbitProjection_embed
    (z : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K)) :
    W.lastOrbitProjection a ha K (W.nonisotropicLastSkewAdjointEmbed a ha K z) = 0 := by
  ext i
  simp [lastOrbitProjection]

theorem lastOrbitProjection_ker
    (A : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K)) :
    W.lastOrbitProjection a ha K A = 0 ↔ A ∈ W.nonisotropicLastSkewAdjointFiber a ha K := by
  constructor
  · intro h i
    cases i using Fin.lastCases with
    | cast i => exact congrFun h i
    | last =>
      have hp := ((W.nonisotropicLastExtension a ha).orbitPolarTangentLinearMap K
        lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        A).2
      change ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin
        lastCoordinateVector (mulVec A.1 lastCoordinateVector) = 0 at hp
      rw [W.nonisotropicLastExtension_polar_last, lastCoordinateVector, mulVec_single_one] at hp
      exact (mul_eq_zero.mp hp).resolve_left
        (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha))
  · intro h
    funext i
    exact h i.castSucc

/-- The map in the old tangent exact sequence, with the old explicit lift. -/
def lastOrbitAssembly :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K) × (Fin n → K)) →ₗ[K]
    skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K) :=
  (W.nonisotropicLastSkewAdjointEmbed a ha K).coprod (W.lastOrbitLift a ha K)

theorem lastOrbitAssembly_bijective : Function.Bijective (W.lastOrbitAssembly a ha K) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨z,y⟩ h
    have hp := congrArg (W.lastOrbitProjection a ha K) h
    have hy : y = 0 := by
      simpa [lastOrbitAssembly, LinearMap.coprod_apply, map_add,
        W.lastOrbitProjection_embed, W.lastOrbitProjection_lift] using hp
    have hz : W.nonisotropicLastSkewAdjointEmbed a ha K z = 0 := by
      simpa [lastOrbitAssembly, LinearMap.coprod_apply, hy] using h
    have hz' : z = 0 := by
      have he := congrArg (fun X ↦ upperLeftBlock X.1) hz
      apply Subtype.ext
      ext i j
      simpa [upperLeftBlock] using congrFun (congrFun he i) j
    simp [hy,hz']
  · intro A
    let y := W.lastOrbitProjection a ha K A
    have hr : A - W.lastOrbitLift a ha K y ∈ W.nonisotropicLastSkewAdjointFiber a ha K :=
      (W.lastOrbitProjection_ker a ha K _).mp (by simp [map_sub, W.lastOrbitProjection_lift, y])
    let z := W.nonisotropicLastSkewAdjointFiberExtract a ha K ⟨_, hr⟩
    refine ⟨(z,y), ?_⟩
    have he := congrArg Subtype.val
      (W.nonisotropicLastSkewAdjointFiberEmbed_extract a ha K ⟨_,hr⟩)
    change W.nonisotropicLastSkewAdjointEmbed a ha K z = A - W.lastOrbitLift a ha K y at he
    change W.nonisotropicLastSkewAdjointEmbed a ha K z + W.lastOrbitLift a ha K y = A
    rw [he]
    exact sub_add_cancel _ _

/-- An equivalence derived from the already fixed embedding and lift. -/
def lastOrbitAssemblyEquiv := LinearEquiv.ofBijective (W.lastOrbitAssembly a ha K)
  (W.lastOrbitAssembly_bijective a ha K)

/-- Assemble the scalar-extended lower basis and coordinate basis.
This derived frame does not replace the fixed ambient group basis. -/
def lastOrbitFrame :=
  ((skewAdjointScalarExtensionFinBasis (K := K) W.pairingMatrix).prod
    (Pi.basisFun K (Fin n))).map (W.lastOrbitAssemblyEquiv a ha K)

theorem lastOrbit_finrank :
    Module.finrank ℚ (W.nonisotropicLastExtension a ha).skewAdjointTangent =
      Module.finrank ℚ W.skewAdjointTangent + n := by
  have h := Module.finrank_eq_card_basis (W.lastOrbitFrame a ha ℚ)
  simpa using h

/-- Canonical index concatenation, lower tangent first. -/
def lastOrbitIndexEquiv :
    Fin (Module.finrank ℚ (W.nonisotropicLastExtension a ha).skewAdjointTangent) ≃
      (Fin (Module.finrank ℚ W.skewAdjointTangent) ⊕ Fin n) :=
  (finCongr (W.lastOrbit_finrank a ha)).trans finSumFinEquiv.symm

/-- The existing group determinant form with only its indices concatenated. -/
def lastOrbitGroupForm :=
  (skewAdjointScalarExtensionDetForm (K := K) (W.nonisotropicLastExtension a ha).pairingMatrix).domDomCongr
    (W.lastOrbitIndexEquiv a ha)

/-- The actual old-basis determinant, not normalized to one. -/
def lastOrbitDeterminant : K :=
  W.lastOrbitGroupForm a ha K (W.lastOrbitFrame a ha K)

theorem lastOrbitDeterminant_ne_zero : W.lastOrbitDeterminant a ha K ≠ 0 := by
  apply (AlternatingMap.map_basis_ne_zero_iff (W.lastOrbitFrame a ha K) _).mpr
  intro h
  apply skewAdjointScalarExtensionDetForm_ne_zero (K := K)
    (W.nonisotropicLastExtension a ha).pairingMatrix
  change (skewAdjointScalarExtensionDetForm (K := K)
    (W.nonisotropicLastExtension a ha).pairingMatrix).domDomCongr
      (W.lastOrbitIndexEquiv a ha) = 0 at h
  exact (AlternatingMap.domDomCongr_eq_zero_iff (W.lastOrbitIndexEquiv a ha) _).mp h

omit [CharZero K] in
private theorem prodBasis_det
    {I J E F : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    (b : Module.Basis I K E) (b' : Module.Basis J K F) (u : I → E) (v : J → E) (w : J → F) :
    (b.prod b').det (Sum.elim (fun i ↦ (u i,0)) (fun j ↦ (v j,w j))) = b.det u * b'.det w := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply]
  rw [show (b.prod b').toMatrix (Sum.elim (fun i ↦ (u i,0)) (fun j ↦ (v j,w j))) =
    Matrix.fromBlocks (b.toMatrix u) (b.toMatrix v) 0 (b'.toMatrix w) by
      ext i j
      cases i <;> cases j <;> simp [Module.Basis.toMatrix_apply, Matrix.fromBlocks]]
  exact Matrix.det_fromBlocks_zero₂₁ _ _ _

/-- Evaluation of the ambient form on lower vectors followed by orbit
lifts, allowing arbitrary stabilizer additions to the transverse lifts.
The block upper-triangular determinant keeps the same change-of-frame factor. -/
theorem lastOrbitGroupForm_apply_vertical_add
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (v : Fin n → skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (w : Fin n → Fin n → K) :
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
        (fun j ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (v j) + W.lastOrbitLift a ha K (w j))) =
      W.lastOrbitDeterminant a ha K *
        skewAdjointScalarExtensionDetForm (K := K) W.pairingMatrix u *
          (Pi.basisFun K (Fin n)).det w := by
  have h := congrArg (fun f ↦ f
    (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
      (fun j ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (v j) + W.lastOrbitLift a ha K (w j))))
    ((W.lastOrbitGroupForm a ha K).eq_smul_basis_det (W.lastOrbitFrame a ha K))
  dsimp only at h
  rw [AlternatingMap.smul_apply, smul_eq_mul] at h
  refine h.trans ?_
  change _ * (W.lastOrbitFrame a ha K).det _ = _
  rw [lastOrbitFrame, Module.Basis.det_map]
  have he : (W.lastOrbitAssemblyEquiv a ha K).symm ∘
      Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
        (fun j ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (v j) + W.lastOrbitLift a ha K (w j)) =
      Sum.elim (fun i ↦ (u i,0)) (fun j ↦ (v j,w j)) := by
    funext i
    apply (W.lastOrbitAssemblyEquiv a ha K).injective
    cases i <;> simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
      LinearEquiv.apply_symm_apply]
    · simp [lastOrbitAssemblyEquiv, lastOrbitAssembly, LinearMap.coprod_apply]
    · rfl
  exact (congrArg (fun v ↦ W.lastOrbitDeterminant a ha K *
    ((skewAdjointScalarExtensionFinBasis (K := K) W.pairingMatrix).prod
      (Pi.basisFun K (Fin n))).det v) he).trans
        ((congrArg (fun c ↦ W.lastOrbitDeterminant a ha K * c)
          (prodBasis_det K (skewAdjointScalarExtensionFinBasis (K := K) W.pairingMatrix)
            (Pi.basisFun K (Fin n)) u v w)).trans (mul_assoc _ _ _).symm)

/-- Evaluation of the ambient form on lower vectors followed by orbit
lifts, with the change-of-frame determinant as an explicit factor. -/
theorem lastOrbitGroupForm_apply
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (w : Fin n → Fin n → K) :
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
        (fun j ↦ W.lastOrbitLift a ha K (w j))) =
      W.lastOrbitDeterminant a ha K *
        skewAdjointScalarExtensionDetForm (K := K) W.pairingMatrix u *
          (Pi.basisFun K (Fin n)).det w := by
  simpa using W.lastOrbitGroupForm_apply_vertical_add a ha K u (fun _ ↦ 0) w

/-- Every transverse frame with the same orbit projection has the same
ambient determinant after the lower frame. The vertical remainder is recovered
by the stabilizer extraction, without choosing a lift or a complement. -/
theorem lastOrbitGroupForm_eq_of_projection_eq
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (Z : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K))
    (w : Fin n → Fin n → K)
    (hZ : ∀ j, W.lastOrbitProjection a ha K (Z j) = w j) :
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i)) Z) =
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
        (fun j ↦ W.lastOrbitLift a ha K (w j))) := by
  have hr (j) : Z j - W.lastOrbitLift a ha K (w j) ∈
      W.nonisotropicLastSkewAdjointFiber a ha K :=
    (W.lastOrbitProjection_ker a ha K _).mp (by
      rw [map_sub, hZ j, W.lastOrbitProjection_lift, sub_self])
  let v := fun j ↦ W.nonisotropicLastSkewAdjointFiberExtract a ha K ⟨_, hr j⟩
  have he : Z = fun j ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (v j) +
      W.lastOrbitLift a ha K (w j) := by
    funext j
    have he := congrArg Subtype.val
      (W.nonisotropicLastSkewAdjointFiberEmbed_extract a ha K ⟨_,hr j⟩)
    change W.nonisotropicLastSkewAdjointEmbed a ha K (v j) =
      Z j - W.lastOrbitLift a ha K (w j) at he
    rw [he, sub_add_cancel]
  rw [he, W.lastOrbitGroupForm_apply_vertical_add, W.lastOrbitGroupForm_apply]

/-- The group/stabilizer-to-vector/value factor in the existing bases.
This is an explicit nonzero determinant expression, not the assertion one. -/
def lastOrbitGaugeRatio : K := W.lastOrbitDeterminant a ha K /
  ((-1 : K)^n / (2 * algebraMap ℚ K a))

theorem lastOrbitGaugeRatio_ne_zero : W.lastOrbitGaugeRatio a ha K ≠ 0 :=
  div_ne_zero (W.lastOrbitDeterminant_ne_zero a ha K)
    (div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha)))

/-- The actual ambient group form equals the explicit ratio times the
lower-group form times the relative coordinate form. Lower tangent first. -/
theorem lastOrbitGroupForm_eq_ratio_mul_relative
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (w : Fin n → Fin n → K) :
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i))
        (fun j ↦ W.lastOrbitLift a ha K (w j))) =
      W.lastOrbitGaugeRatio a ha K *
        skewAdjointScalarExtensionDetForm (K := K) W.pairingMatrix u *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm
            lastCoordinateVector (fun i ↦ W.nonisotropicLastPolarTangent a ha (w i)) := by
  rw [W.lastOrbitGroupForm_apply, W.relativeCoordinateTopForm_nonisotropicLastExtension]
  dsimp only [lastOrbitGaugeRatio]
  field_simp [(map_ne_zero (algebraMap ℚ K)).mpr ha]
  exact (mul_div_cancel_right₀ _ ((map_ne_zero (algebraMap ℚ K)).mpr ha)).symm

/-- The group/relative-form identity accepts arbitrary transverse lifts.
Only the lower vectors are prescribed; vertical additions to the transverse
vectors cancel in the top determinant, without changing the rational ratio. -/
theorem lastOrbitGroupForm_eq_ratio_mul_orbitRelative
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix K))
    (Z : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K)) :
    W.lastOrbitGroupForm a ha K
      (Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha K (u i)) Z) =
      W.lastOrbitGaugeRatio a ha K *
        skewAdjointScalarExtensionDetForm (K := K) W.pairingMatrix u *
        (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm K
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) Z := by
  let w := fun j ↦ W.lastOrbitProjection a ha K (Z j)
  rw [W.lastOrbitGroupForm_eq_of_projection_eq a ha K u Z w (fun _ ↦ rfl),
    W.lastOrbitGroupForm_eq_ratio_mul_relative]
  congr 1
  symm
  calc
    _ = (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm K
        lastCoordinateVector _ (fun j ↦ W.lastOrbitLift a ha K (w j)) := by
      apply (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm_eq_of_same_action
      intro j
      have hr := (W.lastOrbitProjection_ker a ha K (Z j - W.lastOrbitLift a ha K (w j))).mp
        (by simp [map_sub, W.lastOrbitProjection_lift, w])
      rw [lastCoordinateVector, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      funext i
      exact sub_eq_zero.mp (hr i)
    _ = _ := (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm_lift
      K lastCoordinateVector _ (fun j ↦ W.nonisotropicLastPolarTangent a ha (w j))

@[simp] theorem lastOrbitFrame_inl (i : Fin (Module.finrank ℚ W.skewAdjointTangent)) :
    W.lastOrbitFrame a ha K (Sum.inl i) = W.nonisotropicLastSkewAdjointEmbed a ha K
      (skewAdjointScalarExtensionFinBasis (K := K) W.pairingMatrix i) := by
  simp only [lastOrbitFrame, Module.Basis.map_apply, Module.Basis.prod_apply]
  change W.nonisotropicLastSkewAdjointEmbed a ha K _ + W.lastOrbitLift a ha K 0 = _
  simp

@[simp] theorem lastOrbitFrame_inr (i : Fin n) :
    W.lastOrbitFrame a ha K (Sum.inr i) = W.lastOrbitLift a ha K (Pi.basisFun K (Fin n) i) := by
  simp only [lastOrbitFrame, Module.Basis.map_apply, Module.Basis.prod_apply]
  change W.nonisotropicLastSkewAdjointEmbed a ha K 0 + W.lastOrbitLift a ha K _ = _
  simp

/-- The explicit lift is the scalar extension of the same rational lift. -/
theorem lastOrbitLift_map (y : Fin n → ℚ) :
    (W.lastOrbitLift a ha ℚ y).1.map (algebraMap ℚ K) =
      (W.lastOrbitLift a ha K (fun i ↦ algebraMap ℚ K (y i))).1 := by
  change (Matrix.nonisotropicOrbitTangentLift _ lastCoordinateVector (Fin.snoc y 0)).map
    (algebraMap ℚ K) = Matrix.nonisotropicOrbitTangentLift
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix K)
      lastCoordinateVector (Fin.snoc (fun i ↦ algebraMap ℚ K (y i)) 0)
  rw [Matrix.nonisotropicOrbitTangentLift_map]
  congr 1
  · ext i
    simp [lastCoordinateVector, Pi.single_apply]
  · ext i
    cases i using Fin.lastCases <;> simp

open scoped TensorProduct

theorem lastOrbitFrame_scalarExtension
    (i : Fin (Module.finrank ℚ W.skewAdjointTangent) ⊕ Fin n) :
    W.lastOrbitFrame a ha K i =
      skewAdjointScalarExtensionEquiv (K := K) (W.nonisotropicLastExtension a ha).pairingMatrix
        (1 ⊗ₜ[ℚ] W.lastOrbitFrame a ha ℚ i) := by
  apply Subtype.ext
  rw [coe_skewAdjointScalarExtensionEquiv_tmul, one_smul]
  cases i with
  | inl i =>
      simp only [lastOrbitFrame_inl, coe_nonisotropicLastSkewAdjointEmbed_apply,
        skewAdjointScalarExtensionFinBasis, coe_skewAdjointScalarExtensionBasis_apply,
        zeroLastBlockMatrix_map]
      rfl
  | inr i =>
      simp only [lastOrbitFrame_inr]
      rw [W.lastOrbitLift_map]
      congr 2
      ext j
      simp [Pi.basisFun_apply, Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in
/-- One rational determinant supplies every local determinant. No local
basis is selected and no raw compact-volume factor is cancelled. -/
theorem lastOrbitDeterminant_scalarExtension :
    W.lastOrbitDeterminant a ha K = algebraMap ℚ K (W.lastOrbitDeterminant a ha ℚ) := by
  have hK := skewAdjointScalarExtensionDetForm_apply (K := K)
    (W.nonisotropicLastExtension a ha).pairingMatrix
    (fun j ↦ W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j))
  have hQ := skewAdjointScalarExtensionDetForm_apply (K := ℚ)
    (W.nonisotropicLastExtension a ha).pairingMatrix
    (fun j ↦ W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j))
  simp only [← W.lastOrbitFrame_scalarExtension a ha K] at hK
  simp only [← W.lastOrbitFrame_scalarExtension a ha ℚ] at hQ
  have hQvalue :
      (W.nonisotropicLastExtension a ha).pairingMatrix.skewAdjointDetForm
          (fun j ↦ W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j)) =
        W.lastOrbitDeterminant a ha ℚ := by
    simpa [lastOrbitDeterminant, lastOrbitGroupForm] using hQ.symm
  exact hK.trans (congrArg (algebraMap ℚ K) hQvalue)

theorem lastOrbitGaugeRatio_scalarExtension :
    W.lastOrbitGaugeRatio a ha K = algebraMap ℚ K (W.lastOrbitGaugeRatio a ha ℚ) := by
  simp [lastOrbitGaugeRatio, W.lastOrbitDeterminant_scalarExtension a ha K]

end RationalQuadraticSpaceMatrix
