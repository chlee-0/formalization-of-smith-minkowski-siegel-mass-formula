import SMSFormula.PadicCayleyLeftTrivializedDetFactor

/-!
# Alternating-matrix model of the p-adic Cayley denominator action

For a symmetric nonsingular rational form, left multiplication by its p-adic
scalar extension identifies transported skew-adjoint matrices with
skew-symmetric matrices. Under this continuous linear equivalence, the
unscaled left-trivialized Cayley denominator action becomes matrix congruence
by the inverse source denominator.

This file does not compute a determinant or determinant norm, pull back a
determinant form, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {R ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The submodule of matrices satisfying the skew-symmetry equation
`Yᵀ = -Y`. Over the p-adic fields used below, these are the matrices of
alternating bilinear forms. -/
def skewSymmetricMatricesSubmodule [CommRing R] :
    Submodule R (Matrix ι ι R) where
  carrier := {Y | Yᵀ = -Y}
  zero_mem' := by simp
  add_mem' := by
    intro Y Z hY hZ
    change Yᵀ = -Y at hY
    change Zᵀ = -Z at hZ
    change (Y + Z)ᵀ = -(Y + Z)
    rw [Matrix.transpose_add, hY, hZ]
    abel
  smul_mem' := by
    intro c Y hY
    change Yᵀ = -Y at hY
    change (c • Y)ᵀ = -(c • Y)
    rw [Matrix.transpose_smul, hY]
    simp

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_skewSymmetricMatricesSubmodule [CommRing R]
    (Y : Matrix ι ι R) :
    Y ∈ skewSymmetricMatricesSubmodule (R := R) (ι := ι) ↔
      Yᵀ = -Y :=
  Iff.rfl

variable (p : ℕ) [Fact (Nat.Prime p)]

omit [DecidableEq ι] in
/-- Congruence by `C` preserves skew-symmetric matrices. -/
theorem skewSymmetricMatricesSubmodule_congruence_mem
    (C : Matrix ι ι ℚ_[p])
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) :
    Cᵀ * (Y : Matrix ι ι ℚ_[p]) * C ∈
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) := by
  change (Cᵀ * (Y : Matrix ι ι ℚ_[p]) * C)ᵀ =
    -(Cᵀ * (Y : Matrix ι ι ℚ_[p]) * C)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Y.property]
  noncomm_ring

/-- The continuous linear congruence action `Y ↦ Cᵀ Y C` on skew-symmetric
matrices. -/
def skewSymmetricPadicCongruenceEndomorphism
    (C : Matrix ι ι ℚ_[p]) :
    skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) →L[ℚ_[p]]
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) :=
  ((ContinuousLinearMap.mulLeftRight ℚ_[p] (Matrix ι ι ℚ_[p]) Cᵀ C).comp
      (skewSymmetricMatricesSubmodule
        (R := ℚ_[p]) (ι := ι)).subtypeL).codRestrict _
    (fun Y => skewSymmetricMatricesSubmodule_congruence_mem p C Y)

@[simp]
theorem coe_skewSymmetricPadicCongruenceEndomorphism_apply
    (C : Matrix ι ι ℚ_[p])
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) :
    (skewSymmetricPadicCongruenceEndomorphism p C Y :
        Matrix ι ι ℚ_[p]) =
      Cᵀ * (Y : Matrix ι ι ℚ_[p]) * C :=
  rfl

variable (F : Matrix ι ι ℚ)

omit [Fintype ι] [DecidableEq ι] in
/-- Symmetry survives scalar extension from the rational form to `Q_p`. -/
theorem skewAdjointPadicForm_isSymm (hF : F.IsSymm) :
    (F.map (algebraMap ℚ ℚ_[p])).IsSymm :=
  hF.map _

/-- Nonsingularity survives scalar extension from the rational form to
`Q_p`. -/
theorem skewAdjointPadicForm_det_ne_zero (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
  have hmap : algebraMap ℚ ℚ_[p] F.det ≠ 0 := by
    intro hz
    apply hdet
    apply (algebraMap ℚ ℚ_[p]).injective
    simpa using hz
  have heq :
      (F.map (algebraMap ℚ ℚ_[p])).det =
        algebraMap ℚ ℚ_[p] F.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((algebraMap ℚ ℚ_[p]).map_det F).symm
  rwa [heq]

/-- Left multiplication by the scalar-extended form sends transported
skew-adjoint matrices to skew-symmetric matrices. -/
def skewAdjointPadicToSkewSymmetricLinearMap
    (hF : F.IsSymm) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →ₗ[ℚ_[p]]
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) where
  toFun H := ⟨F.map (algebraMap ℚ ℚ_[p]) * (H : Matrix ι ι ℚ_[p]), by
    let Fp := F.map (algebraMap ℚ ℚ_[p])
    let Hm : Matrix ι ι ℚ_[p] := H
    have hHker : skewAdjointOperator Fp Hm = 0 := by
      exact LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff Fp Hm).mpr H.property)
    have hHskew : Hmᵀ * Fp = -(Fp * Hm) :=
      eq_neg_of_add_eq_zero_left hHker
    have hFpSymm : Fp.IsSymm :=
      skewAdjointPadicForm_isSymm p F hF
    change (Fp * Hm)ᵀ = -(Fp * Hm)
    rw [Matrix.transpose_mul, hFpSymm.eq, hHskew]⟩
  map_add' H K := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' c H := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewAdjointPadicToSkewSymmetricLinearMap_apply
    (hF : F.IsSymm)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointPadicToSkewSymmetricLinearMap p F hF H :
        Matrix ι ι ℚ_[p]) =
      F.map (algebraMap ℚ ℚ_[p]) * (H : Matrix ι ι ℚ_[p]) :=
  rfl

/-- Left multiplication by the nonsingular inverse form sends
skew-symmetric matrices back to transported skew-adjoint matrices. -/
def skewSymmetricPadicToSkewAdjointLinearMap
    (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) →ₗ[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule where
  toFun Y := ⟨(F.map (algebraMap ℚ ℚ_[p]))⁻¹ *
      (Y : Matrix ι ι ℚ_[p]), by
    let Fp := F.map (algebraMap ℚ ℚ_[p])
    let Ym : Matrix ι ι ℚ_[p] := Y
    have hFpdet : IsUnit Fp.det :=
      isUnit_iff_ne_zero.mpr (skewAdjointPadicForm_det_ne_zero p F hdet)
    have hFpSymm : Fp.IsSymm := skewAdjointPadicForm_isSymm p F hF
    apply (mem_ker_skewAdjointOperator_iff Fp (Fp⁻¹ * Ym)).mp
    rw [LinearMap.mem_ker, skewAdjointOperator_apply, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv, hFpSymm.eq, Y.property]
    calc
      (-Ym) * Fp⁻¹ * Fp + Fp * (Fp⁻¹ * Ym) =
          -(Ym * (Fp⁻¹ * Fp)) + (Fp * Fp⁻¹) * Ym := by
            noncomm_ring
      _ = 0 := by
        rw [Matrix.nonsing_inv_mul Fp hFpdet,
          Matrix.mul_nonsing_inv Fp hFpdet]
        simp⟩
  map_add' Y Z := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' c Y := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewSymmetricPadicToSkewAdjointLinearMap_apply
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) :
    (skewSymmetricPadicToSkewAdjointLinearMap p F hF hdet Y :
        Matrix ι ι ℚ_[p]) =
      (F.map (algebraMap ℚ ℚ_[p]))⁻¹ * (Y : Matrix ι ι ℚ_[p]) :=
  rfl

/-- For a symmetric nonsingular form, `H ↦ F_p H` continuously identifies
the transported skew-adjoint model with skew-symmetric matrices. -/
noncomputable def skewAdjointPadicSkewSymmetricContinuousLinearEquiv
    (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) := by
  let hFpdet : IsUnit (F.map (algebraMap ℚ ℚ_[p])).det :=
    isUnit_iff_ne_zero.mpr (skewAdjointPadicForm_det_ne_zero p F hdet)
  let e : (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃ₗ[ℚ_[p]]
        skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) := by
    refine LinearEquiv.ofLinear
      (skewAdjointPadicToSkewSymmetricLinearMap p F hF)
      (skewSymmetricPadicToSkewAdjointLinearMap p F hF hdet) ?_ ?_
    · apply LinearMap.ext
      intro Y
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.id_apply,
        coe_skewAdjointPadicToSkewSymmetricLinearMap_apply,
        coe_skewSymmetricPadicToSkewAdjointLinearMap_apply]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFpdet,
        one_mul]
    · apply LinearMap.ext
      intro H
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.id_apply,
        coe_skewAdjointPadicToSkewSymmetricLinearMap_apply,
        coe_skewSymmetricPadicToSkewAdjointLinearMap_apply]
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFpdet,
        one_mul]
  exact e.toContinuousLinearEquiv

@[simp]
theorem coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_apply
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
        p F hF hdet H : Matrix ι ι ℚ_[p]) =
      F.map (algebraMap ℚ ℚ_[p]) * (H : Matrix ι ι ℚ_[p]) :=
  rfl

@[simp]
theorem coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_toContinuousLinearMap_apply
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    ((skewAdjointPadicSkewSymmetricContinuousLinearEquiv
        p F hF hdet).toContinuousLinearMap H : Matrix ι ι ℚ_[p]) =
      F.map (algebraMap ℚ ℚ_[p]) * (H : Matrix ι ι ℚ_[p]) :=
  rfl

/-- Under the skew-adjoint-to-skew-symmetric equivalence, the unscaled
Cayley denominator action is congruence by `(1-X)⁻¹`. -/
theorem skewAdjointPadicCayleyDenominatorEndomorphism_conjugation
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
        p F hF hdet).toContinuousLinearMap.comp
      (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
        F p X hX) =
      (skewSymmetricPadicCongruenceEndomorphism p
          (1 - (X : Matrix ι ι ℚ_[p]))⁻¹).comp
        (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
          p F hF hdet).toContinuousLinearMap := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  let A : Matrix ι ι ℚ_[p] := 1 - Xm
  let B : Matrix ι ι ℚ_[p] := 1 + Xm
  have hAunit : IsUnit A := hX
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hAtdet : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact hAdet
  have hBunit : IsUnit B :=
    isUnit_one_add_of_mem_skewAdjointPadicCayleySource F p hdet X hX
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hXker : skewAdjointOperator Fp Xm = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff Fp Xm).mpr X.property)
  have hXskew : Xmᵀ * Fp = -(Fp * Xm) :=
    eq_neg_of_add_eq_zero_left hXker
  have hminus : Aᵀ * Fp = Fp * B := by
    dsimp [A, B]
    rw [Matrix.transpose_sub]
    simp only [Matrix.transpose_one]
    calc
      (1 - Xmᵀ) * Fp = Fp - Xmᵀ * Fp := by noncomm_ring
      _ = Fp + Fp * Xm := by rw [hXskew]; noncomm_ring
      _ = Fp * (1 + Xm) := by noncomm_ring
  have htransport : (Aᵀ)⁻¹ * Fp = Fp * B⁻¹ := by
    calc
      (Aᵀ)⁻¹ * Fp = (Aᵀ)⁻¹ * Fp * 1 := by rw [Matrix.mul_one]
      _ = (Aᵀ)⁻¹ * Fp * (B * B⁻¹) := by
        rw [Matrix.mul_nonsing_inv B hBdet]
      _ = (Aᵀ)⁻¹ * (Fp * B) * B⁻¹ := by noncomm_ring
      _ = (Aᵀ)⁻¹ * (Aᵀ * Fp) * B⁻¹ := by rw [hminus]
      _ = Fp * B⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left Aᵀ Fp hAtdet]
  apply ContinuousLinearMap.ext
  intro H
  apply Subtype.ext
  simp only [ContinuousLinearMap.comp_apply]
  rw [
    coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_toContinuousLinearMap_apply,
    coe_skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism_apply,
    coe_skewSymmetricPadicCongruenceEndomorphism_apply,
    coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_toContinuousLinearMap_apply]
  change
    Fp * (B⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹) =
      (A⁻¹)ᵀ * (Fp * (H : Matrix ι ι ℚ_[p])) * A⁻¹
  rw [Matrix.transpose_nonsing_inv]
  calc
    Fp * (B⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹) =
        (Fp * B⁻¹) * (H : Matrix ι ι ℚ_[p]) * A⁻¹ := by
          noncomm_ring
    _ = ((Aᵀ)⁻¹ * Fp) * (H : Matrix ι ι ℚ_[p]) * A⁻¹ := by
      rw [htransport]
    _ = (Aᵀ)⁻¹ * (Fp * (H : Matrix ι ι ℚ_[p])) * A⁻¹ := by
      noncomm_ring

end Matrix
