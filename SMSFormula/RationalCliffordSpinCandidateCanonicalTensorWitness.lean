import SMSFormula.RationalCliffordSpinCandidateRankTwoInvolution

/-!
# The canonical rank-two tensor witness for the Spin candidate torsor

The represented central torsor law is converted here into its affine canonical
map. An explicit inverse is reconstructed from the pointwise torsor inverse
on the two universal candidate points. Pulling back the positive idempotent
of the rational `mu_2` coordinate ring gives a finite pure-tensor
decomposition whose evaluations at `+1` and `-1` are respectively one and
zero. These are precisely the two finite witness equations required by the
elementary rank-two faithful-flatness criterion.

No trace or coinvariant descent is asserted. After this file, that descent is
the only remaining input in the specialized rank-two route to flatness.
-/
noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

abbrev CT := TensorProduct ℚ V.cliffordSpinCandidateCoordinateRing
  RationalMuTwoCoordinateRing

noncomputable instance ctAlg : Algebra V.specialOrthogonalCoordinateRing V.CT :=
  RingHom.toAlgebra (R := V.specialOrthogonalCoordinateRing) (S := V.CT)
    (((Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
      (A := V.cliffordSpinCandidateCoordinateRing)
      (B := RationalMuTwoCoordinateRing)).comp
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom).toRingHom)

def ctLeft : V.cliffordSpinCandidateCoordinateRing →ₐ[
    V.specialOrthogonalCoordinateRing] V.CT where
  toFun := Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
    (A := V.cliffordSpinCandidateCoordinateRing)
    (B := RationalMuTwoCoordinateRing)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' a := by
    change Algebra.TensorProduct.includeLeft
      (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a) = _
    rfl

def ctRoot : rootsOfUnity 2 V.CT :=
  muTwoRootOfPoint (Algebra.TensorProduct.includeRight (R := ℚ)
    (A := V.cliffordSpinCandidateCoordinateRing)
    (B := RationalMuTwoCoordinateRing))

def ctActionQ : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT :=
  (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CT
    (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
      (A := V.cliffordSpinCandidateCoordinateRing)
      (B := RationalMuTwoCoordinateRing), V.ctRoot)).1.2

def ctAction : V.cliffordSpinCandidateCoordinateRing →ₐ[
    V.specialOrthogonalCoordinateRing] V.CT where
  toFun := V.ctActionQ
  map_one' := V.ctActionQ.map_one'
  map_mul' := V.ctActionQ.map_mul'
  map_zero' := V.ctActionQ.map_zero'
  map_add' := V.ctActionQ.map_add'
  commutes' a := by
    letI : Group (V.specialOrthogonalCoordinateRing →ₐ[ℚ] V.CT) :=
      V.specialOrthogonalCoordinateAlgHomGroup V.CT
    let x : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT :=
      Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing)
    let y := V.ctActionQ
    have h := (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CT
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing), V.ctRoot)).2
    have hcomp : x.comp
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom =
        y.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
      apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup V.CT).injective
      rw [V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
        V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp]
      exact h
    exact (DFunLike.congr_fun hcomp a).symm

def can : TensorProduct V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing
      V.cliffordSpinCandidateCoordinateRing →ₐ[
        V.specialOrthogonalCoordinateRing] V.CT :=
  by
    letI : SMul V.specialOrthogonalCoordinateRing V.CT :=
      (V.ctAlg).toSMul
    letI : IsScalarTower V.specialOrthogonalCoordinateRing
        V.specialOrthogonalCoordinateRing V.CT :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower V.specialOrthogonalCoordinateRing
        V.specialOrthogonalCoordinateRing V.cliffordSpinCandidateCoordinateRing :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact Algebra.TensorProduct.lift V.ctLeft V.ctAction
      (fun left right => show V.ctLeft left * V.ctAction right =
        V.ctAction right * V.ctLeft left from
          mul_comm (V.ctLeft left) (V.ctAction right))

abbrev CS := TensorProduct V.specialOrthogonalCoordinateRing
  V.cliffordSpinCandidateCoordinateRing
  V.cliffordSpinCandidateCoordinateRing

local instance : Algebra ℚ V.CS :=
  Algebra.TensorProduct.leftAlgebra (R := V.specialOrthogonalCoordinateRing)
    (S := ℚ) (A := V.cliffordSpinCandidateCoordinateRing)
    (B := V.cliffordSpinCandidateCoordinateRing)

def csLeftQ : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS :=
  (Algebra.TensorProduct.includeLeft
    (R := V.specialOrthogonalCoordinateRing) (S := ℚ)
    (A := V.cliffordSpinCandidateCoordinateRing)
    (B := V.cliffordSpinCandidateCoordinateRing) :
      V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS)

def csRightQ : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS where
  toFun := (Algebra.TensorProduct.includeRight :
    V.cliffordSpinCandidateCoordinateRing →ₐ[
      V.specialOrthogonalCoordinateRing] V.CS)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' q := by
    change Algebra.TensorProduct.includeRight
      (algebraMap ℚ V.cliffordSpinCandidateCoordinateRing q) =
        V.csLeftQ (algebraMap ℚ V.cliffordSpinCandidateCoordinateRing q)
    rw [← V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.commutes q]
    change 1 ⊗ₜ[V.specialOrthogonalCoordinateRing]
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
          (algebraMap ℚ V.specialOrthogonalCoordinateRing q) =
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
          (algebraMap ℚ V.specialOrthogonalCoordinateRing q) ⊗ₜ 1
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
      (algebraMap ℚ V.specialOrthogonalCoordinateRing q)).symm

def canQ : V.CS →ₐ[ℚ] V.CT where
  toFun := V.can
  map_one' := V.can.map_one'
  map_mul' := V.can.map_mul'
  map_zero' := V.can.map_zero'
  map_add' := V.can.map_add'
  commutes' q := by
    change V.can (V.csLeftQ (algebraMap ℚ
      V.cliffordSpinCandidateCoordinateRing q)) =
        algebraMap ℚ V.CT q
    simp [can, csLeftQ, ctLeft]
    exact (congrArg
      (fun value : V.CT =>
        ((algebraMap ℚ V.cliffordSpinCandidateCoordinateRing q) ⊗ₜ[ℚ] 1) * value)
      V.ctAction.map_one').trans (mul_one _)

@[simp] theorem canQ_csLeftQ (b : V.cliffordSpinCandidateCoordinateRing) :
    V.canQ (V.csLeftQ b) = V.ctLeft b := by
  simp [canQ, can, csLeftQ, ctLeft]
  exact (congrArg (fun value : V.CT => (b ⊗ₜ[ℚ] 1) * value)
    V.ctAction.map_one').trans (mul_one _)

@[simp] theorem canQ_csRightQ (b : V.cliffordSpinCandidateCoordinateRing) :
    V.canQ (V.csRightQ b) = V.ctActionQ b := by
  simp [canQ, can, csRightQ, ctAction, ctActionQ]
  exact (congrArg (fun value : V.CT => value * V.ctActionQ b)
    V.ctLeft.map_one').trans (one_mul _)

local instance canonicalTensorRationalAlgHomMonoidHomClass :
    MonoidHomClass (V.CS →ₐ[ℚ] V.CT) V.CS V.CT :=
  (AlgHom.algHomClass (R := ℚ) (A := V.CS) (B := V.CT)).toRingHomClass.toMonoidHomClass

local instance tensorEvaluationRationalAlgHomMonoidHomClass :
    MonoidHomClass (V.CT →ₐ[ℚ] V.cliffordSpinCandidateCoordinateRing)
      V.CT V.cliffordSpinCandidateCoordinateRing :=
  (AlgHom.algHomClass (R := ℚ) (A := V.CT)
    (B := V.cliffordSpinCandidateCoordinateRing)).toRingHomClass.toMonoidHomClass

def csSelfFiber : V.cliffordSpinCandidateCoordinateSelfFiber V.CS := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  letI : Group (V.specialOrthogonalCoordinateRing →ₐ[ℚ] V.CS) :=
    V.specialOrthogonalCoordinateAlgHomGroup V.CS
  refine ⟨(V.csLeftQ, V.csRightQ), ?_⟩
  change V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup V.CS
      V.csLeftQ =
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup V.CS V.csRightQ
  have hcomp : V.csLeftQ.comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom =
    V.csRightQ.comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
    ext a
    change V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a ⊗ₜ 1 =
      1 ⊗ₜ[V.specialOrthogonalCoordinateRing]
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a
  rw [← V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
    ← V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
    hcomp]

def csTorsorInverse :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) × rootsOfUnity 2 V.CS := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  exact (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS).symm V.csSelfFiber

def canInv : V.CT →ₐ[ℚ] V.CS :=
  Algebra.TensorProduct.productMap V.csTorsorInverse.1
    (muTwoPointOfRoot V.csTorsorInverse.2)

theorem csTorsorInverse_fst : V.csTorsorInverse.1 = V.csLeftQ := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  have h := congrArg (fun p => p.1.1)
    ((V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS).apply_symm_apply
      V.csSelfFiber)
  exact h

theorem csTorsorInverse_snd :
    (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS
      V.csTorsorInverse).1.2 = V.csRightQ := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  exact congrArg (fun point => point.1.2)
    ((V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS).apply_symm_apply
      V.csSelfFiber)

@[simp] theorem canInv_ctLeft (b : V.cliffordSpinCandidateCoordinateRing) :
    V.canInv (V.ctLeft b) = V.csLeftQ b := by
  change Algebra.TensorProduct.productMap V.csTorsorInverse.1
      (muTwoPointOfRoot V.csTorsorInverse.2) (b ⊗ₜ[ℚ] 1) = V.csLeftQ b
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  calc
    _ = V.csTorsorInverse.1 b :=
      (congrArg (fun value : V.CS => V.csTorsorInverse.1 b * value)
        (muTwoPointOfRoot V.csTorsorInverse.2).map_one').trans (mul_one _)
    _ = V.csLeftQ b := DFunLike.congr_fun V.csTorsorInverse_fst b

@[simp] theorem canInv_muTwoRight (h : RationalMuTwoCoordinateRing) :
    V.canInv ((Algebra.TensorProduct.includeRight (R := ℚ)
      (A := V.cliffordSpinCandidateCoordinateRing)
      (B := RationalMuTwoCoordinateRing)) h) =
      muTwoPointOfRoot V.csTorsorInverse.2 h := by
  simp only [canInv, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_right_apply]

theorem canQ_csTorsorInverse_pair :
    (V.canQ.comp V.csTorsorInverse.1,
      restrictRootsOfUnity V.canQ 2 V.csTorsorInverse.2) =
    ((Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
      (A := V.cliffordSpinCandidateCoordinateRing)
      (B := RationalMuTwoCoordinateRing) :
        V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT), V.ctRoot) := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CT
  apply (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CT).injective
  change V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CT
      (V.cliffordSpinCandidateCoordinateAlgHomMap V.CS (B := V.CT) V.canQ
          V.csTorsorInverse.1,
        restrictRootsOfUnity V.canQ 2 V.csTorsorInverse.2) = _
  rw [← V.cliffordSpinCandidateCoordinateTorsorMulEquiv_naturality]
  rw [show V.csTorsorInverse =
      (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS).symm
        V.csSelfFiber by rfl]
  rw [(V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS).apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · ext b
    exact V.canQ_csLeftQ b
  · ext b
    exact V.canQ_csRightQ b

theorem canQ_csTorsorInverse_root :
    restrictRootsOfUnity V.canQ 2 V.csTorsorInverse.2 = V.ctRoot :=
  congrArg Prod.snd V.canQ_csTorsorInverse_pair

theorem canQ_comp_canInv : V.canQ.comp V.canInv = AlgHom.id ℚ V.CT := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro b
    change V.canQ (V.canInv (V.ctLeft b)) = V.ctLeft b
    rw [V.canInv_ctLeft, V.canQ_csLeftQ]
  · change (V.canQ.comp V.canInv).comp
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := V.cliffordSpinCandidateCoordinateRing)
          (B := RationalMuTwoCoordinateRing)) =
      (AlgHom.id ℚ V.CT).comp
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := V.cliffordSpinCandidateCoordinateRing)
          (B := RationalMuTwoCoordinateRing))
    apply AddMonoidAlgebra.algHom_ext'
    apply MonoidHom.ext
    intro g
    simp only [MonoidHom.comp_apply, AddMonoidAlgebra.of_apply]
    cases g with
    | ofAdd g =>
      change V.canQ (V.canInv
          ((Algebra.TensorProduct.includeRight (R := ℚ)
            (A := V.cliffordSpinCandidateCoordinateRing)
            (B := RationalMuTwoCoordinateRing))
              (AddMonoidAlgebra.single g 1))) =
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := V.cliffordSpinCandidateCoordinateRing)
          (B := RationalMuTwoCoordinateRing))
            (AddMonoidAlgebra.single g 1)
      have hg : g = 0 ∨ g = 1 := by
        fin_cases g <;> simp
      rcases hg with rfl | rfl
      · simp [canInv, muTwoPointOfRoot, muTwoCyclicHom]
        rw [← AddMonoidAlgebra.one_def, ← Algebra.TensorProduct.one_def]
        exact (congrArg (fun element : V.CS => V.canQ element)
          V.csTorsorInverse.1.map_one').trans V.canQ.map_one'
      · rw [V.canInv_muTwoRight]
        rw [muTwoPointOfRoot_generator]
        change (((restrictRootsOfUnity V.canQ 2 V.csTorsorInverse.2 :
          rootsOfUnity 2 V.CT) : V.CTˣ) : V.CT) = _
        rw [V.canQ_csTorsorInverse_root]
        rfl

def ctEval (z : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing) :
    V.CT →ₐ[ℚ] V.cliffordSpinCandidateCoordinateRing :=
  Algebra.TensorProduct.productMap
    (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
    (muTwoPointOfRoot z)

@[simp] theorem ctEval_ctLeft
    (z : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
    (b : V.cliffordSpinCandidateCoordinateRing) :
    V.ctEval z (V.ctLeft b) = b := by
  simp [ctEval, ctLeft]

theorem restrict_ctRoot_ctEval
    (z : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing) :
    restrictRootsOfUnity (V.ctEval z) 2 V.ctRoot = z := by
  apply rootsOfUnity.coe_injective
  change Algebra.TensorProduct.productMap
      (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) (muTwoPointOfRoot z)
      (1 ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1) = ((z :
        V.cliffordSpinCandidateCoordinateRingˣ) : V.cliffordSpinCandidateCoordinateRing)
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  exact (one_mul _).trans (muTwoPointOfRoot_generator z)

theorem ctEval_comp_ctActionQ
    (z : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing) :
    (V.ctEval z).comp V.ctActionQ =
      (V.cliffordSpinCandidateCoordinateTorsorMulEquiv
        V.cliffordSpinCandidateCoordinateRing
        (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing, z)).1.2 := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CT
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing
  have h := congrArg (fun p => p.1.2)
    (V.cliffordSpinCandidateCoordinateTorsorMulEquiv_naturality
      (V.ctEval z)
      ((Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing) :
          V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT), V.ctRoot))
  change (V.ctEval z).comp V.ctActionQ =
    (V.cliffordSpinCandidateCoordinateTorsorMulEquiv
      V.cliffordSpinCandidateCoordinateRing
      ((V.ctEval z).comp
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
          (A := V.cliffordSpinCandidateCoordinateRing)
          (B := RationalMuTwoCoordinateRing)),
        restrictRootsOfUnity (V.ctEval z) 2 V.ctRoot)).1.2 at h
  rw [V.restrict_ctRoot_ctEval z] at h
  rw [show (V.ctEval z).comp
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing)) =
      AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing by
        ext b
        simp [ctEval]] at h
  exact h

theorem ctEval_one_comp_ctActionQ :
    (V.ctEval (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
      ).comp V.ctActionQ =
      AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing
  rw [V.ctEval_comp_ctActionQ]
  simp [cliffordSpinCandidateCoordinateTorsorMulEquiv,
    MonoidHom.centralKernelTorsorMulEquiv]
  exact @mul_one
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.cliffordSpinCandidateCoordinateRing)
    (V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing).toMulOneClass
    (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)

theorem ctEval_negOne_comp_ctActionQ :
    (V.ctEval (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
      ).comp V.ctActionQ = V.cliffordSpinCandidateNegOneCoordinateEnd := by
  rw [V.ctEval_comp_ctActionQ]
  rfl

theorem canQ_tmul
    (x y : V.cliffordSpinCandidateCoordinateRing) :
    V.canQ (x ⊗ₜ[V.specialOrthogonalCoordinateRing] y) =
      V.ctLeft x * V.ctActionQ y := by
  simp [canQ, can, ctLeft, ctAction, ctActionQ]

theorem ctEval_one_canQ_tmul
    (x y : V.cliffordSpinCandidateCoordinateRing) :
    V.ctEval (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
        (V.canQ (x ⊗ₜ[V.specialOrthogonalCoordinateRing] y)) = x * y := by
  rw [V.canQ_tmul, map_mul, V.ctEval_ctLeft]
  change x * (((V.ctEval
      (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)).comp
        V.ctActionQ) y) = x * y
  rw [V.ctEval_one_comp_ctActionQ]
  rfl

theorem ctEval_negOne_canQ_tmul
    (x y : V.cliffordSpinCandidateCoordinateRing) :
    V.ctEval (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
        (V.canQ (x ⊗ₜ[V.specialOrthogonalCoordinateRing] y)) =
      x * V.cliffordSpinCandidateNegOneCoordinateAlgEquiv y := by
  rw [V.canQ_tmul, map_mul, V.ctEval_ctLeft]
  change x * (((V.ctEval
      (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)).comp
        V.ctActionQ) y) = _
  rw [V.ctEval_negOne_comp_ctActionQ]
  rfl

def muTwoPositiveSelector : RationalMuTwoCoordinateRing :=
  (2 : ℚ)⁻¹ •
    (AddMonoidAlgebra.single (0 : ZMod 2) 1 +
      AddMonoidAlgebra.single (1 : ZMod 2) 1)

def canonicalPositiveSelector : V.CT :=
  (Algebra.TensorProduct.includeRight (R := ℚ)
    (A := V.cliffordSpinCandidateCoordinateRing)
    (B := RationalMuTwoCoordinateRing)) muTwoPositiveSelector

theorem ctEval_one_canonicalPositiveSelector :
    V.ctEval (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
      V.canonicalPositiveSelector = 1 := by
  rw [show V.ctEval
      (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
        V.canonicalPositiveSelector =
      muTwoPointOfRoot
        (1 : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing)
          muTwoPositiveSelector by simp [ctEval, canonicalPositiveSelector]]
  rw [muTwoPositiveSelector, map_smul, map_add,
    ← AddMonoidAlgebra.one_def, map_one, muTwoPointOfRoot_generator]
  change (2 : ℚ)⁻¹ •
    ((1 : V.cliffordSpinCandidateCoordinateRing) + 1) = 1
  simpa only [two_smul] using
    (inv_smul_smul₀ (show (2 : ℚ) ≠ 0 by decide)
      (1 : V.cliffordSpinCandidateCoordinateRing))

theorem ctEval_negOne_canonicalPositiveSelector :
    V.ctEval (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
      V.canonicalPositiveSelector = 0 := by
  rw [show V.ctEval
      (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
        V.canonicalPositiveSelector =
      muTwoPointOfRoot
        (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
          muTwoPositiveSelector by simp [ctEval, canonicalPositiveSelector]]
  rw [muTwoPositiveSelector, map_smul, map_add,
    ← AddMonoidAlgebra.one_def, map_one, muTwoPointOfRoot_generator]
  change (2 : ℚ)⁻¹ •
    ((1 : V.cliffordSpinCandidateCoordinateRing) + (-1)) = 0
  norm_num

def canonicalWitnessTensor : V.CS :=
  V.canInv V.canonicalPositiveSelector

theorem canQ_canonicalWitnessTensor :
    V.canQ V.canonicalWitnessTensor = V.canonicalPositiveSelector := by
  exact DFunLike.congr_fun V.canQ_comp_canInv V.canonicalPositiveSelector

structure CanonicalWitnessDecomposition where
  size : ℕ
  left : Fin size → V.cliffordSpinCandidateCoordinateRing
  right : Fin size → V.cliffordSpinCandidateCoordinateRing
  eq_sum : V.canonicalWitnessTensor =
    ∑ i, left i ⊗ₜ[V.specialOrthogonalCoordinateRing] right i

noncomputable def canonicalWitnessDecomposition :
    V.CanonicalWitnessDecomposition := by
  let h := TensorProduct.exists_sum_tmul_eq V.canonicalWitnessTensor
  let k := h.choose
  let left := h.choose_spec.choose
  let right := h.choose_spec.choose_spec.choose
  exact ⟨k, left, right, h.choose_spec.choose_spec.choose_spec⟩

structure CanonicalRankTwoWitness where
  size : ℕ
  left : Fin size → V.cliffordSpinCandidateCoordinateRing
  right : Fin size → V.cliffordSpinCandidateCoordinateRing
  canonical_one : ∑ i, left i * right i = 1
  canonical_zero : ∑ i,
    left i * V.cliffordSpinCandidateNegOneCoordinateAlgEquiv (right i) = 0

noncomputable def canonicalRankTwoWitness : V.CanonicalRankTwoWitness := by
  let D := V.canonicalWitnessDecomposition
  refine ⟨D.size, D.left, D.right, ?_, ?_⟩
  · calc
      ∑ i, D.left i * D.right i =
          V.ctEval (1 : rootsOfUnity 2
            V.cliffordSpinCandidateCoordinateRing)
            (V.canQ (∑ i, D.left i ⊗ₜ[
              V.specialOrthogonalCoordinateRing] D.right i)) := by
                simp only [map_sum, V.ctEval_one_canQ_tmul]
      _ = V.ctEval (1 : rootsOfUnity 2
            V.cliffordSpinCandidateCoordinateRing)
            (V.canQ V.canonicalWitnessTensor) := by rw [D.eq_sum]
      _ = V.ctEval (1 : rootsOfUnity 2
            V.cliffordSpinCandidateCoordinateRing)
            V.canonicalPositiveSelector := by rw [V.canQ_canonicalWitnessTensor]
      _ = 1 := V.ctEval_one_canonicalPositiveSelector
  · calc
      ∑ i, D.left i *
          V.cliffordSpinCandidateNegOneCoordinateAlgEquiv (D.right i) =
        V.ctEval (negOneRootOfUnity
          V.cliffordSpinCandidateCoordinateRing)
          (V.canQ (∑ i, D.left i ⊗ₜ[
            V.specialOrthogonalCoordinateRing] D.right i)) := by
              simp only [map_sum, V.ctEval_negOne_canQ_tmul]
      _ = V.ctEval (negOneRootOfUnity
            V.cliffordSpinCandidateCoordinateRing)
            (V.canQ V.canonicalWitnessTensor) := by rw [D.eq_sum]
      _ = V.ctEval (negOneRootOfUnity
            V.cliffordSpinCandidateCoordinateRing)
            V.canonicalPositiveSelector := by rw [V.canQ_canonicalWitnessTensor]
      _ = 0 := V.ctEval_negOne_canonicalPositiveSelector

/-- The only datum still missing after the canonical tensor witness: descent
of the involution trace to the special-orthogonal coordinate ring. -/
structure CliffordSpinCandidateRankTwoTraceDescentData where
  trace : V.cliffordSpinCandidateCoordinateRing →ₗ[
    V.specialOrthogonalCoordinateRing] V.specialOrthogonalCoordinateRing
  trace_spec : ∀ b, algebraMap V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing (trace b) =
      b + V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b

/-- Trace descent and the canonical witness assemble the effective-quotient
data required by the rank-two flatness endpoint. -/
noncomputable def CliffordSpinCandidateRankTwoTraceDescentData.toEffectiveQuotientData
    (D : V.CliffordSpinCandidateRankTwoTraceDescentData) :
    V.CliffordSpinCandidateRankTwoEffectiveQuotientData := by
  let W := V.canonicalRankTwoWitness
  exact
    { size := W.size
      trace := D.trace
      trace_spec := D.trace_spec
      left := W.left
      right := W.right
      canonical_one := W.canonical_one
      canonical_zero := W.canonical_zero }

/-- Once the involution trace descends, the Spin-candidate coordinate map is
faithfully flat; the finite canonical witness is supplied by this file. -/
theorem faithfullyFlat_of_rankTwoTraceDescentData
    (D : V.CliffordSpinCandidateRankTwoTraceDescentData) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat :=
  V.faithfullyFlat_of_rankTwoEffectiveQuotientData
    D.toEffectiveQuotientData

end RationalQuadraticSpaceMatrix
